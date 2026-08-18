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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___closed__1;
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___closed__2;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3;
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
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashSet_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__9_value)} };
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
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_cellCount_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_2_ = lean_unsigned_to_nat(4u);
v___x_3_ = lean_nat_mul(v_capacity_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_add(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_unsigned_to_nat(3u);
v___x_7_ = lean_nat_div(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v_cellCount_8_ = l_Nat_nextPowerOfTwo(v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_8_);
v___x_10_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_8_);
v___x_11_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_8_);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_9_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_ExtHashSet_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_capacity_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_cellCount_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_19_ = lean_unsigned_to_nat(4u);
v___x_20_ = lean_nat_mul(v_capacity_18_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_nat_add(v___x_20_, v___x_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_unsigned_to_nat(3u);
v___x_24_ = lean_nat_div(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
v_cellCount_25_ = l_Nat_nextPowerOfTwo(v___x_24_);
lean_dec(v___x_24_);
v___x_26_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_25_);
v___x_27_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_25_);
v___x_28_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_25_);
v___x_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_29_, 0, v___x_26_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___boxed(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_capacity_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_ExtHashSet_emptyWithCapacity(v_00_u03b1_30_, v_inst_31_, v_inst_32_, v_capacity_33_);
lean_dec(v_capacity_33_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_34_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_35_; lean_object* v___x_36_; 
v_cellCount_35_ = lean_unsigned_to_nat(16u);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_37_; lean_object* v___x_38_; 
v_cellCount_37_ = lean_unsigned_to_nat(16u);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
v___x_40_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__0, &l_Std_ExtHashSet_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__0);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
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
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___boxed(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_ExtHashSet_instInhabited(v_00_u03b1_55_, v_inst_56_, v_inst_57_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert___redArg(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_m_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___y_65_; lean_object* v_i_66_; lean_object* v___y_72_; lean_object* v___y_82_; lean_object* v_i_83_; lean_object* v___x_98_; 
v___x_63_ = lean_box(0);
lean_inc(v_a_62_);
lean_inc_ref(v_x_60_);
lean_inc_ref(v_x_59_);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_59_, v_x_60_, v_m_61_, v_a_62_);
switch(lean_obj_tag(v___x_98_))
{
case 0:
{
lean_dec_ref_known(v___x_98_, 3);
lean_dec(v_a_62_);
lean_dec_ref(v_x_60_);
lean_dec_ref(v_x_59_);
return v_m_61_;
}
case 1:
{
lean_object* v_index_99_; lean_object* v_size_100_; lean_object* v_keyArray_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_index_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_index_99_);
lean_dec_ref_known(v___x_98_, 1);
v_size_100_ = lean_ctor_get(v_m_61_, 0);
v_keyArray_101_ = lean_ctor_get(v_m_61_, 1);
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_size_100_, v___x_102_);
v___x_104_ = lean_array_get_size(v_keyArray_101_);
v___x_105_ = lean_nat_dec_lt(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec(v___x_103_);
lean_dec(v_index_99_);
goto v___jp_88_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_106_ = lean_unsigned_to_nat(4u);
v___x_107_ = lean_nat_mul(v___x_103_, v___x_106_);
v___x_108_ = lean_unsigned_to_nat(3u);
v___x_109_ = lean_nat_mul(v___x_104_, v___x_108_);
v___x_110_ = lean_nat_dec_le(v___x_107_, v___x_109_);
lean_dec(v___x_109_);
lean_dec(v___x_107_);
if (v___x_110_ == 0)
{
lean_dec(v___x_103_);
lean_dec(v_index_99_);
goto v___jp_88_;
}
else
{
lean_object* v___x_111_; 
lean_dec_ref(v_x_60_);
lean_dec_ref(v_x_59_);
v___x_111_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_61_, v___x_103_, v_index_99_, v_a_62_, v___x_63_);
lean_dec(v_index_99_);
return v___x_111_;
}
}
}
default: 
{
lean_object* v_size_112_; lean_object* v_keyArray_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_size_112_ = lean_ctor_get(v_m_61_, 0);
v_keyArray_113_ = lean_ctor_get(v_m_61_, 1);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_size_112_, v___x_114_);
v___x_116_ = lean_array_get_size(v_keyArray_113_);
v___x_117_ = lean_nat_dec_lt(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec(v___x_115_);
lean_inc_ref(v_x_60_);
lean_inc_ref(v_x_59_);
v___x_118_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_59_, v_x_60_, v_m_61_);
v___y_72_ = v___x_118_;
goto v___jp_71_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_119_ = lean_unsigned_to_nat(4u);
v___x_120_ = lean_nat_mul(v___x_115_, v___x_119_);
lean_dec(v___x_115_);
v___x_121_ = lean_unsigned_to_nat(3u);
v___x_122_ = lean_nat_mul(v___x_116_, v___x_121_);
v___x_123_ = lean_nat_dec_le(v___x_120_, v___x_122_);
lean_dec(v___x_122_);
lean_dec(v___x_120_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_inc_ref(v_x_60_);
lean_inc_ref(v_x_59_);
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_59_, v_x_60_, v_m_61_);
v___y_72_ = v___x_124_;
goto v___jp_71_;
}
else
{
v___y_72_ = v_m_61_;
goto v___jp_71_;
}
}
}
}
v___jp_64_:
{
lean_object* v_size_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_size_67_ = lean_ctor_get(v___y_65_, 0);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_size_67_, v___x_68_);
v___x_70_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_65_, v___x_69_, v_i_66_, v_a_62_, v___x_63_);
lean_dec(v_i_66_);
return v___x_70_;
}
v___jp_71_:
{
lean_object* v___x_73_; 
lean_inc(v_a_62_);
v___x_73_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_59_, v_x_60_, v___y_72_, v_a_62_);
switch(lean_obj_tag(v___x_73_))
{
case 0:
{
lean_object* v_index_74_; lean_object* v_size_75_; lean_object* v___x_76_; 
v_index_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_index_74_);
lean_dec_ref_known(v___x_73_, 3);
v_size_75_ = lean_ctor_get(v___y_72_, 0);
lean_inc(v_size_75_);
v___x_76_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_72_, v_size_75_, v_index_74_, v_a_62_, v___x_63_);
lean_dec(v_index_74_);
return v___x_76_;
}
case 1:
{
lean_object* v_index_77_; 
v_index_77_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_index_77_);
lean_dec_ref_known(v___x_73_, 1);
v___y_65_ = v___y_72_;
v_i_66_ = v_index_77_;
goto v___jp_64_;
}
default: 
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_72_, v___x_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_index_80_; 
v_index_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_index_80_);
lean_dec_ref_known(v___x_79_, 1);
v___y_65_ = v___y_72_;
v_i_66_ = v_index_80_;
goto v___jp_64_;
}
else
{
lean_dec(v_a_62_);
return v___y_72_;
}
}
}
}
v___jp_81_:
{
lean_object* v_size_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_size_84_ = lean_ctor_get(v___y_82_, 0);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_size_84_, v___x_85_);
v___x_87_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_82_, v___x_86_, v_i_83_, v_a_62_, v___x_63_);
lean_dec(v_i_83_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_inc_ref(v_x_60_);
lean_inc_ref(v_x_59_);
v___x_89_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_59_, v_x_60_, v_m_61_);
lean_inc(v_a_62_);
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_59_, v_x_60_, v___x_89_, v_a_62_);
switch(lean_obj_tag(v___x_90_))
{
case 0:
{
lean_object* v_index_91_; lean_object* v_size_92_; lean_object* v___x_93_; 
v_index_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_index_91_);
lean_dec_ref_known(v___x_90_, 3);
v_size_92_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_size_92_);
v___x_93_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_89_, v_size_92_, v_index_91_, v_a_62_, v___x_63_);
lean_dec(v_index_91_);
return v___x_93_;
}
case 1:
{
lean_object* v_index_94_; 
v_index_94_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_index_94_);
lean_dec_ref_known(v___x_90_, 1);
v___y_82_ = v___x_89_;
v_i_83_ = v_index_94_;
goto v___jp_81_;
}
default: 
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_89_, v___x_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_index_97_; 
v_index_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_index_97_);
lean_dec_ref_known(v___x_96_, 1);
v___y_82_ = v___x_89_;
v_i_83_ = v_index_97_;
goto v___jp_81_;
}
else
{
lean_dec(v_a_62_);
return v___x_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert(lean_object* v_00_u03b1_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_m_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___y_134_; lean_object* v_i_135_; lean_object* v___y_141_; lean_object* v___y_151_; lean_object* v_i_152_; lean_object* v___x_167_; 
v___x_132_ = lean_box(0);
lean_inc(v_a_131_);
lean_inc_ref(v_x_127_);
lean_inc_ref(v_x_126_);
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_126_, v_x_127_, v_m_130_, v_a_131_);
switch(lean_obj_tag(v___x_167_))
{
case 0:
{
lean_dec_ref_known(v___x_167_, 3);
lean_dec(v_a_131_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
return v_m_130_;
}
case 1:
{
lean_object* v_index_168_; lean_object* v_size_169_; lean_object* v_keyArray_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_index_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_index_168_);
lean_dec_ref_known(v___x_167_, 1);
v_size_169_ = lean_ctor_get(v_m_130_, 0);
v_keyArray_170_ = lean_ctor_get(v_m_130_, 1);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_size_169_, v___x_171_);
v___x_173_ = lean_array_get_size(v_keyArray_170_);
v___x_174_ = lean_nat_dec_lt(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v___x_172_);
lean_dec(v_index_168_);
goto v___jp_157_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_175_ = lean_unsigned_to_nat(4u);
v___x_176_ = lean_nat_mul(v___x_172_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(3u);
v___x_178_ = lean_nat_mul(v___x_173_, v___x_177_);
v___x_179_ = lean_nat_dec_le(v___x_176_, v___x_178_);
lean_dec(v___x_178_);
lean_dec(v___x_176_);
if (v___x_179_ == 0)
{
lean_dec(v___x_172_);
lean_dec(v_index_168_);
goto v___jp_157_;
}
else
{
lean_object* v___x_180_; 
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
v___x_180_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_130_, v___x_172_, v_index_168_, v_a_131_, v___x_132_);
lean_dec(v_index_168_);
return v___x_180_;
}
}
}
default: 
{
lean_object* v_size_181_; lean_object* v_keyArray_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_size_181_ = lean_ctor_get(v_m_130_, 0);
v_keyArray_182_ = lean_ctor_get(v_m_130_, 1);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_size_181_, v___x_183_);
v___x_185_ = lean_array_get_size(v_keyArray_182_);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec(v___x_184_);
lean_inc_ref(v_x_127_);
lean_inc_ref(v_x_126_);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_126_, v_x_127_, v_m_130_);
v___y_141_ = v___x_187_;
goto v___jp_140_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_188_ = lean_unsigned_to_nat(4u);
v___x_189_ = lean_nat_mul(v___x_184_, v___x_188_);
lean_dec(v___x_184_);
v___x_190_ = lean_unsigned_to_nat(3u);
v___x_191_ = lean_nat_mul(v___x_185_, v___x_190_);
v___x_192_ = lean_nat_dec_le(v___x_189_, v___x_191_);
lean_dec(v___x_191_);
lean_dec(v___x_189_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_inc_ref(v_x_127_);
lean_inc_ref(v_x_126_);
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_126_, v_x_127_, v_m_130_);
v___y_141_ = v___x_193_;
goto v___jp_140_;
}
else
{
v___y_141_ = v_m_130_;
goto v___jp_140_;
}
}
}
}
v___jp_133_:
{
lean_object* v_size_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_size_136_ = lean_ctor_get(v___y_134_, 0);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_size_136_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_134_, v___x_138_, v_i_135_, v_a_131_, v___x_132_);
lean_dec(v_i_135_);
return v___x_139_;
}
v___jp_140_:
{
lean_object* v___x_142_; 
lean_inc(v_a_131_);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_126_, v_x_127_, v___y_141_, v_a_131_);
switch(lean_obj_tag(v___x_142_))
{
case 0:
{
lean_object* v_index_143_; lean_object* v_size_144_; lean_object* v___x_145_; 
v_index_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_143_);
lean_dec_ref_known(v___x_142_, 3);
v_size_144_ = lean_ctor_get(v___y_141_, 0);
lean_inc(v_size_144_);
v___x_145_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_141_, v_size_144_, v_index_143_, v_a_131_, v___x_132_);
lean_dec(v_index_143_);
return v___x_145_;
}
case 1:
{
lean_object* v_index_146_; 
v_index_146_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_146_);
lean_dec_ref_known(v___x_142_, 1);
v___y_134_ = v___y_141_;
v_i_135_ = v_index_146_;
goto v___jp_133_;
}
default: 
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_141_, v___x_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_index_149_; 
v_index_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_index_149_);
lean_dec_ref_known(v___x_148_, 1);
v___y_134_ = v___y_141_;
v_i_135_ = v_index_149_;
goto v___jp_133_;
}
else
{
lean_dec(v_a_131_);
return v___y_141_;
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
v___x_156_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_151_, v___x_155_, v_i_152_, v_a_131_, v___x_132_);
lean_dec(v_i_152_);
return v___x_156_;
}
v___jp_157_:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc_ref(v_x_127_);
lean_inc_ref(v_x_126_);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_126_, v_x_127_, v_m_130_);
lean_inc(v_a_131_);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_126_, v_x_127_, v___x_158_, v_a_131_);
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
v___x_162_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_158_, v_size_161_, v_index_160_, v_a_131_, v___x_132_);
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
lean_dec(v_a_131_);
return v___x_158_;
}
}
}
}
}
}
static lean_object* _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__0, &l_Std_ExtHashSet_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__0);
v___x_195_ = lean_array_get_size(v___x_194_);
return v___x_195_;
}
}
static uint8_t _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_obj_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_unsigned_to_nat(3u);
v___x_200_ = lean_obj_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_201_ = lean_nat_mul(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static uint8_t _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = lean_obj_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2);
v___x_203_ = lean_unsigned_to_nat(4u);
v___x_204_ = lean_nat_dec_le(v___x_203_, v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___y_212_; lean_object* v_i_213_; lean_object* v___y_219_; lean_object* v___y_228_; lean_object* v_i_229_; lean_object* v___x_243_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
v___x_210_ = lean_box(0);
lean_inc(v_a_207_);
lean_inc_ref(v_x_206_);
lean_inc_ref(v_x_205_);
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_205_, v_x_206_, v___x_209_, v_a_207_);
switch(lean_obj_tag(v___x_243_))
{
case 0:
{
lean_dec_ref_known(v___x_243_, 3);
lean_dec(v_a_207_);
lean_dec_ref(v_x_206_);
lean_dec_ref(v_x_205_);
return v___x_209_;
}
case 1:
{
lean_object* v_index_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_index_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_index_244_);
lean_dec_ref_known(v___x_243_, 1);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_uint8_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1);
if (v___x_246_ == 0)
{
lean_dec(v_index_244_);
goto v___jp_234_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = lean_uint8_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3);
if (v___x_247_ == 0)
{
lean_dec(v_index_244_);
goto v___jp_234_;
}
else
{
lean_object* v___x_248_; 
lean_dec_ref(v_x_206_);
lean_dec_ref(v_x_205_);
v___x_248_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_209_, v___x_245_, v_index_244_, v_a_207_, v___x_210_);
lean_dec(v_index_244_);
return v___x_248_;
}
}
}
default: 
{
uint8_t v___x_249_; 
v___x_249_ = lean_uint8_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_inc_ref(v_x_206_);
lean_inc_ref(v_x_205_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_205_, v_x_206_, v___x_209_);
v___y_219_ = v___x_250_;
goto v___jp_218_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = lean_uint8_once(&l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3, &l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once, _init_l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_inc_ref(v_x_206_);
lean_inc_ref(v_x_205_);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_205_, v_x_206_, v___x_209_);
v___y_219_ = v___x_252_;
goto v___jp_218_;
}
else
{
v___y_219_ = v___x_209_;
goto v___jp_218_;
}
}
}
}
v___jp_211_:
{
lean_object* v_size_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_size_214_ = lean_ctor_get(v___y_212_, 0);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_size_214_, v___x_215_);
v___x_217_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_212_, v___x_216_, v_i_213_, v_a_207_, v___x_210_);
lean_dec(v_i_213_);
return v___x_217_;
}
v___jp_218_:
{
lean_object* v___x_220_; 
lean_inc(v_a_207_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_205_, v_x_206_, v___y_219_, v_a_207_);
switch(lean_obj_tag(v___x_220_))
{
case 0:
{
lean_object* v_index_221_; lean_object* v_size_222_; lean_object* v___x_223_; 
v_index_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_index_221_);
lean_dec_ref_known(v___x_220_, 3);
v_size_222_ = lean_ctor_get(v___y_219_, 0);
lean_inc(v_size_222_);
v___x_223_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_219_, v_size_222_, v_index_221_, v_a_207_, v___x_210_);
lean_dec(v_index_221_);
return v___x_223_;
}
case 1:
{
lean_object* v_index_224_; 
v_index_224_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_index_224_);
lean_dec_ref_known(v___x_220_, 1);
v___y_212_ = v___y_219_;
v_i_213_ = v_index_224_;
goto v___jp_211_;
}
default: 
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_219_, v___x_208_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_index_226_; 
v_index_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_index_226_);
lean_dec_ref_known(v___x_225_, 1);
v___y_212_ = v___y_219_;
v_i_213_ = v_index_226_;
goto v___jp_211_;
}
else
{
lean_dec(v_a_207_);
return v___y_219_;
}
}
}
}
v___jp_227_:
{
lean_object* v_size_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_size_230_ = lean_ctor_get(v___y_228_, 0);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_size_230_, v___x_231_);
v___x_233_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_228_, v___x_232_, v_i_229_, v_a_207_, v___x_210_);
lean_dec(v_i_229_);
return v___x_233_;
}
v___jp_234_:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_inc_ref(v_x_206_);
lean_inc_ref(v_x_205_);
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_205_, v_x_206_, v___x_209_);
lean_inc(v_a_207_);
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_205_, v_x_206_, v___x_235_, v_a_207_);
switch(lean_obj_tag(v___x_236_))
{
case 0:
{
lean_object* v_index_237_; lean_object* v_size_238_; lean_object* v___x_239_; 
v_index_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_index_237_);
lean_dec_ref_known(v___x_236_, 3);
v_size_238_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_size_238_);
v___x_239_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_235_, v_size_238_, v_index_237_, v_a_207_, v___x_210_);
lean_dec(v_index_237_);
return v___x_239_;
}
case 1:
{
lean_object* v_index_240_; 
v_index_240_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_index_240_);
lean_dec_ref_known(v___x_236_, 1);
v___y_228_ = v___x_235_;
v_i_229_ = v_index_240_;
goto v___jp_227_;
}
default: 
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_235_, v___x_208_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_index_242_; 
v_index_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_index_242_);
lean_dec_ref_known(v___x_241_, 1);
v___y_228_ = v___x_235_;
v_i_229_ = v_index_242_;
goto v___jp_227_;
}
else
{
lean_dec(v_a_207_);
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_255_, 0, v_x_253_);
lean_closure_set(v___f_255_, 1, v_x_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_inst_259_, lean_object* v_inst_260_){
_start:
{
lean_object* v___f_261_; 
v___f_261_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_261_, 0, v_x_257_);
lean_closure_set(v___f_261_, 1, v_x_258_);
return v___f_261_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_s_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___y_268_; lean_object* v_i_269_; lean_object* v___y_275_; lean_object* v___y_285_; lean_object* v_i_286_; lean_object* v___x_301_; 
v___x_266_ = lean_box(0);
lean_inc(v_a_264_);
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_262_, v_x_263_, v_s_265_, v_a_264_);
switch(lean_obj_tag(v___x_301_))
{
case 0:
{
lean_dec_ref_known(v___x_301_, 3);
lean_dec(v_a_264_);
lean_dec_ref(v_x_263_);
lean_dec_ref(v_x_262_);
return v_s_265_;
}
case 1:
{
lean_object* v_index_302_; lean_object* v_size_303_; lean_object* v_keyArray_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_index_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_index_302_);
lean_dec_ref_known(v___x_301_, 1);
v_size_303_ = lean_ctor_get(v_s_265_, 0);
v_keyArray_304_ = lean_ctor_get(v_s_265_, 1);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_size_303_, v___x_305_);
v___x_307_ = lean_array_get_size(v_keyArray_304_);
v___x_308_ = lean_nat_dec_lt(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v___x_306_);
lean_dec(v_index_302_);
goto v___jp_291_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_309_ = lean_unsigned_to_nat(4u);
v___x_310_ = lean_nat_mul(v___x_306_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(3u);
v___x_312_ = lean_nat_mul(v___x_307_, v___x_311_);
v___x_313_ = lean_nat_dec_le(v___x_310_, v___x_312_);
lean_dec(v___x_312_);
lean_dec(v___x_310_);
if (v___x_313_ == 0)
{
lean_dec(v___x_306_);
lean_dec(v_index_302_);
goto v___jp_291_;
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v_x_263_);
lean_dec_ref(v_x_262_);
v___x_314_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_265_, v___x_306_, v_index_302_, v_a_264_, v___x_266_);
lean_dec(v_index_302_);
return v___x_314_;
}
}
}
default: 
{
lean_object* v_size_315_; lean_object* v_keyArray_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_size_315_ = lean_ctor_get(v_s_265_, 0);
v_keyArray_316_ = lean_ctor_get(v_s_265_, 1);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_size_315_, v___x_317_);
v___x_319_ = lean_array_get_size(v_keyArray_316_);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
lean_dec(v___x_318_);
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_262_, v_x_263_, v_s_265_);
v___y_275_ = v___x_321_;
goto v___jp_274_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_322_ = lean_unsigned_to_nat(4u);
v___x_323_ = lean_nat_mul(v___x_318_, v___x_322_);
lean_dec(v___x_318_);
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_nat_mul(v___x_319_, v___x_324_);
v___x_326_ = lean_nat_dec_le(v___x_323_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v___x_323_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_262_, v_x_263_, v_s_265_);
v___y_275_ = v___x_327_;
goto v___jp_274_;
}
else
{
v___y_275_ = v_s_265_;
goto v___jp_274_;
}
}
}
}
v___jp_267_:
{
lean_object* v_size_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_size_270_ = lean_ctor_get(v___y_268_, 0);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_size_270_, v___x_271_);
v___x_273_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_268_, v___x_272_, v_i_269_, v_a_264_, v___x_266_);
lean_dec(v_i_269_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_276_; 
lean_inc(v_a_264_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_262_, v_x_263_, v___y_275_, v_a_264_);
switch(lean_obj_tag(v___x_276_))
{
case 0:
{
lean_object* v_index_277_; lean_object* v_size_278_; lean_object* v___x_279_; 
v_index_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_277_);
lean_dec_ref_known(v___x_276_, 3);
v_size_278_ = lean_ctor_get(v___y_275_, 0);
lean_inc(v_size_278_);
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_275_, v_size_278_, v_index_277_, v_a_264_, v___x_266_);
lean_dec(v_index_277_);
return v___x_279_;
}
case 1:
{
lean_object* v_index_280_; 
v_index_280_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_280_);
lean_dec_ref_known(v___x_276_, 1);
v___y_268_ = v___y_275_;
v_i_269_ = v_index_280_;
goto v___jp_267_;
}
default: 
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_275_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_index_283_; 
v_index_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_283_);
lean_dec_ref_known(v___x_282_, 1);
v___y_268_ = v___y_275_;
v_i_269_ = v_index_283_;
goto v___jp_267_;
}
else
{
lean_dec(v_a_264_);
return v___y_275_;
}
}
}
}
v___jp_284_:
{
lean_object* v_size_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_size_287_ = lean_ctor_get(v___y_285_, 0);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_size_287_, v___x_288_);
v___x_290_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_285_, v___x_289_, v_i_286_, v_a_264_, v___x_266_);
lean_dec(v_i_286_);
return v___x_290_;
}
v___jp_291_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_262_, v_x_263_, v_s_265_);
lean_inc(v_a_264_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_262_, v_x_263_, v___x_292_, v_a_264_);
switch(lean_obj_tag(v___x_293_))
{
case 0:
{
lean_object* v_index_294_; lean_object* v_size_295_; lean_object* v___x_296_; 
v_index_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_index_294_);
lean_dec_ref_known(v___x_293_, 3);
v_size_295_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_size_295_);
v___x_296_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_292_, v_size_295_, v_index_294_, v_a_264_, v___x_266_);
lean_dec(v_index_294_);
return v___x_296_;
}
case 1:
{
lean_object* v_index_297_; 
v_index_297_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_index_297_);
lean_dec_ref_known(v___x_293_, 1);
v___y_285_ = v___x_292_;
v_i_286_ = v_index_297_;
goto v___jp_284_;
}
default: 
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_292_, v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_index_300_; 
v_index_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_299_, 1);
v___y_285_ = v___x_292_;
v_i_286_ = v_index_300_;
goto v___jp_284_;
}
else
{
lean_dec(v_a_264_);
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
lean_object* v___f_330_; 
v___f_330_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_330_, 0, v_x_328_);
lean_closure_set(v___f_330_, 1, v_x_329_);
return v___f_330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_inst_334_, lean_object* v_inst_335_){
_start:
{
lean_object* v___f_336_; 
v___f_336_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_336_, 0, v_x_332_);
lean_closure_set(v___f_336_, 1, v_x_333_);
return v___f_336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert___redArg(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(0);
lean_inc(v_a_340_);
lean_inc_ref(v_x_338_);
lean_inc_ref(v_x_337_);
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_337_, v_x_338_, v_m_339_, v_a_340_);
switch(lean_obj_tag(v___x_342_))
{
case 0:
{
uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec_ref_known(v___x_342_, 3);
lean_dec(v_a_340_);
lean_dec_ref(v_x_338_);
lean_dec_ref(v_x_337_);
v___x_343_ = 1;
v___x_344_ = lean_box(v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_m_339_);
return v___x_345_;
}
case 1:
{
lean_object* v_index_346_; lean_object* v_size_347_; lean_object* v_keyArray_348_; uint8_t v___x_349_; lean_object* v___y_351_; lean_object* v_i_352_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_index_346_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_index_346_);
lean_dec_ref_known(v___x_342_, 1);
v_size_347_ = lean_ctor_get(v_m_339_, 0);
v_keyArray_348_ = lean_ctor_get(v_m_339_, 1);
v___x_349_ = 0;
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_size_347_, v___x_373_);
v___x_375_ = lean_array_get_size(v_keyArray_348_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_dec(v___x_374_);
lean_dec(v_index_346_);
goto v___jp_359_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_377_ = lean_unsigned_to_nat(4u);
v___x_378_ = lean_nat_mul(v___x_374_, v___x_377_);
v___x_379_ = lean_unsigned_to_nat(3u);
v___x_380_ = lean_nat_mul(v___x_375_, v___x_379_);
v___x_381_ = lean_nat_dec_le(v___x_378_, v___x_380_);
lean_dec(v___x_380_);
lean_dec(v___x_378_);
if (v___x_381_ == 0)
{
lean_dec(v___x_374_);
lean_dec(v_index_346_);
goto v___jp_359_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec_ref(v_x_338_);
lean_dec_ref(v_x_337_);
v___x_382_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_339_, v___x_374_, v_index_346_, v_a_340_, v___x_341_);
lean_dec(v_index_346_);
v___x_383_ = lean_box(v___x_349_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
return v___x_384_;
}
}
v___jp_350_:
{
lean_object* v_size_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_size_353_ = lean_ctor_get(v___y_351_, 0);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_size_353_, v___x_354_);
v___x_356_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_351_, v___x_355_, v_i_352_, v_a_340_, v___x_341_);
lean_dec(v_i_352_);
v___x_357_ = lean_box(v___x_349_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_inc_ref(v_x_338_);
lean_inc_ref(v_x_337_);
v___x_360_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_337_, v_x_338_, v_m_339_);
lean_inc(v_a_340_);
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_337_, v_x_338_, v___x_360_, v_a_340_);
switch(lean_obj_tag(v___x_361_))
{
case 0:
{
lean_object* v_index_362_; lean_object* v_size_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_index_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_index_362_);
lean_dec_ref_known(v___x_361_, 3);
v_size_363_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_size_363_);
v___x_364_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_360_, v_size_363_, v_index_362_, v_a_340_, v___x_341_);
lean_dec(v_index_362_);
v___x_365_ = lean_box(v___x_349_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
return v___x_366_;
}
case 1:
{
lean_object* v_index_367_; 
v_index_367_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_index_367_);
lean_dec_ref_known(v___x_361_, 1);
v___y_351_ = v___x_360_;
v_i_352_ = v_index_367_;
goto v___jp_350_;
}
default: 
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_360_, v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_index_370_; 
v_index_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_index_370_);
lean_dec_ref_known(v___x_369_, 1);
v___y_351_ = v___x_360_;
v_i_352_ = v_index_370_;
goto v___jp_350_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_a_340_);
v___x_371_ = lean_box(v___x_349_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_360_);
return v___x_372_;
}
}
}
}
}
default: 
{
lean_object* v_size_385_; lean_object* v_keyArray_386_; uint8_t v___x_387_; lean_object* v___y_389_; lean_object* v_i_390_; lean_object* v___y_398_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_size_385_ = lean_ctor_get(v_m_339_, 0);
v_keyArray_386_ = lean_ctor_get(v_m_339_, 1);
v___x_387_ = 0;
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_add(v_size_385_, v___x_411_);
v___x_413_ = lean_array_get_size(v_keyArray_386_);
v___x_414_ = lean_nat_dec_lt(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v___x_412_);
lean_inc_ref(v_x_338_);
lean_inc_ref(v_x_337_);
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_337_, v_x_338_, v_m_339_);
v___y_398_ = v___x_415_;
goto v___jp_397_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_416_ = lean_unsigned_to_nat(4u);
v___x_417_ = lean_nat_mul(v___x_412_, v___x_416_);
lean_dec(v___x_412_);
v___x_418_ = lean_unsigned_to_nat(3u);
v___x_419_ = lean_nat_mul(v___x_413_, v___x_418_);
v___x_420_ = lean_nat_dec_le(v___x_417_, v___x_419_);
lean_dec(v___x_419_);
lean_dec(v___x_417_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_inc_ref(v_x_338_);
lean_inc_ref(v_x_337_);
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_337_, v_x_338_, v_m_339_);
v___y_398_ = v___x_421_;
goto v___jp_397_;
}
else
{
v___y_398_ = v_m_339_;
goto v___jp_397_;
}
}
v___jp_388_:
{
lean_object* v_size_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_size_391_ = lean_ctor_get(v___y_389_, 0);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_add(v_size_391_, v___x_392_);
v___x_394_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_389_, v___x_393_, v_i_390_, v_a_340_, v___x_341_);
lean_dec(v_i_390_);
v___x_395_ = lean_box(v___x_387_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
return v___x_396_;
}
v___jp_397_:
{
lean_object* v___x_399_; 
lean_inc(v_a_340_);
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_337_, v_x_338_, v___y_398_, v_a_340_);
switch(lean_obj_tag(v___x_399_))
{
case 0:
{
lean_object* v_index_400_; lean_object* v_size_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_index_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_index_400_);
lean_dec_ref_known(v___x_399_, 3);
v_size_401_ = lean_ctor_get(v___y_398_, 0);
lean_inc(v_size_401_);
v___x_402_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_398_, v_size_401_, v_index_400_, v_a_340_, v___x_341_);
lean_dec(v_index_400_);
v___x_403_ = lean_box(v___x_387_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
return v___x_404_;
}
case 1:
{
lean_object* v_index_405_; 
v_index_405_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_index_405_);
lean_dec_ref_known(v___x_399_, 1);
v___y_389_ = v___y_398_;
v_i_390_ = v_index_405_;
goto v___jp_388_;
}
default: 
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_398_, v___x_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_index_408_; 
v_index_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_index_408_);
lean_dec_ref_known(v___x_407_, 1);
v___y_389_ = v___y_398_;
v_i_390_ = v_index_408_;
goto v___jp_388_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_a_340_);
v___x_409_ = lean_box(v___x_387_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___y_398_);
return v___x_410_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert(lean_object* v_00_u03b1_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_m_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
lean_inc(v_a_428_);
lean_inc_ref(v_x_424_);
lean_inc_ref(v_x_423_);
v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_423_, v_x_424_, v_m_427_, v_a_428_);
switch(lean_obj_tag(v___x_430_))
{
case 0:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref_known(v___x_430_, 3);
lean_dec(v_a_428_);
lean_dec_ref(v_x_424_);
lean_dec_ref(v_x_423_);
v___x_431_ = 1;
v___x_432_ = lean_box(v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_m_427_);
return v___x_433_;
}
case 1:
{
lean_object* v_index_434_; lean_object* v_size_435_; lean_object* v_keyArray_436_; uint8_t v___x_437_; lean_object* v___y_439_; lean_object* v_i_440_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_index_434_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_index_434_);
lean_dec_ref_known(v___x_430_, 1);
v_size_435_ = lean_ctor_get(v_m_427_, 0);
v_keyArray_436_ = lean_ctor_get(v_m_427_, 1);
v___x_437_ = 0;
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_add(v_size_435_, v___x_461_);
v___x_463_ = lean_array_get_size(v_keyArray_436_);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec(v___x_462_);
lean_dec(v_index_434_);
goto v___jp_447_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_465_ = lean_unsigned_to_nat(4u);
v___x_466_ = lean_nat_mul(v___x_462_, v___x_465_);
v___x_467_ = lean_unsigned_to_nat(3u);
v___x_468_ = lean_nat_mul(v___x_463_, v___x_467_);
v___x_469_ = lean_nat_dec_le(v___x_466_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_466_);
if (v___x_469_ == 0)
{
lean_dec(v___x_462_);
lean_dec(v_index_434_);
goto v___jp_447_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref(v_x_424_);
lean_dec_ref(v_x_423_);
v___x_470_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_427_, v___x_462_, v_index_434_, v_a_428_, v___x_429_);
lean_dec(v_index_434_);
v___x_471_ = lean_box(v___x_437_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
return v___x_472_;
}
}
v___jp_438_:
{
lean_object* v_size_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_size_441_ = lean_ctor_get(v___y_439_, 0);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_size_441_, v___x_442_);
v___x_444_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_439_, v___x_443_, v_i_440_, v_a_428_, v___x_429_);
lean_dec(v_i_440_);
v___x_445_ = lean_box(v___x_437_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
return v___x_446_;
}
v___jp_447_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_inc_ref(v_x_424_);
lean_inc_ref(v_x_423_);
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_423_, v_x_424_, v_m_427_);
lean_inc(v_a_428_);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_423_, v_x_424_, v___x_448_, v_a_428_);
switch(lean_obj_tag(v___x_449_))
{
case 0:
{
lean_object* v_index_450_; lean_object* v_size_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_index_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_index_450_);
lean_dec_ref_known(v___x_449_, 3);
v_size_451_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_size_451_);
v___x_452_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_448_, v_size_451_, v_index_450_, v_a_428_, v___x_429_);
lean_dec(v_index_450_);
v___x_453_ = lean_box(v___x_437_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
return v___x_454_;
}
case 1:
{
lean_object* v_index_455_; 
v_index_455_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_index_455_);
lean_dec_ref_known(v___x_449_, 1);
v___y_439_ = v___x_448_;
v_i_440_ = v_index_455_;
goto v___jp_438_;
}
default: 
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_448_, v___x_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_index_458_; 
v_index_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_index_458_);
lean_dec_ref_known(v___x_457_, 1);
v___y_439_ = v___x_448_;
v_i_440_ = v_index_458_;
goto v___jp_438_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_a_428_);
v___x_459_ = lean_box(v___x_437_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_448_);
return v___x_460_;
}
}
}
}
}
default: 
{
lean_object* v_size_473_; lean_object* v_keyArray_474_; uint8_t v___x_475_; lean_object* v___y_477_; lean_object* v_i_478_; lean_object* v___y_486_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_size_473_ = lean_ctor_get(v_m_427_, 0);
v_keyArray_474_ = lean_ctor_get(v_m_427_, 1);
v___x_475_ = 0;
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_size_473_, v___x_499_);
v___x_501_ = lean_array_get_size(v_keyArray_474_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v___x_500_);
lean_inc_ref(v_x_424_);
lean_inc_ref(v_x_423_);
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_423_, v_x_424_, v_m_427_);
v___y_486_ = v___x_503_;
goto v___jp_485_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_504_ = lean_unsigned_to_nat(4u);
v___x_505_ = lean_nat_mul(v___x_500_, v___x_504_);
lean_dec(v___x_500_);
v___x_506_ = lean_unsigned_to_nat(3u);
v___x_507_ = lean_nat_mul(v___x_501_, v___x_506_);
v___x_508_ = lean_nat_dec_le(v___x_505_, v___x_507_);
lean_dec(v___x_507_);
lean_dec(v___x_505_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_inc_ref(v_x_424_);
lean_inc_ref(v_x_423_);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_423_, v_x_424_, v_m_427_);
v___y_486_ = v___x_509_;
goto v___jp_485_;
}
else
{
v___y_486_ = v_m_427_;
goto v___jp_485_;
}
}
v___jp_476_:
{
lean_object* v_size_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_size_479_ = lean_ctor_get(v___y_477_, 0);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_size_479_, v___x_480_);
v___x_482_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_477_, v___x_481_, v_i_478_, v_a_428_, v___x_429_);
lean_dec(v_i_478_);
v___x_483_ = lean_box(v___x_475_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
return v___x_484_;
}
v___jp_485_:
{
lean_object* v___x_487_; 
lean_inc(v_a_428_);
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_423_, v_x_424_, v___y_486_, v_a_428_);
switch(lean_obj_tag(v___x_487_))
{
case 0:
{
lean_object* v_index_488_; lean_object* v_size_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_index_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_index_488_);
lean_dec_ref_known(v___x_487_, 3);
v_size_489_ = lean_ctor_get(v___y_486_, 0);
lean_inc(v_size_489_);
v___x_490_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_486_, v_size_489_, v_index_488_, v_a_428_, v___x_429_);
lean_dec(v_index_488_);
v___x_491_ = lean_box(v___x_475_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
return v___x_492_;
}
case 1:
{
lean_object* v_index_493_; 
v_index_493_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_index_493_);
lean_dec_ref_known(v___x_487_, 1);
v___y_477_ = v___y_486_;
v_i_478_ = v_index_493_;
goto v___jp_476_;
}
default: 
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_486_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_index_496_; 
v_index_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_index_496_);
lean_dec_ref_known(v___x_495_, 1);
v___y_477_ = v___y_486_;
v_i_478_ = v_index_496_;
goto v___jp_476_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_a_428_);
v___x_497_ = lean_box(v___x_475_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___y_486_);
return v___x_498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains___redArg(lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_510_, v_x_511_, v_m_512_, v_a_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___redArg___boxed(lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_m_517_, lean_object* v_a_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Std_ExtHashSet_contains___redArg(v_x_515_, v_x_516_, v_m_517_, v_a_518_);
lean_dec(v_m_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains(lean_object* v_00_u03b1_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_m_526_, lean_object* v_a_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_522_, v_x_523_, v_m_526_, v_a_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___boxed(lean_object* v_00_u03b1_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Std_ExtHashSet_contains(v_00_u03b1_529_, v_x_530_, v_x_531_, v_inst_532_, v_inst_533_, v_m_534_, v_a_535_);
lean_dec(v_m_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_inst_548_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_inst_545_);
return v_res_549_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem___redArg(lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_m_552_, lean_object* v_a_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_550_, v_inst_551_, v_m_552_, v_a_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_m_557_, lean_object* v_a_558_){
_start:
{
uint8_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = l_Std_ExtHashSet_instDecidableMem___redArg(v_inst_555_, v_inst_556_, v_m_557_, v_a_558_);
lean_dec(v_m_557_);
v_r_560_ = lean_box(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem(lean_object* v_00_u03b1_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_562_, v_inst_563_, v_m_566_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_m_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = l_Std_ExtHashSet_instDecidableMem(v_00_u03b1_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_inst_573_, v_m_574_, v_a_575_);
lean_dec(v_m_574_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase___redArg(lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_m_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_578_, v_x_579_, v_m_580_, v_a_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase(lean_object* v_00_u03b1_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_m_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_584_, v_x_585_, v_m_588_, v_a_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg(lean_object* v_m_591_){
_start:
{
lean_object* v_size_592_; 
v_size_592_ = lean_ctor_get(v_m_591_, 0);
lean_inc(v_size_592_);
return v_size_592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg___boxed(lean_object* v_m_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_ExtHashSet_size___redArg(v_m_593_);
lean_dec(v_m_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size(lean_object* v_00_u03b1_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_m_600_){
_start:
{
lean_object* v_size_601_; 
v_size_601_ = lean_ctor_get(v_m_600_, 0);
lean_inc(v_size_601_);
return v_size_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___boxed(lean_object* v_00_u03b1_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_m_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_ExtHashSet_size(v_00_u03b1_602_, v_x_603_, v_x_604_, v_inst_605_, v_inst_606_, v_m_607_);
lean_dec(v_m_607_);
lean_dec_ref(v_x_604_);
lean_dec_ref(v_x_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg(lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_m_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_609_, v_x_610_, v_m_611_, v_a_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg___boxed(lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_m_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_ExtHashSet_get_x3f___redArg(v_x_614_, v_x_615_, v_m_616_, v_a_617_);
lean_dec(v_m_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f(lean_object* v_00_u03b1_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_620_, v_x_621_, v_m_624_, v_a_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___boxed(lean_object* v_00_u03b1_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_m_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_ExtHashSet_get_x3f(v_00_u03b1_627_, v_x_628_, v_x_629_, v_inst_630_, v_inst_631_, v_m_632_, v_a_633_);
lean_dec(v_m_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_m_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_639_; lean_object* v_val_640_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_635_, v_x_636_, v_m_637_, v_a_638_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec(v___x_639_);
return v_val_640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg___boxed(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_m_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_ExtHashSet_get___redArg(v_x_641_, v_x_642_, v_m_643_, v_a_644_);
lean_dec(v_m_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get(lean_object* v_00_u03b1_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_m_651_, lean_object* v_a_652_, lean_object* v_h_653_){
_start:
{
lean_object* v___x_654_; lean_object* v_val_655_; 
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_647_, v_x_648_, v_m_651_, v_a_652_);
v_val_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_655_);
lean_dec(v___x_654_);
return v_val_655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___boxed(lean_object* v_00_u03b1_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_m_661_, lean_object* v_a_662_, lean_object* v_h_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_ExtHashSet_get(v_00_u03b1_656_, v_x_657_, v_x_658_, v_inst_659_, v_inst_660_, v_m_661_, v_a_662_, v_h_663_);
lean_dec(v_m_661_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg(lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_m_667_, lean_object* v_a_668_, lean_object* v_fallback_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_665_, v_x_666_, v_m_667_, v_a_668_, v_fallback_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_m_673_, lean_object* v_a_674_, lean_object* v_fallback_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_ExtHashSet_getD___redArg(v_x_671_, v_x_672_, v_m_673_, v_a_674_, v_fallback_675_);
lean_dec(v_fallback_675_);
lean_dec(v_m_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD(lean_object* v_00_u03b1_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_m_682_, lean_object* v_a_683_, lean_object* v_fallback_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_678_, v_x_679_, v_m_682_, v_a_683_, v_fallback_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___boxed(lean_object* v_00_u03b1_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_m_691_, lean_object* v_a_692_, lean_object* v_fallback_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_ExtHashSet_getD(v_00_u03b1_686_, v_x_687_, v_x_688_, v_inst_689_, v_inst_690_, v_m_691_, v_a_692_, v_fallback_693_);
lean_dec(v_fallback_693_);
lean_dec(v_m_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg(lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_inst_697_, lean_object* v_m_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_695_, v_x_696_, v_inst_697_, v_m_698_, v_a_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg___boxed(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_inst_703_, lean_object* v_m_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_ExtHashSet_get_x21___redArg(v_x_701_, v_x_702_, v_inst_703_, v_m_704_, v_a_705_);
lean_dec(v_m_704_);
lean_dec(v_inst_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21(lean_object* v_00_u03b1_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_m_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_708_, v_x_709_, v_inst_712_, v_m_713_, v_a_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___boxed(lean_object* v_00_u03b1_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_m_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_ExtHashSet_get_x21(v_00_u03b1_716_, v_x_717_, v_x_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_m_722_, v_a_723_);
lean_dec(v_m_722_);
lean_dec(v_inst_721_);
return v_res_724_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty___redArg(lean_object* v_m_725_){
_start:
{
lean_object* v_size_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_size_726_ = lean_ctor_get(v_m_725_, 0);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_nat_dec_eq(v_size_726_, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___redArg___boxed(lean_object* v_m_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Std_ExtHashSet_isEmpty___redArg(v_m_729_);
lean_dec(v_m_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty(lean_object* v_00_u03b1_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_m_737_){
_start:
{
lean_object* v_size_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_size_738_ = lean_ctor_get(v_m_737_, 0);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_nat_dec_eq(v_size_738_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___boxed(lean_object* v_00_u03b1_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_m_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Std_ExtHashSet_isEmpty(v_00_u03b1_741_, v_x_742_, v_x_743_, v_inst_744_, v_inst_745_, v_m_746_);
lean_dec(v_m_746_);
lean_dec_ref(v_x_743_);
lean_dec_ref(v_x_742_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList___redArg(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_l_774_){
_start:
{
lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___f_775_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_776_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
v___x_777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_775_, v_inst_772_, v_inst_773_, v___x_776_, v_l_774_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList(lean_object* v_00_u03b1_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_l_781_){
_start:
{
lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___f_782_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_783_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_782_, v_inst_779_, v_inst_780_, v___x_783_, v_l_781_);
return v___x_784_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_filter___redArg___lam__0(lean_object* v_f_785_, lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_apply_1(v_f_785_, v_a_786_);
v___x_789_ = lean_unbox(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___lam__0___boxed(lean_object* v_f_790_, lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Std_ExtHashSet_filter___redArg___lam__0(v_f_790_, v_a_791_, v_x_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg(lean_object* v_f_795_, lean_object* v_m_796_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; 
v___f_797_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_797_, 0, v_f_795_);
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_797_, v_m_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___boxed(lean_object* v_f_799_, lean_object* v_m_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_ExtHashSet_filter___redArg(v_f_799_, v_m_800_);
lean_dec(v_m_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter(lean_object* v_00_u03b1_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_f_807_, lean_object* v_m_808_){
_start:
{
lean_object* v___f_809_; lean_object* v___x_810_; 
v___f_809_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_809_, 0, v_f_807_);
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_809_, v_m_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___boxed(lean_object* v_00_u03b1_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_f_816_, lean_object* v_m_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_ExtHashSet_filter(v_00_u03b1_811_, v_x_812_, v_x_813_, v_inst_814_, v_inst_815_, v_f_816_, v_m_817_);
lean_dec(v_m_817_);
lean_dec_ref(v_x_813_);
lean_dec_ref(v_x_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg___lam__0(lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_a_821_, lean_object* v_____s_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___y_825_; lean_object* v_i_826_; lean_object* v___y_833_; lean_object* v___y_845_; lean_object* v_i_846_; lean_object* v___x_864_; 
v___x_823_ = lean_box(0);
lean_inc(v_a_821_);
lean_inc_ref(v_x_820_);
lean_inc_ref(v_x_819_);
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_819_, v_x_820_, v_____s_822_, v_a_821_);
switch(lean_obj_tag(v___x_864_))
{
case 0:
{
lean_object* v___x_865_; 
lean_dec_ref_known(v___x_864_, 3);
lean_dec(v_a_821_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_____s_822_);
return v___x_865_;
}
case 1:
{
lean_object* v_index_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_885_; 
v_index_866_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_885_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_885_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_index_866_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_885_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_size_870_; lean_object* v_keyArray_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_size_870_ = lean_ctor_get(v_____s_822_, 0);
v_keyArray_871_ = lean_ctor_get(v_____s_822_, 1);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_add(v_size_870_, v___x_872_);
v___x_874_ = lean_array_get_size(v_keyArray_871_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec(v___x_873_);
lean_del_object(v___x_868_);
lean_dec(v_index_866_);
goto v___jp_852_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_876_ = lean_unsigned_to_nat(4u);
v___x_877_ = lean_nat_mul(v___x_873_, v___x_876_);
v___x_878_ = lean_unsigned_to_nat(3u);
v___x_879_ = lean_nat_mul(v___x_874_, v___x_878_);
v___x_880_ = lean_nat_dec_le(v___x_877_, v___x_879_);
lean_dec(v___x_879_);
lean_dec(v___x_877_);
if (v___x_880_ == 0)
{
lean_dec(v___x_873_);
lean_del_object(v___x_868_);
lean_dec(v_index_866_);
goto v___jp_852_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_883_; 
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
v___x_881_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_822_, v___x_873_, v_index_866_, v_a_821_, v___x_823_);
lean_dec(v_index_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_881_);
v___x_883_ = v___x_868_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
default: 
{
lean_object* v_size_886_; lean_object* v_keyArray_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_size_886_ = lean_ctor_get(v_____s_822_, 0);
v_keyArray_887_ = lean_ctor_get(v_____s_822_, 1);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_size_886_, v___x_888_);
v___x_890_ = lean_array_get_size(v_keyArray_887_);
v___x_891_ = lean_nat_dec_lt(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v___x_889_);
lean_inc_ref(v_x_820_);
lean_inc_ref(v_x_819_);
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_819_, v_x_820_, v_____s_822_);
v___y_833_ = v___x_892_;
goto v___jp_832_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_893_ = lean_unsigned_to_nat(4u);
v___x_894_ = lean_nat_mul(v___x_889_, v___x_893_);
lean_dec(v___x_889_);
v___x_895_ = lean_unsigned_to_nat(3u);
v___x_896_ = lean_nat_mul(v___x_890_, v___x_895_);
v___x_897_ = lean_nat_dec_le(v___x_894_, v___x_896_);
lean_dec(v___x_896_);
lean_dec(v___x_894_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_inc_ref(v_x_820_);
lean_inc_ref(v_x_819_);
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_819_, v_x_820_, v_____s_822_);
v___y_833_ = v___x_898_;
goto v___jp_832_;
}
else
{
v___y_833_ = v_____s_822_;
goto v___jp_832_;
}
}
}
}
v___jp_824_:
{
lean_object* v_size_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_size_827_ = lean_ctor_get(v___y_825_, 0);
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_nat_add(v_size_827_, v___x_828_);
v___x_830_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_825_, v___x_829_, v_i_826_, v_a_821_, v___x_823_);
lean_dec(v_i_826_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
v___jp_832_:
{
lean_object* v___x_834_; 
lean_inc(v_a_821_);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_819_, v_x_820_, v___y_833_, v_a_821_);
switch(lean_obj_tag(v___x_834_))
{
case 0:
{
lean_object* v_index_835_; lean_object* v_size_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_index_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_index_835_);
lean_dec_ref_known(v___x_834_, 3);
v_size_836_ = lean_ctor_get(v___y_833_, 0);
lean_inc(v_size_836_);
v___x_837_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_833_, v_size_836_, v_index_835_, v_a_821_, v___x_823_);
lean_dec(v_index_835_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
case 1:
{
lean_object* v_index_839_; 
v_index_839_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_index_839_);
lean_dec_ref_known(v___x_834_, 1);
v___y_825_ = v___y_833_;
v_i_826_ = v_index_839_;
goto v___jp_824_;
}
default: 
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_833_, v___x_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_index_842_; 
v_index_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_index_842_);
lean_dec_ref_known(v___x_841_, 1);
v___y_825_ = v___y_833_;
v_i_826_ = v_index_842_;
goto v___jp_824_;
}
else
{
lean_object* v___x_843_; 
lean_dec(v_a_821_);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___y_833_);
return v___x_843_;
}
}
}
}
v___jp_844_:
{
lean_object* v_size_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_size_847_ = lean_ctor_get(v___y_845_, 0);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_size_847_, v___x_848_);
v___x_850_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_845_, v___x_849_, v_i_846_, v_a_821_, v___x_823_);
lean_dec(v_i_846_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
v___jp_852_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_inc_ref(v_x_820_);
lean_inc_ref(v_x_819_);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_819_, v_x_820_, v_____s_822_);
lean_inc(v_a_821_);
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_819_, v_x_820_, v___x_853_, v_a_821_);
switch(lean_obj_tag(v___x_854_))
{
case 0:
{
lean_object* v_index_855_; lean_object* v_size_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_index_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_index_855_);
lean_dec_ref_known(v___x_854_, 3);
v_size_856_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_size_856_);
v___x_857_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_853_, v_size_856_, v_index_855_, v_a_821_, v___x_823_);
lean_dec(v_index_855_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
case 1:
{
lean_object* v_index_859_; 
v_index_859_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_index_859_);
lean_dec_ref_known(v___x_854_, 1);
v___y_845_ = v___x_853_;
v_i_846_ = v_index_859_;
goto v___jp_844_;
}
default: 
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_853_, v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_index_862_; 
v_index_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_index_862_);
lean_dec_ref_known(v___x_861_, 1);
v___y_845_ = v___x_853_;
v_i_846_ = v_index_862_;
goto v___jp_844_;
}
else
{
lean_object* v___x_863_; 
lean_dec(v_a_821_);
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_853_);
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg(lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_inst_901_, lean_object* v_m_902_, lean_object* v_l_903_){
_start:
{
lean_object* v___f_904_; lean_object* v___x_905_; 
v___f_904_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_904_, 0, v_x_899_);
lean_closure_set(v___f_904_, 1, v_x_900_);
v___x_905_ = lean_apply_4(v_inst_901_, lean_box(0), v_l_903_, v_m_902_, v___f_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany(lean_object* v_00_u03b1_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_00_u03c1_911_, lean_object* v_inst_912_, lean_object* v_m_913_, lean_object* v_l_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; 
v___f_915_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_915_, 0, v_x_907_);
lean_closure_set(v___f_915_, 1, v_x_908_);
v___x_916_ = lean_apply_4(v_inst_912_, lean_box(0), v_l_914_, v_m_913_, v___f_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__0(lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_b_920_, lean_object* v_acc_921_){
_start:
{
lean_object* v___y_923_; lean_object* v_i_924_; lean_object* v___y_943_; lean_object* v_i_944_; lean_object* v___y_951_; lean_object* v___x_962_; 
lean_inc(v_a_919_);
lean_inc_ref(v_x_918_);
lean_inc_ref(v_x_917_);
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_917_, v_x_918_, v_acc_921_, v_a_919_);
switch(lean_obj_tag(v___x_962_))
{
case 0:
{
lean_object* v___x_963_; 
lean_dec_ref_known(v___x_962_, 3);
lean_dec(v_a_919_);
lean_dec_ref(v_x_918_);
lean_dec_ref(v_x_917_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_acc_921_);
return v___x_963_;
}
case 1:
{
lean_object* v_index_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_983_; 
v_index_964_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_983_ == 0)
{
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_983_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_index_964_);
lean_dec(v___x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_983_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_size_968_; lean_object* v_keyArray_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_size_968_ = lean_ctor_get(v_acc_921_, 0);
v_keyArray_969_ = lean_ctor_get(v_acc_921_, 1);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_add(v_size_968_, v___x_970_);
v___x_972_ = lean_array_get_size(v_keyArray_969_);
v___x_973_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec(v___x_971_);
lean_del_object(v___x_966_);
lean_dec(v_index_964_);
goto v___jp_930_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_974_ = lean_unsigned_to_nat(4u);
v___x_975_ = lean_nat_mul(v___x_971_, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(3u);
v___x_977_ = lean_nat_mul(v___x_972_, v___x_976_);
v___x_978_ = lean_nat_dec_le(v___x_975_, v___x_977_);
lean_dec(v___x_977_);
lean_dec(v___x_975_);
if (v___x_978_ == 0)
{
lean_dec(v___x_971_);
lean_del_object(v___x_966_);
lean_dec(v_index_964_);
goto v___jp_930_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec_ref(v_x_918_);
lean_dec_ref(v_x_917_);
v___x_979_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_921_, v___x_971_, v_index_964_, v_a_919_, v_b_920_);
lean_dec(v_index_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_979_);
v___x_981_ = v___x_966_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
default: 
{
lean_object* v_size_984_; lean_object* v_keyArray_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_size_984_ = lean_ctor_get(v_acc_921_, 0);
v_keyArray_985_ = lean_ctor_get(v_acc_921_, 1);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_add(v_size_984_, v___x_986_);
v___x_988_ = lean_array_get_size(v_keyArray_985_);
v___x_989_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
lean_dec(v___x_987_);
lean_inc_ref(v_x_918_);
lean_inc_ref(v_x_917_);
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_917_, v_x_918_, v_acc_921_);
v___y_951_ = v___x_990_;
goto v___jp_950_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_991_ = lean_unsigned_to_nat(4u);
v___x_992_ = lean_nat_mul(v___x_987_, v___x_991_);
lean_dec(v___x_987_);
v___x_993_ = lean_unsigned_to_nat(3u);
v___x_994_ = lean_nat_mul(v___x_988_, v___x_993_);
v___x_995_ = lean_nat_dec_le(v___x_992_, v___x_994_);
lean_dec(v___x_994_);
lean_dec(v___x_992_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_inc_ref(v_x_918_);
lean_inc_ref(v_x_917_);
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_917_, v_x_918_, v_acc_921_);
v___y_951_ = v___x_996_;
goto v___jp_950_;
}
else
{
v___y_951_ = v_acc_921_;
goto v___jp_950_;
}
}
}
}
v___jp_922_:
{
lean_object* v_size_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_size_925_ = lean_ctor_get(v___y_923_, 0);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_size_925_, v___x_926_);
v___x_928_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_923_, v___x_927_, v_i_924_, v_a_919_, v_b_920_);
lean_dec(v_i_924_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
v___jp_930_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc_ref(v_x_918_);
lean_inc_ref(v_x_917_);
v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_917_, v_x_918_, v_acc_921_);
lean_inc(v_a_919_);
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_917_, v_x_918_, v___x_931_, v_a_919_);
switch(lean_obj_tag(v___x_932_))
{
case 0:
{
lean_object* v_index_933_; lean_object* v_size_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_index_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_index_933_);
lean_dec_ref_known(v___x_932_, 3);
v_size_934_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_size_934_);
v___x_935_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_931_, v_size_934_, v_index_933_, v_a_919_, v_b_920_);
lean_dec(v_index_933_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
case 1:
{
lean_object* v_index_937_; 
v_index_937_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_index_937_);
lean_dec_ref_known(v___x_932_, 1);
v___y_923_ = v___x_931_;
v_i_924_ = v_index_937_;
goto v___jp_922_;
}
default: 
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_931_, v___x_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_index_940_; 
v_index_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_index_940_);
lean_dec_ref_known(v___x_939_, 1);
v___y_923_ = v___x_931_;
v_i_924_ = v_index_940_;
goto v___jp_922_;
}
else
{
lean_object* v___x_941_; 
lean_dec(v_a_919_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_931_);
return v___x_941_;
}
}
}
}
v___jp_942_:
{
lean_object* v_size_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_size_945_ = lean_ctor_get(v___y_943_, 0);
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_size_945_, v___x_946_);
v___x_948_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_943_, v___x_947_, v_i_944_, v_a_919_, v_b_920_);
lean_dec(v_i_944_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
v___jp_950_:
{
lean_object* v___x_952_; 
lean_inc(v_a_919_);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_917_, v_x_918_, v___y_951_, v_a_919_);
switch(lean_obj_tag(v___x_952_))
{
case 0:
{
lean_object* v_index_953_; lean_object* v_size_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_index_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_index_953_);
lean_dec_ref_known(v___x_952_, 3);
v_size_954_ = lean_ctor_get(v___y_951_, 0);
lean_inc(v_size_954_);
v___x_955_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_951_, v_size_954_, v_index_953_, v_a_919_, v_b_920_);
lean_dec(v_index_953_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
case 1:
{
lean_object* v_index_957_; 
v_index_957_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_index_957_);
lean_dec_ref_known(v___x_952_, 1);
v___y_943_ = v___y_951_;
v_i_944_ = v_index_957_;
goto v___jp_942_;
}
default: 
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_951_, v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_index_960_; 
v_index_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_index_960_);
lean_dec_ref_known(v___x_959_, 1);
v___y_943_ = v___y_951_;
v_i_944_ = v_index_960_;
goto v___jp_942_;
}
else
{
lean_object* v___x_961_; 
lean_dec(v_a_919_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___y_951_);
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg(lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_m_u2081_1001_, lean_object* v_m_u2082_1002_){
_start:
{
lean_object* v_size_1003_; lean_object* v_size_1004_; uint8_t v___x_1005_; 
v_size_1003_ = lean_ctor_get(v_m_u2081_1001_, 0);
v_size_1004_ = lean_ctor_get(v_m_u2082_1002_, 0);
v___x_1005_ = lean_nat_dec_le(v_size_1003_, v_size_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___f_1006_; lean_object* v___x_1007_; 
v___f_1006_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1006_, v_x_999_, v_x_1000_, v_m_u2081_1001_, v_m_u2082_1002_);
return v___x_1007_;
}
else
{
lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1008_, 0, v_x_999_);
lean_closure_set(v___f_1008_, 1, v_x_1000_);
v___x_1009_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v___x_1010_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1009_, v___f_1008_, v_m_u2082_1002_, v_m_u2081_1001_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union(lean_object* v_00_u03b1_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_m_u2081_1016_, lean_object* v_m_u2082_1017_){
_start:
{
lean_object* v_size_1018_; lean_object* v_size_1019_; uint8_t v___x_1020_; 
v_size_1018_ = lean_ctor_get(v_m_u2081_1016_, 0);
v_size_1019_ = lean_ctor_get(v_m_u2082_1017_, 0);
v___x_1020_ = lean_nat_dec_le(v_size_1018_, v_size_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___f_1021_; lean_object* v___x_1022_; 
v___f_1021_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1021_, v_x_1012_, v_x_1013_, v_m_u2081_1016_, v_m_u2082_1017_);
return v___x_1022_;
}
else
{
lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___f_1023_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1023_, 0, v_x_1012_);
lean_closure_set(v___f_1023_, 1, v_x_1013_);
v___x_1024_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v___x_1025_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1024_, v___f_1023_, v_m_u2082_1017_, v_m_u2081_1016_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_1028_, 0, lean_box(0));
lean_closure_set(v___x_1028_, 1, v_x_1026_);
lean_closure_set(v___x_1028_, 2, v_x_1027_);
lean_closure_set(v___x_1028_, 3, lean_box(0));
lean_closure_set(v___x_1028_, 4, lean_box(0));
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_1034_, 0, lean_box(0));
lean_closure_set(v___x_1034_, 1, v_x_1030_);
lean_closure_set(v___x_1034_, 2, v_x_1031_);
lean_closure_set(v___x_1034_, 3, lean_box(0));
lean_closure_set(v___x_1034_, 4, lean_box(0));
return v___x_1034_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___f_1036_; 
v___x_1035_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1036_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1036_, 0, v___x_1035_);
return v___f_1036_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_m_u2081_1039_, lean_object* v_m_u2082_1040_){
_start:
{
lean_object* v___f_1041_; uint8_t v___x_1042_; 
v___f_1041_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1037_, v_x_1038_, v___f_1041_, v_m_u2081_1039_, v_m_u2082_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_m_u2081_1045_, lean_object* v_m_u2082_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_1043_, v_x_1044_, v_m_u2081_1045_, v_m_u2082_1046_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v___f_1051_; 
v___f_1051_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1051_, 0, v_x_1049_);
lean_closure_set(v___f_1051_, 1, v_x_1050_);
return v___f_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v___f_1057_; 
v___f_1057_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1057_, 0, v_x_1053_);
lean_closure_set(v___f_1057_, 1, v_x_1054_);
return v___f_1057_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___f_1062_; uint8_t v___x_1063_; 
v___f_1062_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1058_, v_inst_1059_, v___f_1062_, v_x_1060_, v_x_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_res_1068_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_1064_, v_inst_1065_, v_x_1066_, v_x_1067_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_1071_, v_inst_1073_, v_x_1074_, v_x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(v_00_u03b1_1077_, v_inst_1078_, v_inst_1079_, v_inst_1080_, v_x_1081_, v_x_1082_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter___redArg(lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_m_u2081_1087_, lean_object* v_m_u2082_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1085_, v_x_1086_, v_m_u2081_1087_, v_m_u2082_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter(lean_object* v_00_u03b1_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_m_u2081_1095_, lean_object* v_m_u2082_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1091_, v_x_1092_, v_m_u2081_1095_, v_m_u2082_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_1100_, 0, lean_box(0));
lean_closure_set(v___x_1100_, 1, v_x_1098_);
lean_closure_set(v___x_1100_, 2, v_x_1099_);
lean_closure_set(v___x_1100_, 3, lean_box(0));
lean_closure_set(v___x_1100_, 4, lean_box(0));
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_1106_, 0, lean_box(0));
lean_closure_set(v___x_1106_, 1, v_x_1102_);
lean_closure_set(v___x_1106_, 2, v_x_1103_);
lean_closure_set(v___x_1106_, 3, lean_box(0));
lean_closure_set(v___x_1106_, 4, lean_box(0));
return v___x_1106_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_diff___redArg___lam__0(lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_m_u2082_1109_, uint8_t v___x_1110_, lean_object* v_k_1111_, lean_object* v_x_1112_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1107_, v_x_1108_, v_m_u2082_1109_, v_k_1111_);
if (v___x_1113_ == 0)
{
return v___x_1110_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = 0;
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg___lam__0___boxed(lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_m_u2082_1117_, lean_object* v___x_1118_, lean_object* v_k_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v___x_109__boxed_1121_; uint8_t v_res_1122_; lean_object* v_r_1123_; 
v___x_109__boxed_1121_ = lean_unbox(v___x_1118_);
v_res_1122_ = l_Std_ExtHashSet_diff___redArg___lam__0(v_x_1115_, v_x_1116_, v_m_u2082_1117_, v___x_109__boxed_1121_, v_k_1119_, v_x_1120_);
lean_dec(v_m_u2082_1117_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg(lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_m_u2081_1126_, lean_object* v_m_u2082_1127_){
_start:
{
lean_object* v_size_1128_; lean_object* v_size_1129_; uint8_t v___x_1130_; 
v_size_1128_ = lean_ctor_get(v_m_u2081_1126_, 0);
v_size_1129_ = lean_ctor_get(v_m_u2082_1127_, 0);
v___x_1130_ = lean_nat_dec_le(v_size_1128_, v_size_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___f_1131_; lean_object* v___x_1132_; 
v___f_1131_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1131_, v_x_1124_, v_x_1125_, v_m_u2081_1126_, v_m_u2082_1127_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_box(v___x_1130_);
v___f_1134_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1134_, 0, v_x_1124_);
lean_closure_set(v___f_1134_, 1, v_x_1125_);
lean_closure_set(v___f_1134_, 2, v_m_u2082_1127_);
lean_closure_set(v___f_1134_, 3, v___x_1133_);
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1134_, v_m_u2081_1126_);
lean_dec(v_m_u2081_1126_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff(lean_object* v_00_u03b1_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_m_u2081_1141_, lean_object* v_m_u2082_1142_){
_start:
{
lean_object* v_size_1143_; lean_object* v_size_1144_; uint8_t v___x_1145_; 
v_size_1143_ = lean_ctor_get(v_m_u2081_1141_, 0);
v_size_1144_ = lean_ctor_get(v_m_u2082_1142_, 0);
v___x_1145_ = lean_nat_dec_le(v_size_1143_, v_size_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___f_1146_; lean_object* v___x_1147_; 
v___f_1146_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_1147_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1146_, v_x_1137_, v_x_1138_, v_m_u2081_1141_, v_m_u2082_1142_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_box(v___x_1145_);
v___f_1149_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1149_, 0, v_x_1137_);
lean_closure_set(v___f_1149_, 1, v_x_1138_);
lean_closure_set(v___f_1149_, 2, v_m_u2082_1142_);
lean_closure_set(v___f_1149_, 3, v___x_1148_);
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1149_, v_m_u2081_1141_);
lean_dec(v_m_u2081_1141_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_1153_, 0, lean_box(0));
lean_closure_set(v___x_1153_, 1, v_x_1151_);
lean_closure_set(v___x_1153_, 2, v_x_1152_);
lean_closure_set(v___x_1153_, 3, lean_box(0));
lean_closure_set(v___x_1153_, 4, lean_box(0));
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_1159_, 0, lean_box(0));
lean_closure_set(v___x_1159_, 1, v_x_1155_);
lean_closure_set(v___x_1159_, 2, v_x_1156_);
lean_closure_set(v___x_1159_, 3, lean_box(0));
lean_closure_set(v___x_1159_, 4, lean_box(0));
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray___redArg(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_l_1166_){
_start:
{
lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___f_1167_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_1168_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
v___x_1169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1167_, v_inst_1164_, v_inst_1165_, v___x_1168_, v_l_1166_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray(lean_object* v_00_u03b1_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_l_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1174_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_1175_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__2, &l_Std_ExtHashSet_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__2);
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1174_, v_inst_1171_, v_inst_1172_, v___x_1175_, v_l_1173_);
return v___x_1176_;
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
