// Lean compiler output
// Module: Std.Data.ExtHashMap.Basic
// Imports: public import Std.Data.ExtDHashMap.Basic
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__0 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__1 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__1_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__2 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__2_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__3 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__3_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__4 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__4_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__5 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__5_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__6 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__6_value;
static const lean_ctor_object l_Std_ExtHashMap_ofList___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__0_value),((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__1_value)}};
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__7 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__7_value;
static const lean_ctor_object l_Std_ExtHashMap_ofList___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__7_value),((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__2_value),((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__3_value),((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__4_value),((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__5_value)}};
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__8 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__8_value;
static const lean_ctor_object l_Std_ExtHashMap_ofList___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__8_value),((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__6_value)}};
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__9 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__9_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__10 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__10_value;
static const lean_closure_object l_Std_ExtHashMap_ofList___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__10_value)} };
static const lean_object* l_Std_ExtHashMap_ofList___redArg___closed__11 = (const lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashMap_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtHashMap_union___redArg___closed__0 = (const lean_object*)&l_Std_ExtHashMap_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashMap_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashMap_unitOfArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtHashMap_unitOfArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtHashMap_unitOfArray___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtHashMap_unitOfArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashMap_unitOfArray___redArg___closed__0_value)} };
static const lean_object* l_Std_ExtHashMap_unitOfArray___redArg___closed__1 = (const lean_object*)&l_Std_ExtHashMap_unitOfArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_ExtHashMap_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_capacity_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_unsigned_to_nat(4u);
v___x_20_ = lean_nat_mul(v_capacity_17_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_nat_div(v___x_20_, v___x_21_);
lean_dec(v___x_20_);
v___x_23_ = l_Nat_nextPowerOfTwo(v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_mk_array(v___x_23_, v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_18_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___boxed(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_capacity_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_ExtHashMap_emptyWithCapacity(v_00_u03b1_27_, v_00_u03b2_28_, v_inst_29_, v_inst_30_, v_capacity_31_);
lean_dec(v_capacity_31_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_32_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(0);
v___x_34_ = lean_unsigned_to_nat(16u);
v___x_35_ = lean_mk_array(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__0, &l_Std_ExtHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__0);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_ExtHashMap_instEmptyCollection(v_00_u03b1_44_, v_00_u03b2_45_, v_inst_46_, v_inst_47_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___boxed(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_ExtHashMap_instInhabited(v_00_u03b1_54_, v_00_u03b2_55_, v_inst_56_, v_inst_57_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert___redArg(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_m_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_59_, v_x_60_, v_m_61_, v_a_62_, v_b_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert(lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_m_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_67_, v_x_68_, v_m_71_, v_a_72_, v_b_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_fst_78_; lean_object* v_snd_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_fst_78_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_fst_78_);
v_snd_79_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_snd_79_);
lean_dec_ref(v_x_77_);
v___x_80_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_75_, v_x_76_, v___x_80_, v_fst_78_, v_snd_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___f_84_; 
v___f_84_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_84_, 0, v_x_82_);
lean_closure_set(v___f_84_, 1, v_x_83_);
return v___f_84_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_inst_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v_x_87_);
lean_closure_set(v___f_91_, 1, v_x_88_);
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_fst_96_; lean_object* v_snd_97_; lean_object* v___x_98_; 
v_fst_96_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_fst_96_);
v_snd_97_ = lean_ctor_get(v_x_94_, 1);
lean_inc(v_snd_97_);
lean_dec_ref(v_x_94_);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_92_, v_x_93_, v_x_95_, v_fst_96_, v_snd_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v___f_101_; 
v___f_101_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_101_, 0, v_x_99_);
lean_closure_set(v___f_101_, 1, v_x_100_);
return v___f_101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b2_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_inst_106_, lean_object* v_inst_107_){
_start:
{
lean_object* v___f_108_; 
v___f_108_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_108_, 0, v_x_104_);
lean_closure_set(v___f_108_, 1, v_x_105_);
return v___f_108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew___redArg(lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_m_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_109_, v_x_110_, v_m_111_, v_a_112_, v_b_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_m_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_117_, v_x_118_, v_m_121_, v_a_122_, v_b_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert___redArg(lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_m_127_, lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
lean_object* v_size_130_; lean_object* v_buckets_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_182_; 
v_size_130_ = lean_ctor_get(v_m_127_, 0);
v_buckets_131_ = lean_ctor_get(v_m_127_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_m_127_);
if (v_isSharedCheck_182_ == 0)
{
v___x_133_ = v_m_127_;
v_isShared_134_ = v_isSharedCheck_182_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_buckets_131_);
lean_inc(v_size_130_);
lean_dec(v_m_127_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_182_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v___x_135_ = lean_array_get_size(v_buckets_131_);
lean_inc_ref(v_x_126_);
lean_inc_n(v_a_128_, 2);
v___x_136_ = lean_apply_1(v_x_126_, v_a_128_);
v___x_137_ = 32ULL;
v___x_138_ = lean_unbox_uint64(v___x_136_);
v___x_139_ = lean_uint64_shift_right(v___x_138_, v___x_137_);
v___x_140_ = lean_unbox_uint64(v___x_136_);
lean_dec_ref(v___x_136_);
v_fold_141_ = lean_uint64_xor(v___x_140_, v___x_139_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_135_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_131_, v___x_149_);
lean_inc(v_bkt_150_);
lean_inc_ref(v_x_125_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_125_, v_a_128_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v_size_x27_153_; lean_object* v___x_154_; lean_object* v_buckets_x27_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
lean_dec_ref(v_x_125_);
v___x_152_ = lean_unsigned_to_nat(1u);
v_size_x27_153_ = lean_nat_add(v_size_130_, v___x_152_);
lean_dec(v_size_130_);
lean_inc(v_bkt_150_);
v___x_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_154_, 0, v_a_128_);
lean_ctor_set(v___x_154_, 1, v_b_129_);
lean_ctor_set(v___x_154_, 2, v_bkt_150_);
v_buckets_x27_155_ = lean_array_uset(v_buckets_131_, v___x_149_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_mul(v_size_x27_153_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = lean_nat_div(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_array_get_size(v_buckets_x27_155_);
v___x_161_ = lean_nat_dec_le(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
if (v___x_161_ == 0)
{
lean_object* v_val_162_; lean_object* v___x_164_; 
v_val_162_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_126_, v_buckets_x27_155_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_val_162_);
lean_ctor_set(v___x_133_, 0, v_size_x27_153_);
v___x_164_ = v___x_133_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_val_162_);
v___x_164_ = v_reuseFailAlloc_167_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_box(v___x_151_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
return v___x_166_;
}
}
else
{
lean_object* v___x_169_; 
lean_dec_ref(v_x_126_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_buckets_x27_155_);
lean_ctor_set(v___x_133_, 0, v_size_x27_153_);
v___x_169_ = v___x_133_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_buckets_x27_155_);
v___x_169_ = v_reuseFailAlloc_172_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_box(v___x_151_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
}
else
{
lean_object* v___x_173_; lean_object* v_buckets_x27_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
lean_inc(v_bkt_150_);
lean_dec_ref(v_x_126_);
v___x_173_ = lean_box(0);
v_buckets_x27_174_ = lean_array_uset(v_buckets_131_, v___x_149_, v___x_173_);
v___x_175_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_125_, v_a_128_, v_b_129_, v_bkt_150_);
v___x_176_ = lean_array_uset(v_buckets_x27_174_, v___x_149_, v___x_175_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_176_);
v___x_178_ = v___x_133_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_size_130_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_181_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_box(v___x_151_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_m_189_, lean_object* v_a_190_, lean_object* v_b_191_){
_start:
{
lean_object* v_size_192_; lean_object* v_buckets_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_244_; 
v_size_192_ = lean_ctor_get(v_m_189_, 0);
v_buckets_193_ = lean_ctor_get(v_m_189_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_m_189_);
if (v_isSharedCheck_244_ == 0)
{
v___x_195_ = v_m_189_;
v_isShared_196_ = v_isSharedCheck_244_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_buckets_193_);
lean_inc(v_size_192_);
lean_dec(v_m_189_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_244_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v_fold_203_; uint64_t v___x_204_; uint64_t v___x_205_; uint64_t v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; lean_object* v_bkt_212_; uint8_t v___x_213_; 
v___x_197_ = lean_array_get_size(v_buckets_193_);
lean_inc_ref(v_x_186_);
lean_inc_n(v_a_190_, 2);
v___x_198_ = lean_apply_1(v_x_186_, v_a_190_);
v___x_199_ = 32ULL;
v___x_200_ = lean_unbox_uint64(v___x_198_);
v___x_201_ = lean_uint64_shift_right(v___x_200_, v___x_199_);
v___x_202_ = lean_unbox_uint64(v___x_198_);
lean_dec_ref(v___x_198_);
v_fold_203_ = lean_uint64_xor(v___x_202_, v___x_201_);
v___x_204_ = 16ULL;
v___x_205_ = lean_uint64_shift_right(v_fold_203_, v___x_204_);
v___x_206_ = lean_uint64_xor(v_fold_203_, v___x_205_);
v___x_207_ = lean_uint64_to_usize(v___x_206_);
v___x_208_ = lean_usize_of_nat(v___x_197_);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_sub(v___x_208_, v___x_209_);
v___x_211_ = lean_usize_land(v___x_207_, v___x_210_);
v_bkt_212_ = lean_array_uget_borrowed(v_buckets_193_, v___x_211_);
lean_inc(v_bkt_212_);
lean_inc_ref(v_x_185_);
v___x_213_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_185_, v_a_190_, v_bkt_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v_size_x27_215_; lean_object* v___x_216_; lean_object* v_buckets_x27_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
lean_dec_ref(v_x_185_);
v___x_214_ = lean_unsigned_to_nat(1u);
v_size_x27_215_ = lean_nat_add(v_size_192_, v___x_214_);
lean_dec(v_size_192_);
lean_inc(v_bkt_212_);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v_a_190_);
lean_ctor_set(v___x_216_, 1, v_b_191_);
lean_ctor_set(v___x_216_, 2, v_bkt_212_);
v_buckets_x27_217_ = lean_array_uset(v_buckets_193_, v___x_211_, v___x_216_);
v___x_218_ = lean_unsigned_to_nat(4u);
v___x_219_ = lean_nat_mul(v_size_x27_215_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(3u);
v___x_221_ = lean_nat_div(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_array_get_size(v_buckets_x27_217_);
v___x_223_ = lean_nat_dec_le(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
if (v___x_223_ == 0)
{
lean_object* v_val_224_; lean_object* v___x_226_; 
v_val_224_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_186_, v_buckets_x27_217_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v_val_224_);
lean_ctor_set(v___x_195_, 0, v_size_x27_215_);
v___x_226_ = v___x_195_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_size_x27_215_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_val_224_);
v___x_226_ = v_reuseFailAlloc_229_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_box(v___x_213_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
return v___x_228_;
}
}
else
{
lean_object* v___x_231_; 
lean_dec_ref(v_x_186_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v_buckets_x27_217_);
lean_ctor_set(v___x_195_, 0, v_size_x27_215_);
v___x_231_ = v___x_195_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_size_x27_215_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_buckets_x27_217_);
v___x_231_ = v_reuseFailAlloc_234_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(v___x_213_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
return v___x_233_;
}
}
}
else
{
lean_object* v___x_235_; lean_object* v_buckets_x27_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_inc(v_bkt_212_);
lean_dec_ref(v_x_186_);
v___x_235_ = lean_box(0);
v_buckets_x27_236_ = lean_array_uset(v_buckets_193_, v___x_211_, v___x_235_);
v___x_237_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_185_, v_a_190_, v_b_191_, v_bkt_212_);
v___x_238_ = lean_array_uset(v_buckets_x27_236_, v___x_211_, v___x_237_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___x_238_);
v___x_240_ = v___x_195_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_size_192_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_243_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_box(v___x_213_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_m_247_, lean_object* v_a_248_, lean_object* v_b_249_){
_start:
{
lean_object* v_size_250_; lean_object* v_buckets_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v_fold_258_; uint64_t v___x_259_; uint64_t v___x_260_; uint64_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v_bkt_267_; uint8_t v___x_268_; 
v_size_250_ = lean_ctor_get(v_m_247_, 0);
v_buckets_251_ = lean_ctor_get(v_m_247_, 1);
v___x_252_ = lean_array_get_size(v_buckets_251_);
lean_inc_ref(v_x_246_);
lean_inc_n(v_a_248_, 2);
v___x_253_ = lean_apply_1(v_x_246_, v_a_248_);
v___x_254_ = 32ULL;
v___x_255_ = lean_unbox_uint64(v___x_253_);
v___x_256_ = lean_uint64_shift_right(v___x_255_, v___x_254_);
v___x_257_ = lean_unbox_uint64(v___x_253_);
lean_dec_ref(v___x_253_);
v_fold_258_ = lean_uint64_xor(v___x_257_, v___x_256_);
v___x_259_ = 16ULL;
v___x_260_ = lean_uint64_shift_right(v_fold_258_, v___x_259_);
v___x_261_ = lean_uint64_xor(v_fold_258_, v___x_260_);
v___x_262_ = lean_uint64_to_usize(v___x_261_);
v___x_263_ = lean_usize_of_nat(v___x_252_);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_sub(v___x_263_, v___x_264_);
v___x_266_ = lean_usize_land(v___x_262_, v___x_265_);
v_bkt_267_ = lean_array_uget_borrowed(v_buckets_251_, v___x_266_);
lean_inc(v_bkt_267_);
v___x_268_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_245_, v_a_248_, v_bkt_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_293_; 
lean_inc_ref(v_buckets_251_);
lean_inc(v_size_250_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_m_247_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; 
v_unused_294_ = lean_ctor_get(v_m_247_, 1);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_m_247_, 0);
lean_dec(v_unused_295_);
v___x_270_ = v_m_247_;
v_isShared_271_ = v_isSharedCheck_293_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_m_247_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_293_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v_size_x27_273_; lean_object* v___x_274_; lean_object* v_buckets_x27_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v_size_x27_273_ = lean_nat_add(v_size_250_, v___x_272_);
lean_dec(v_size_250_);
lean_inc(v_bkt_267_);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v_a_248_);
lean_ctor_set(v___x_274_, 1, v_b_249_);
lean_ctor_set(v___x_274_, 2, v_bkt_267_);
v_buckets_x27_275_ = lean_array_uset(v_buckets_251_, v___x_266_, v___x_274_);
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = lean_nat_mul(v_size_x27_273_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(3u);
v___x_279_ = lean_nat_div(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_array_get_size(v_buckets_x27_275_);
v___x_281_ = lean_nat_dec_le(v___x_279_, v___x_280_);
lean_dec(v___x_279_);
if (v___x_281_ == 0)
{
lean_object* v_val_282_; lean_object* v___x_284_; 
v_val_282_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_246_, v_buckets_x27_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v_val_282_);
lean_ctor_set(v___x_270_, 0, v_size_x27_273_);
v___x_284_ = v___x_270_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_size_x27_273_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_val_282_);
v___x_284_ = v_reuseFailAlloc_287_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_box(v___x_268_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
return v___x_286_;
}
}
else
{
lean_object* v___x_289_; 
lean_dec_ref(v_x_246_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v_buckets_x27_275_);
lean_ctor_set(v___x_270_, 0, v_size_x27_273_);
v___x_289_ = v___x_270_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_size_x27_273_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_buckets_x27_275_);
v___x_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(v___x_268_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_289_);
return v___x_291_;
}
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_b_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_x_246_);
v___x_296_ = lean_box(v___x_268_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_m_247_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_m_304_, lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
lean_object* v_size_307_; lean_object* v_buckets_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v_fold_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v_bkt_324_; uint8_t v___x_325_; 
v_size_307_ = lean_ctor_get(v_m_304_, 0);
v_buckets_308_ = lean_ctor_get(v_m_304_, 1);
v___x_309_ = lean_array_get_size(v_buckets_308_);
lean_inc_ref(v_x_301_);
lean_inc_n(v_a_305_, 2);
v___x_310_ = lean_apply_1(v_x_301_, v_a_305_);
v___x_311_ = 32ULL;
v___x_312_ = lean_unbox_uint64(v___x_310_);
v___x_313_ = lean_uint64_shift_right(v___x_312_, v___x_311_);
v___x_314_ = lean_unbox_uint64(v___x_310_);
lean_dec_ref(v___x_310_);
v_fold_315_ = lean_uint64_xor(v___x_314_, v___x_313_);
v___x_316_ = 16ULL;
v___x_317_ = lean_uint64_shift_right(v_fold_315_, v___x_316_);
v___x_318_ = lean_uint64_xor(v_fold_315_, v___x_317_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = lean_usize_of_nat(v___x_309_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_sub(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_land(v___x_319_, v___x_322_);
v_bkt_324_ = lean_array_uget_borrowed(v_buckets_308_, v___x_323_);
lean_inc(v_bkt_324_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_300_, v_a_305_, v_bkt_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_350_; 
lean_inc_ref(v_buckets_308_);
lean_inc(v_size_307_);
v_isSharedCheck_350_ = !lean_is_exclusive(v_m_304_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_351_ = lean_ctor_get(v_m_304_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_m_304_, 0);
lean_dec(v_unused_352_);
v___x_327_ = v_m_304_;
v_isShared_328_ = v_isSharedCheck_350_;
goto v_resetjp_326_;
}
else
{
lean_dec(v_m_304_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_350_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v_size_x27_330_; lean_object* v___x_331_; lean_object* v_buckets_x27_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v_size_x27_330_ = lean_nat_add(v_size_307_, v___x_329_);
lean_dec(v_size_307_);
lean_inc(v_bkt_324_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_a_305_);
lean_ctor_set(v___x_331_, 1, v_b_306_);
lean_ctor_set(v___x_331_, 2, v_bkt_324_);
v_buckets_x27_332_ = lean_array_uset(v_buckets_308_, v___x_323_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_mul(v_size_x27_330_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_div(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_array_get_size(v_buckets_x27_332_);
v___x_338_ = lean_nat_dec_le(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v_val_339_; lean_object* v___x_341_; 
v_val_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_301_, v_buckets_x27_332_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_339_);
lean_ctor_set(v___x_327_, 0, v_size_x27_330_);
v___x_341_ = v___x_327_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_val_339_);
v___x_341_ = v_reuseFailAlloc_344_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_box(v___x_325_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec_ref(v_x_301_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_332_);
lean_ctor_set(v___x_327_, 0, v_size_x27_330_);
v___x_346_ = v___x_327_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_buckets_x27_332_);
v___x_346_ = v_reuseFailAlloc_349_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_box(v___x_325_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_b_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_x_301_);
v___x_353_ = lean_box(v___x_325_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_m_304_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_m_357_, lean_object* v_a_358_, lean_object* v_b_359_){
_start:
{
lean_object* v_size_360_; lean_object* v_buckets_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v_fold_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v_bkt_377_; lean_object* v___x_378_; 
v_size_360_ = lean_ctor_get(v_m_357_, 0);
v_buckets_361_ = lean_ctor_get(v_m_357_, 1);
v___x_362_ = lean_array_get_size(v_buckets_361_);
lean_inc_ref(v_x_356_);
lean_inc_n(v_a_358_, 2);
v___x_363_ = lean_apply_1(v_x_356_, v_a_358_);
v___x_364_ = 32ULL;
v___x_365_ = lean_unbox_uint64(v___x_363_);
v___x_366_ = lean_uint64_shift_right(v___x_365_, v___x_364_);
v___x_367_ = lean_unbox_uint64(v___x_363_);
lean_dec_ref(v___x_363_);
v_fold_368_ = lean_uint64_xor(v___x_367_, v___x_366_);
v___x_369_ = 16ULL;
v___x_370_ = lean_uint64_shift_right(v_fold_368_, v___x_369_);
v___x_371_ = lean_uint64_xor(v_fold_368_, v___x_370_);
v___x_372_ = lean_uint64_to_usize(v___x_371_);
v___x_373_ = lean_usize_of_nat(v___x_362_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_sub(v___x_373_, v___x_374_);
v___x_376_ = lean_usize_land(v___x_372_, v___x_375_);
v_bkt_377_ = lean_array_uget_borrowed(v_buckets_361_, v___x_376_);
lean_inc(v_bkt_377_);
v___x_378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_355_, v_a_358_, v_bkt_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_401_; 
lean_inc_ref(v_buckets_361_);
lean_inc(v_size_360_);
v_isSharedCheck_401_ = !lean_is_exclusive(v_m_357_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; lean_object* v_unused_403_; 
v_unused_402_ = lean_ctor_get(v_m_357_, 1);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_m_357_, 0);
lean_dec(v_unused_403_);
v___x_380_ = v_m_357_;
v_isShared_381_ = v_isSharedCheck_401_;
goto v_resetjp_379_;
}
else
{
lean_dec(v_m_357_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_401_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v_size_x27_383_; lean_object* v___x_384_; lean_object* v_buckets_x27_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v_size_x27_383_ = lean_nat_add(v_size_360_, v___x_382_);
lean_dec(v_size_360_);
lean_inc(v_bkt_377_);
v___x_384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_384_, 0, v_a_358_);
lean_ctor_set(v___x_384_, 1, v_b_359_);
lean_ctor_set(v___x_384_, 2, v_bkt_377_);
v_buckets_x27_385_ = lean_array_uset(v_buckets_361_, v___x_376_, v___x_384_);
v___x_386_ = lean_unsigned_to_nat(4u);
v___x_387_ = lean_nat_mul(v_size_x27_383_, v___x_386_);
v___x_388_ = lean_unsigned_to_nat(3u);
v___x_389_ = lean_nat_div(v___x_387_, v___x_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_array_get_size(v_buckets_x27_385_);
v___x_391_ = lean_nat_dec_le(v___x_389_, v___x_390_);
lean_dec(v___x_389_);
if (v___x_391_ == 0)
{
lean_object* v_val_392_; lean_object* v___x_394_; 
v_val_392_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_356_, v_buckets_x27_385_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_val_392_);
lean_ctor_set(v___x_380_, 0, v_size_x27_383_);
v___x_394_ = v___x_380_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_size_x27_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_val_392_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_378_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
return v___x_395_;
}
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v_x_356_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_buckets_x27_385_);
lean_ctor_set(v___x_380_, 0, v_size_x27_383_);
v___x_398_ = v___x_380_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_size_x27_383_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_buckets_x27_385_);
v___x_398_ = v_reuseFailAlloc_400_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_378_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
}
}
else
{
lean_object* v___x_404_; 
lean_dec(v_b_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_x_356_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_378_);
lean_ctor_set(v___x_404_, 1, v_m_357_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_m_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v_size_414_; lean_object* v_buckets_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v_fold_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v_bkt_431_; lean_object* v___x_432_; 
v_size_414_ = lean_ctor_get(v_m_411_, 0);
v_buckets_415_ = lean_ctor_get(v_m_411_, 1);
v___x_416_ = lean_array_get_size(v_buckets_415_);
lean_inc_ref(v_x_408_);
lean_inc_n(v_a_412_, 2);
v___x_417_ = lean_apply_1(v_x_408_, v_a_412_);
v___x_418_ = 32ULL;
v___x_419_ = lean_unbox_uint64(v___x_417_);
v___x_420_ = lean_uint64_shift_right(v___x_419_, v___x_418_);
v___x_421_ = lean_unbox_uint64(v___x_417_);
lean_dec_ref(v___x_417_);
v_fold_422_ = lean_uint64_xor(v___x_421_, v___x_420_);
v___x_423_ = 16ULL;
v___x_424_ = lean_uint64_shift_right(v_fold_422_, v___x_423_);
v___x_425_ = lean_uint64_xor(v_fold_422_, v___x_424_);
v___x_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = lean_usize_of_nat(v___x_416_);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_sub(v___x_427_, v___x_428_);
v___x_430_ = lean_usize_land(v___x_426_, v___x_429_);
v_bkt_431_ = lean_array_uget_borrowed(v_buckets_415_, v___x_430_);
lean_inc(v_bkt_431_);
v___x_432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_407_, v_a_412_, v_bkt_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_455_; 
lean_inc_ref(v_buckets_415_);
lean_inc(v_size_414_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_m_411_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; 
v_unused_456_ = lean_ctor_get(v_m_411_, 1);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_m_411_, 0);
lean_dec(v_unused_457_);
v___x_434_ = v_m_411_;
v_isShared_435_ = v_isSharedCheck_455_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_m_411_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_455_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v_size_x27_437_; lean_object* v___x_438_; lean_object* v_buckets_x27_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v_size_x27_437_ = lean_nat_add(v_size_414_, v___x_436_);
lean_dec(v_size_414_);
lean_inc(v_bkt_431_);
v___x_438_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_438_, 0, v_a_412_);
lean_ctor_set(v___x_438_, 1, v_b_413_);
lean_ctor_set(v___x_438_, 2, v_bkt_431_);
v_buckets_x27_439_ = lean_array_uset(v_buckets_415_, v___x_430_, v___x_438_);
v___x_440_ = lean_unsigned_to_nat(4u);
v___x_441_ = lean_nat_mul(v_size_x27_437_, v___x_440_);
v___x_442_ = lean_unsigned_to_nat(3u);
v___x_443_ = lean_nat_div(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_array_get_size(v_buckets_x27_439_);
v___x_445_ = lean_nat_dec_le(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v_val_446_; lean_object* v___x_448_; 
v_val_446_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_408_, v_buckets_x27_439_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_val_446_);
lean_ctor_set(v___x_434_, 0, v_size_x27_437_);
v___x_448_ = v___x_434_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_size_x27_437_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_val_446_);
v___x_448_ = v_reuseFailAlloc_450_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; 
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_432_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
return v___x_449_;
}
}
else
{
lean_object* v___x_452_; 
lean_dec_ref(v_x_408_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_buckets_x27_439_);
lean_ctor_set(v___x_434_, 0, v_size_x27_437_);
v___x_452_ = v___x_434_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_buckets_x27_439_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_432_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
}
}
}
else
{
lean_object* v___x_458_; 
lean_dec(v_b_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_x_408_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_432_);
lean_ctor_set(v___x_458_, 1, v_m_411_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg(lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_459_, v_x_460_, v_m_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg___boxed(lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_m_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_ExtHashMap_get_x3f___redArg(v_x_464_, v_x_465_, v_m_466_, v_a_467_);
lean_dec(v_m_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_m_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_471_, v_x_472_, v_m_475_, v_a_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___boxed(lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_ExtHashMap_get_x3f(v_00_u03b1_478_, v_00_u03b2_479_, v_x_480_, v_x_481_, v_inst_482_, v_inst_483_, v_m_484_, v_a_485_);
lean_dec(v_m_484_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains___redArg(lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_m_489_, lean_object* v_a_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_487_, v_x_488_, v_m_489_, v_a_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___redArg___boxed(lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Std_ExtHashMap_contains___redArg(v_x_492_, v_x_493_, v_m_494_, v_a_495_);
lean_dec(v_m_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_m_504_, lean_object* v_a_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_500_, v_x_501_, v_m_504_, v_a_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___boxed(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_m_513_, lean_object* v_a_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Std_ExtHashMap_contains(v_00_u03b1_507_, v_00_u03b2_508_, v_x_509_, v_x_510_, v_inst_511_, v_inst_512_, v_m_513_, v_a_514_);
lean_dec(v_m_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_524_, v_00_u03b2_525_, v_inst_526_, v_inst_527_, v_inst_528_, v_inst_529_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
return v_res_530_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem___redArg(lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_m_533_, lean_object* v_a_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_531_, v_inst_532_, v_m_533_, v_a_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Std_ExtHashMap_instDecidableMem___redArg(v_inst_536_, v_inst_537_, v_m_538_, v_a_539_);
lean_dec(v_m_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_544_, v_inst_545_, v_m_548_, v_a_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_m_557_, lean_object* v_a_558_){
_start:
{
uint8_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = l_Std_ExtHashMap_instDecidableMem(v_00_u03b1_551_, v_00_u03b2_552_, v_inst_553_, v_inst_554_, v_inst_555_, v_inst_556_, v_m_557_, v_a_558_);
lean_dec(v_m_557_);
v_r_560_ = lean_box(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg(lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_m_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_561_, v_x_562_, v_m_563_, v_a_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg___boxed(lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_ExtHashMap_get___redArg(v_x_566_, v_x_567_, v_m_568_, v_a_569_);
lean_dec(v_m_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_m_577_, lean_object* v_a_578_, lean_object* v_h_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_573_, v_x_574_, v_m_577_, v_a_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___boxed(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_m_587_, lean_object* v_a_588_, lean_object* v_h_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_ExtHashMap_get(v_00_u03b1_581_, v_00_u03b2_582_, v_x_583_, v_x_584_, v_inst_585_, v_inst_586_, v_m_587_, v_a_588_, v_h_589_);
lean_dec(v_m_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg(lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_m_593_, lean_object* v_a_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_591_, v_x_592_, v_m_593_, v_a_594_, v_fallback_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg___boxed(lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_m_599_, lean_object* v_a_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_ExtHashMap_getD___redArg(v_x_597_, v_x_598_, v_m_599_, v_a_600_, v_fallback_601_);
lean_dec(v_fallback_601_);
lean_dec(v_m_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_m_609_, lean_object* v_a_610_, lean_object* v_fallback_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_605_, v_x_606_, v_m_609_, v_a_610_, v_fallback_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___boxed(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_m_619_, lean_object* v_a_620_, lean_object* v_fallback_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_ExtHashMap_getD(v_00_u03b1_613_, v_00_u03b2_614_, v_x_615_, v_x_616_, v_inst_617_, v_inst_618_, v_m_619_, v_a_620_, v_fallback_621_);
lean_dec(v_fallback_621_);
lean_dec(v_m_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_inst_625_, lean_object* v_m_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_623_, v_x_624_, v_inst_625_, v_m_626_, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg___boxed(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_inst_631_, lean_object* v_m_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_ExtHashMap_get_x21___redArg(v_x_629_, v_x_630_, v_inst_631_, v_m_632_, v_a_633_);
lean_dec(v_m_632_);
lean_dec(v_inst_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_637_, v_x_638_, v_inst_641_, v_m_642_, v_a_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_m_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_ExtHashMap_get_x21(v_00_u03b1_645_, v_00_u03b2_646_, v_x_647_, v_x_648_, v_inst_649_, v_inst_650_, v_inst_651_, v_m_652_, v_a_653_);
lean_dec(v_m_652_);
lean_dec(v_inst_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_m_657_, lean_object* v_a_658_, lean_object* v_h_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_655_, v_inst_656_, v_m_657_, v_a_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_m_663_, lean_object* v_a_664_, lean_object* v_h_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_661_, v_inst_662_, v_m_663_, v_a_664_, v_h_665_);
lean_dec(v_m_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_m_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_667_, v_inst_668_, v_m_669_, v_a_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_m_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_672_, v_inst_673_, v_m_674_, v_a_675_);
lean_dec(v_m_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_m_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_677_, v_inst_678_, v_inst_679_, v_m_680_, v_a_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_m_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_683_, v_inst_684_, v_inst_685_, v_m_686_, v_a_687_);
lean_dec(v_m_686_);
lean_dec(v_inst_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___f_693_; lean_object* v___x_694_; 
lean_inc_ref_n(v_inst_690_, 2);
lean_inc_ref_n(v_inst_689_, 2);
v___f_691_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_691_, 0, v_inst_689_);
lean_closure_set(v___f_691_, 1, v_inst_690_);
v___f_692_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_692_, 0, v_inst_689_);
lean_closure_set(v___f_692_, 1, v_inst_690_);
v___f_693_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_693_, 0, v_inst_689_);
lean_closure_set(v___f_693_, 1, v_inst_690_);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___f_691_);
lean_ctor_set(v___x_694_, 1, v___f_692_);
lean_ctor_set(v___x_694_, 2, v___f_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg(v_inst_697_, v_inst_698_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_m_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_702_, v_x_703_, v_m_704_, v_a_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_m_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_ExtHashMap_getKey_x3f___redArg(v_x_707_, v_x_708_, v_m_709_, v_a_710_);
lean_dec(v_m_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_m_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_714_, v_x_715_, v_m_718_, v_a_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_ExtHashMap_getKey_x3f(v_00_u03b1_721_, v_00_u03b2_722_, v_x_723_, v_x_724_, v_inst_725_, v_inst_726_, v_m_727_, v_a_728_);
lean_dec(v_m_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg(lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_730_, v_x_731_, v_m_732_, v_a_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg___boxed(lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_m_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_ExtHashMap_getKey___redArg(v_x_735_, v_x_736_, v_m_737_, v_a_738_);
lean_dec(v_m_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_m_746_, lean_object* v_a_747_, lean_object* v_h_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_742_, v_x_743_, v_m_746_, v_a_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___boxed(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_a_757_, lean_object* v_h_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_ExtHashMap_getKey(v_00_u03b1_750_, v_00_u03b2_751_, v_x_752_, v_x_753_, v_inst_754_, v_inst_755_, v_m_756_, v_a_757_, v_h_758_);
lean_dec(v_m_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg(lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_m_762_, lean_object* v_a_763_, lean_object* v_fallback_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_760_, v_x_761_, v_m_762_, v_a_763_, v_fallback_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg___boxed(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_m_768_, lean_object* v_a_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_ExtHashMap_getKeyD___redArg(v_x_766_, v_x_767_, v_m_768_, v_a_769_, v_fallback_770_);
lean_dec(v_fallback_770_);
lean_dec(v_m_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_m_778_, lean_object* v_a_779_, lean_object* v_fallback_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_774_, v_x_775_, v_m_778_, v_a_779_, v_fallback_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___boxed(lean_object* v_00_u03b1_782_, lean_object* v_00_u03b2_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_m_788_, lean_object* v_a_789_, lean_object* v_fallback_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_ExtHashMap_getKeyD(v_00_u03b1_782_, v_00_u03b2_783_, v_x_784_, v_x_785_, v_inst_786_, v_inst_787_, v_m_788_, v_a_789_, v_fallback_790_);
lean_dec(v_fallback_790_);
lean_dec(v_m_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg(lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_inst_794_, lean_object* v_m_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_792_, v_x_793_, v_inst_794_, v_m_795_, v_a_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg___boxed(lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_inst_800_, lean_object* v_m_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_ExtHashMap_getKey_x21___redArg(v_x_798_, v_x_799_, v_inst_800_, v_m_801_, v_a_802_);
lean_dec(v_m_801_);
lean_dec(v_inst_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_m_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_806_, v_x_807_, v_inst_810_, v_m_811_, v_a_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_ExtHashMap_getKey_x21(v_00_u03b1_814_, v_00_u03b2_815_, v_x_816_, v_x_817_, v_inst_818_, v_inst_819_, v_inst_820_, v_m_821_, v_a_822_);
lean_dec(v_m_821_);
lean_dec(v_inst_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase___redArg(lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_m_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_824_, v_x_825_, v_m_826_, v_a_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_m_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_831_, v_x_832_, v_m_835_, v_a_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg(lean_object* v_m_838_){
_start:
{
lean_object* v_size_839_; 
v_size_839_ = lean_ctor_get(v_m_838_, 0);
lean_inc(v_size_839_);
return v_size_839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg___boxed(lean_object* v_m_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_ExtHashMap_size___redArg(v_m_840_);
lean_dec(v_m_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_m_848_){
_start:
{
lean_object* v_size_849_; 
v_size_849_ = lean_ctor_get(v_m_848_, 0);
lean_inc(v_size_849_);
return v_size_849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___boxed(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_m_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_ExtHashMap_size(v_00_u03b1_850_, v_00_u03b2_851_, v_x_852_, v_x_853_, v_inst_854_, v_inst_855_, v_m_856_);
lean_dec(v_m_856_);
lean_dec_ref(v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_857_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty___redArg(lean_object* v_m_858_){
_start:
{
lean_object* v_size_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_size_859_ = lean_ctor_get(v_m_858_, 0);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_nat_dec_eq(v_size_859_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___redArg___boxed(lean_object* v_m_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l_Std_ExtHashMap_isEmpty___redArg(v_m_862_);
lean_dec(v_m_862_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_m_871_){
_start:
{
lean_object* v_size_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_size_872_ = lean_ctor_get(v_m_871_, 0);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_nat_dec_eq(v_size_872_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___boxed(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_m_881_){
_start:
{
uint8_t v_res_882_; lean_object* v_r_883_; 
v_res_882_ = l_Std_ExtHashMap_isEmpty(v_00_u03b1_875_, v_00_u03b2_876_, v_x_877_, v_x_878_, v_inst_879_, v_inst_880_, v_m_881_);
lean_dec(v_m_881_);
lean_dec_ref(v_x_878_);
lean_dec_ref(v_x_877_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList___redArg(lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_l_909_){
_start:
{
lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___f_910_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_911_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_910_, v_inst_907_, v_inst_908_, v___x_911_, v_l_909_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList(lean_object* v_00_u03b1_913_, lean_object* v_00_u03b2_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_l_917_){
_start:
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___f_918_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_919_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_918_, v_inst_915_, v_inst_916_, v___x_919_, v_l_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList___redArg(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_l_923_){
_start:
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___f_924_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_925_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_924_, v_inst_921_, v_inst_922_, v___x_925_, v_l_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList(lean_object* v_00_u03b1_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_l_930_){
_start:
{
lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___f_931_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_932_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_931_, v_inst_928_, v_inst_929_, v___x_932_, v_l_930_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg(lean_object* v_f_934_, lean_object* v_m_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_934_, v_m_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_f_943_, lean_object* v_m_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_943_, v_m_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___boxed(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_f_952_, lean_object* v_m_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_ExtHashMap_filter(v_00_u03b1_946_, v_00_u03b2_947_, v_x_948_, v_x_949_, v_inst_950_, v_inst_951_, v_f_952_, v_m_953_);
lean_dec_ref(v_x_949_);
lean_dec_ref(v_x_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg(lean_object* v_f_955_, lean_object* v_m_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_955_, v_m_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_00_u03b3_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_f_965_, lean_object* v_m_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_965_, v_m_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___boxed(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_00_u03b3_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_f_975_, lean_object* v_m_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_ExtHashMap_map(v_00_u03b1_968_, v_00_u03b2_969_, v_00_u03b3_970_, v_x_971_, v_x_972_, v_inst_973_, v_inst_974_, v_f_975_, v_m_976_);
lean_dec_ref(v_x_972_);
lean_dec_ref(v_x_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg(lean_object* v_f_978_, lean_object* v_m_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_978_, v_m_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap(lean_object* v_00_u03b1_981_, lean_object* v_00_u03b2_982_, lean_object* v_00_u03b3_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_m_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_988_, v_m_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___boxed(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_00_u03b3_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_f_998_, lean_object* v_m_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_ExtHashMap_filterMap(v_00_u03b1_991_, v_00_u03b2_992_, v_00_u03b3_993_, v_x_994_, v_x_995_, v_inst_996_, v_inst_997_, v_f_998_, v_m_999_);
lean_dec_ref(v_x_995_);
lean_dec_ref(v_x_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify___redArg(lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_m_1003_, lean_object* v_a_1004_, lean_object* v_f_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1001_, v_x_1002_, v_m_1003_, v_a_1004_, v_f_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_m_1013_, lean_object* v_a_1014_, lean_object* v_f_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1009_, v_x_1010_, v_m_1013_, v_a_1014_, v_f_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter___redArg(lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_m_1019_, lean_object* v_a_1020_, lean_object* v_f_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1017_, v_x_1018_, v_m_1019_, v_a_1020_, v_f_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter(lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_m_1029_, lean_object* v_a_1030_, lean_object* v_f_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1025_, v_x_1026_, v_m_1029_, v_a_1030_, v_f_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg___lam__0(lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_____s_1036_){
_start:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v_m_1039_; lean_object* v___x_1040_; 
v_fst_1037_ = lean_ctor_get(v_x_1035_, 0);
lean_inc(v_fst_1037_);
v_snd_1038_ = lean_ctor_get(v_x_1035_, 1);
lean_inc(v_snd_1038_);
lean_dec_ref(v_x_1035_);
v_m_1039_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1033_, v_x_1034_, v_____s_1036_, v_fst_1037_, v_snd_1038_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_m_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg(lean_object* v_x_1041_, lean_object* v_x_1042_, lean_object* v_inst_1043_, lean_object* v_m_1044_, lean_object* v_l_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1046_, 0, v_x_1041_);
lean_closure_set(v___f_1046_, 1, v_x_1042_);
v___x_1047_ = lean_apply_4(v_inst_1043_, lean_box(0), v_l_1045_, v_m_1044_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_00_u03c1_1054_, lean_object* v_inst_1055_, lean_object* v_m_1056_, lean_object* v_l_1057_){
_start:
{
lean_object* v___f_1058_; lean_object* v___x_1059_; 
v___f_1058_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1058_, 0, v_x_1050_);
lean_closure_set(v___f_1058_, 1, v_x_1051_);
v___x_1059_ = lean_apply_4(v_inst_1055_, lean_box(0), v_l_1057_, v_m_1056_, v___f_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_a_1062_, lean_object* v_____s_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v_m_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_box(0);
v_m_1065_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1060_, v_x_1061_, v_____s_1063_, v_a_1062_, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_m_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_inst_1069_, lean_object* v_m_1070_, lean_object* v_l_1071_){
_start:
{
lean_object* v___f_1072_; lean_object* v___x_1073_; 
v___f_1072_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1072_, 0, v_x_1067_);
lean_closure_set(v___f_1072_, 1, v_x_1068_);
v___x_1073_ = lean_apply_4(v_inst_1069_, lean_box(0), v_l_1071_, v_m_1070_, v___f_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_00_u03c1_1079_, lean_object* v_inst_1080_, lean_object* v_m_1081_, lean_object* v_l_1082_){
_start:
{
lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___f_1083_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1083_, 0, v_x_1075_);
lean_closure_set(v___f_1083_, 1, v_x_1076_);
v___x_1084_ = lean_apply_4(v_inst_1080_, lean_box(0), v_l_1082_, v_m_1081_, v___f_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__0(lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v_acc_1089_){
_start:
{
lean_object* v_r_1090_; lean_object* v___x_1091_; 
v_r_1090_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1085_, v_x_1086_, v_acc_1089_, v_a_1087_, v_b_1088_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_r_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__1(lean_object* v___x_1092_, lean_object* v___f_1093_, lean_object* v_a_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1092_, v___f_1093_, v_a_1094_, v___y_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg(lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_m_u2081_1102_, lean_object* v_m_u2082_1103_){
_start:
{
lean_object* v_size_1104_; lean_object* v_buckets_1105_; lean_object* v_size_1106_; uint8_t v___x_1107_; 
v_size_1104_ = lean_ctor_get(v_m_u2081_1102_, 0);
v_buckets_1105_ = lean_ctor_get(v_m_u2081_1102_, 1);
v_size_1106_ = lean_ctor_get(v_m_u2082_1103_, 0);
v___x_1107_ = lean_nat_dec_le(v_size_1104_, v_size_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___f_1108_; lean_object* v___x_1109_; 
v___f_1108_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1108_, v_x_1100_, v_x_1101_, v_m_u2081_1102_, v_m_u2082_1103_);
return v___x_1109_;
}
else
{
lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
lean_inc_ref(v_buckets_1105_);
lean_dec(v_m_u2081_1102_);
v___f_1110_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1110_, 0, v_x_1100_);
lean_closure_set(v___f_1110_, 1, v_x_1101_);
v___x_1111_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v___f_1112_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1112_, 0, v___x_1111_);
lean_closure_set(v___f_1112_, 1, v___f_1110_);
v_sz_1113_ = lean_array_size(v_buckets_1105_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1111_, v_buckets_1105_, v___f_1112_, v_sz_1113_, v___x_1114_, v_m_u2082_1103_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_m_u2081_1122_, lean_object* v_m_u2082_1123_){
_start:
{
lean_object* v_size_1124_; lean_object* v_buckets_1125_; lean_object* v_size_1126_; uint8_t v___x_1127_; 
v_size_1124_ = lean_ctor_get(v_m_u2081_1122_, 0);
v_buckets_1125_ = lean_ctor_get(v_m_u2081_1122_, 1);
v_size_1126_ = lean_ctor_get(v_m_u2082_1123_, 0);
v___x_1127_ = lean_nat_dec_le(v_size_1124_, v_size_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___f_1128_; lean_object* v___x_1129_; 
v___f_1128_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1129_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1128_, v_x_1118_, v_x_1119_, v_m_u2081_1122_, v_m_u2082_1123_);
return v___x_1129_;
}
else
{
lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___f_1132_; size_t v_sz_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
lean_inc_ref(v_buckets_1125_);
lean_dec(v_m_u2081_1122_);
v___f_1130_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1130_, 0, v_x_1118_);
lean_closure_set(v___f_1130_, 1, v_x_1119_);
v___x_1131_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v___f_1132_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1132_, 0, v___x_1131_);
lean_closure_set(v___f_1132_, 1, v___f_1130_);
v_sz_1133_ = lean_array_size(v_buckets_1125_);
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1131_, v_buckets_1125_, v___f_1132_, v_sz_1133_, v___x_1134_, v_m_u2082_1123_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_1138_, 0, lean_box(0));
lean_closure_set(v___x_1138_, 1, lean_box(0));
lean_closure_set(v___x_1138_, 2, v_x_1136_);
lean_closure_set(v___x_1138_, 3, v_x_1137_);
lean_closure_set(v___x_1138_, 4, lean_box(0));
lean_closure_set(v___x_1138_, 5, lean_box(0));
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_1145_, 0, lean_box(0));
lean_closure_set(v___x_1145_, 1, lean_box(0));
lean_closure_set(v___x_1145_, 2, v_x_1141_);
lean_closure_set(v___x_1145_, 3, v_x_1142_);
lean_closure_set(v___x_1145_, 4, lean_box(0));
lean_closure_set(v___x_1145_, 5, lean_box(0));
return v___x_1145_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_inst_1148_, lean_object* v_m_u2081_1149_, lean_object* v_m_u2082_1150_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1146_, v_x_1147_, v_inst_1148_, v_m_u2081_1149_, v_m_u2082_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_inst_1154_, lean_object* v_m_u2081_1155_, lean_object* v_m_u2082_1156_){
_start:
{
uint8_t v_res_1157_; lean_object* v_r_1158_; 
v_res_1157_ = l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_1152_, v_x_1153_, v_inst_1154_, v_m_u2081_1155_, v_m_u2082_1156_);
v_r_1158_ = lean_box(v_res_1157_);
return v_r_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v___f_1162_; 
v___f_1162_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1162_, 0, v_x_1159_);
lean_closure_set(v___f_1162_, 1, v_x_1160_);
lean_closure_set(v___f_1162_, 2, v_inst_1161_);
return v___f_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v___f_1170_; 
v___f_1170_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1170_, 0, v_x_1165_);
lean_closure_set(v___f_1170_, 1, v_x_1166_);
lean_closure_set(v___f_1170_, 2, v_inst_1169_);
return v___f_1170_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1171_, v_inst_1172_, v_inst_1173_, v_x_1174_, v_x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1177_, v_inst_1178_, v_inst_1179_, v_x_1180_, v_x_1181_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1186_, v_inst_1188_, v_inst_1189_, v_x_1191_, v_x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
uint8_t v_res_1203_; lean_object* v_r_1204_; 
v_res_1203_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_1194_, v_00_u03b2_1195_, v_inst_1196_, v_inst_1197_, v_inst_1198_, v_inst_1199_, v_inst_1200_, v_x_1201_, v_x_1202_);
v_r_1204_ = lean_box(v_res_1203_);
return v_r_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter___redArg(lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v_m_u2081_1207_, lean_object* v_m_u2082_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1205_, v_x_1206_, v_m_u2081_1207_, v_m_u2082_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_m_u2081_1216_, lean_object* v_m_u2082_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1212_, v_x_1213_, v_m_u2081_1216_, v_m_u2082_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_1221_, 0, lean_box(0));
lean_closure_set(v___x_1221_, 1, lean_box(0));
lean_closure_set(v___x_1221_, 2, v_x_1219_);
lean_closure_set(v___x_1221_, 3, v_x_1220_);
lean_closure_set(v___x_1221_, 4, lean_box(0));
lean_closure_set(v___x_1221_, 5, lean_box(0));
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_1228_, 0, lean_box(0));
lean_closure_set(v___x_1228_, 1, lean_box(0));
lean_closure_set(v___x_1228_, 2, v_x_1224_);
lean_closure_set(v___x_1228_, 3, v_x_1225_);
lean_closure_set(v___x_1228_, 4, lean_box(0));
lean_closure_set(v___x_1228_, 5, lean_box(0));
return v___x_1228_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_diff___redArg___lam__0(lean_object* v_x_1229_, lean_object* v_x_1230_, lean_object* v_m_u2082_1231_, uint8_t v___x_1232_, lean_object* v_k_1233_, lean_object* v_x_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1229_, v_x_1230_, v_m_u2082_1231_, v_k_1233_);
if (v___x_1235_ == 0)
{
return v___x_1232_;
}
else
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_m_u2082_1239_, lean_object* v___x_1240_, lean_object* v_k_1241_, lean_object* v_x_1242_){
_start:
{
uint8_t v___x_106__boxed_1243_; uint8_t v_res_1244_; lean_object* v_r_1245_; 
v___x_106__boxed_1243_ = lean_unbox(v___x_1240_);
v_res_1244_ = l_Std_ExtHashMap_diff___redArg___lam__0(v_x_1237_, v_x_1238_, v_m_u2082_1239_, v___x_106__boxed_1243_, v_k_1241_, v_x_1242_);
lean_dec(v_x_1242_);
lean_dec(v_m_u2082_1239_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_m_u2081_1248_, lean_object* v_m_u2082_1249_){
_start:
{
lean_object* v_size_1250_; lean_object* v_size_1251_; uint8_t v___x_1252_; 
v_size_1250_ = lean_ctor_get(v_m_u2081_1248_, 0);
v_size_1251_ = lean_ctor_get(v_m_u2082_1249_, 0);
v___x_1252_ = lean_nat_dec_le(v_size_1250_, v_size_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___f_1253_; lean_object* v___x_1254_; 
v___f_1253_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1253_, v_x_1246_, v_x_1247_, v_m_u2081_1248_, v_m_u2082_1249_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_box(v___x_1252_);
v___f_1256_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1256_, 0, v_x_1246_);
lean_closure_set(v___f_1256_, 1, v_x_1247_);
lean_closure_set(v___f_1256_, 2, v_m_u2082_1249_);
lean_closure_set(v___f_1256_, 3, v___x_1255_);
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1256_, v_m_u2081_1248_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_m_u2081_1264_, lean_object* v_m_u2082_1265_){
_start:
{
lean_object* v_size_1266_; lean_object* v_size_1267_; uint8_t v___x_1268_; 
v_size_1266_ = lean_ctor_get(v_m_u2081_1264_, 0);
v_size_1267_ = lean_ctor_get(v_m_u2082_1265_, 0);
v___x_1268_ = lean_nat_dec_le(v_size_1266_, v_size_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___f_1269_; lean_object* v___x_1270_; 
v___f_1269_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1269_, v_x_1260_, v_x_1261_, v_m_u2081_1264_, v_m_u2082_1265_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_box(v___x_1268_);
v___f_1272_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1272_, 0, v_x_1260_);
lean_closure_set(v___f_1272_, 1, v_x_1261_);
lean_closure_set(v___f_1272_, 2, v_m_u2082_1265_);
lean_closure_set(v___f_1272_, 3, v___x_1271_);
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1272_, v_m_u2081_1264_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_1276_, 0, lean_box(0));
lean_closure_set(v___x_1276_, 1, lean_box(0));
lean_closure_set(v___x_1276_, 2, v_x_1274_);
lean_closure_set(v___x_1276_, 3, v_x_1275_);
lean_closure_set(v___x_1276_, 4, lean_box(0));
lean_closure_set(v___x_1276_, 5, lean_box(0));
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_1283_, 0, lean_box(0));
lean_closure_set(v___x_1283_, 1, lean_box(0));
lean_closure_set(v___x_1283_, 2, v_x_1279_);
lean_closure_set(v___x_1283_, 3, v_x_1280_);
lean_closure_set(v___x_1283_, 4, lean_box(0));
lean_closure_set(v___x_1283_, 5, lean_box(0));
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray___redArg(lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_l_1290_){
_start:
{
lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___f_1291_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_1292_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_1293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1291_, v_inst_1288_, v_inst_1289_, v___x_1292_, v_l_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray(lean_object* v_00_u03b1_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_l_1297_){
_start:
{
lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___f_1298_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_1299_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1298_, v_inst_1295_, v_inst_1296_, v___x_1299_, v_l_1297_);
return v___x_1300_;
}
}
lean_object* runtime_initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_ExtDHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ExtHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ExtHashMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
