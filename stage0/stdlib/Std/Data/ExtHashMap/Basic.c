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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_ExtHashMap_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(0);
v___x_34_ = lean_unsigned_to_nat(16u);
v___x_35_ = lean_mk_array(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__0, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__0);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_ExtHashMap_instEmptyCollection___redArg();
return v_res_42_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_ExtHashMap_instEmptyCollection___redArg();
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__0, &l_Std_ExtHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_ExtHashMap_instEmptyCollection(v_00_u03b1_49_, v_00_u03b2_50_, v_inst_51_, v_inst_52_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_ExtHashMap_instInhabited___redArg();
return v_res_57_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_ExtHashMap_instInhabited___redArg();
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Std_ExtHashMap_instInhabited___closed__0, &l_Std_ExtHashMap_instInhabited___closed__0_once, _init_l_Std_ExtHashMap_instInhabited___closed__0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___boxed(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_ExtHashMap_instInhabited(v_00_u03b1_64_, v_00_u03b2_65_, v_inst_66_, v_inst_67_);
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_inst_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert___redArg(lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_m_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_69_, v_x_70_, v_m_71_, v_a_72_, v_b_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_x_77_, lean_object* v_x_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_m_81_, lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_77_, v_x_78_, v_m_81_, v_a_82_, v_b_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_fst_88_; lean_object* v_snd_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_fst_88_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_fst_88_);
v_snd_89_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_snd_89_);
lean_dec_ref(v_x_87_);
v___x_90_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_85_, v_x_86_, v___x_90_, v_fst_88_, v_snd_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v___f_94_; 
v___f_94_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_94_, 0, v_x_92_);
lean_closure_set(v___f_94_, 1, v_x_93_);
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_inst_99_, lean_object* v_inst_100_){
_start:
{
lean_object* v___f_101_; 
v___f_101_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_101_, 0, v_x_97_);
lean_closure_set(v___f_101_, 1, v_x_98_);
return v___f_101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_fst_106_; lean_object* v_snd_107_; lean_object* v___x_108_; 
v_fst_106_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_fst_106_);
v_snd_107_ = lean_ctor_get(v_x_104_, 1);
lean_inc(v_snd_107_);
lean_dec_ref(v_x_104_);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_102_, v_x_103_, v_x_105_, v_fst_106_, v_snd_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v___f_111_; 
v___f_111_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_111_, 0, v_x_109_);
lean_closure_set(v___f_111_, 1, v_x_110_);
return v___f_111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_inst_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_118_, 0, v_x_114_);
lean_closure_set(v___f_118_, 1, v_x_115_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew___redArg(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_m_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_119_, v_x_120_, v_m_121_, v_a_122_, v_b_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_m_131_, lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_127_, v_x_128_, v_m_131_, v_a_132_, v_b_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert___redArg(lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_m_137_, lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
lean_object* v_size_140_; lean_object* v_buckets_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_192_; 
v_size_140_ = lean_ctor_get(v_m_137_, 0);
v_buckets_141_ = lean_ctor_get(v_m_137_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_m_137_);
if (v_isSharedCheck_192_ == 0)
{
v___x_143_ = v_m_137_;
v_isShared_144_ = v_isSharedCheck_192_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_buckets_141_);
lean_inc(v_size_140_);
lean_dec(v_m_137_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_192_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v_fold_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; lean_object* v_bkt_160_; uint8_t v___x_161_; 
v___x_145_ = lean_array_get_size(v_buckets_141_);
lean_inc_ref(v_x_136_);
lean_inc_n(v_a_138_, 2);
v___x_146_ = lean_apply_1(v_x_136_, v_a_138_);
v___x_147_ = 32ULL;
v___x_148_ = lean_unbox_uint64(v___x_146_);
v___x_149_ = lean_uint64_shift_right(v___x_148_, v___x_147_);
v___x_150_ = lean_unbox_uint64(v___x_146_);
lean_dec_ref(v___x_146_);
v_fold_151_ = lean_uint64_xor(v___x_150_, v___x_149_);
v___x_152_ = 16ULL;
v___x_153_ = lean_uint64_shift_right(v_fold_151_, v___x_152_);
v___x_154_ = lean_uint64_xor(v_fold_151_, v___x_153_);
v___x_155_ = lean_uint64_to_usize(v___x_154_);
v___x_156_ = lean_usize_of_nat(v___x_145_);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_sub(v___x_156_, v___x_157_);
v___x_159_ = lean_usize_land(v___x_155_, v___x_158_);
v_bkt_160_ = lean_array_uget_borrowed(v_buckets_141_, v___x_159_);
lean_inc(v_bkt_160_);
lean_inc_ref(v_x_135_);
v___x_161_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_135_, v_a_138_, v_bkt_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v_size_x27_163_; lean_object* v___x_164_; lean_object* v_buckets_x27_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
lean_dec_ref(v_x_135_);
v___x_162_ = lean_unsigned_to_nat(1u);
v_size_x27_163_ = lean_nat_add(v_size_140_, v___x_162_);
lean_dec(v_size_140_);
lean_inc(v_bkt_160_);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v_a_138_);
lean_ctor_set(v___x_164_, 1, v_b_139_);
lean_ctor_set(v___x_164_, 2, v_bkt_160_);
v_buckets_x27_165_ = lean_array_uset(v_buckets_141_, v___x_159_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(4u);
v___x_167_ = lean_nat_mul(v_size_x27_163_, v___x_166_);
v___x_168_ = lean_unsigned_to_nat(3u);
v___x_169_ = lean_nat_div(v___x_167_, v___x_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_array_get_size(v_buckets_x27_165_);
v___x_171_ = lean_nat_dec_le(v___x_169_, v___x_170_);
lean_dec(v___x_169_);
if (v___x_171_ == 0)
{
lean_object* v_val_172_; lean_object* v___x_174_; 
v_val_172_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_136_, v_buckets_x27_165_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v_val_172_);
lean_ctor_set(v___x_143_, 0, v_size_x27_163_);
v___x_174_ = v___x_143_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_size_x27_163_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_val_172_);
v___x_174_ = v_reuseFailAlloc_177_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_box(v___x_161_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
return v___x_176_;
}
}
else
{
lean_object* v___x_179_; 
lean_dec_ref(v_x_136_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v_buckets_x27_165_);
lean_ctor_set(v___x_143_, 0, v_size_x27_163_);
v___x_179_ = v___x_143_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_size_x27_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_buckets_x27_165_);
v___x_179_ = v_reuseFailAlloc_182_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(v___x_161_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
return v___x_181_;
}
}
}
else
{
lean_object* v___x_183_; lean_object* v_buckets_x27_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
lean_inc(v_bkt_160_);
lean_dec_ref(v_x_136_);
v___x_183_ = lean_box(0);
v_buckets_x27_184_ = lean_array_uset(v_buckets_141_, v___x_159_, v___x_183_);
v___x_185_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_135_, v_a_138_, v_b_139_, v_bkt_160_);
v___x_186_ = lean_array_uset(v_buckets_x27_184_, v___x_159_, v___x_185_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_186_);
v___x_188_ = v___x_143_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_size_140_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_191_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(v___x_161_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_m_199_, lean_object* v_a_200_, lean_object* v_b_201_){
_start:
{
lean_object* v_size_202_; lean_object* v_buckets_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_254_; 
v_size_202_ = lean_ctor_get(v_m_199_, 0);
v_buckets_203_ = lean_ctor_get(v_m_199_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_m_199_);
if (v_isSharedCheck_254_ == 0)
{
v___x_205_ = v_m_199_;
v_isShared_206_ = v_isSharedCheck_254_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_buckets_203_);
lean_inc(v_size_202_);
lean_dec(v_m_199_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_254_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v_fold_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v_bkt_222_; uint8_t v___x_223_; 
v___x_207_ = lean_array_get_size(v_buckets_203_);
lean_inc_ref(v_x_196_);
lean_inc_n(v_a_200_, 2);
v___x_208_ = lean_apply_1(v_x_196_, v_a_200_);
v___x_209_ = 32ULL;
v___x_210_ = lean_unbox_uint64(v___x_208_);
v___x_211_ = lean_uint64_shift_right(v___x_210_, v___x_209_);
v___x_212_ = lean_unbox_uint64(v___x_208_);
lean_dec_ref(v___x_208_);
v_fold_213_ = lean_uint64_xor(v___x_212_, v___x_211_);
v___x_214_ = 16ULL;
v___x_215_ = lean_uint64_shift_right(v_fold_213_, v___x_214_);
v___x_216_ = lean_uint64_xor(v_fold_213_, v___x_215_);
v___x_217_ = lean_uint64_to_usize(v___x_216_);
v___x_218_ = lean_usize_of_nat(v___x_207_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_sub(v___x_218_, v___x_219_);
v___x_221_ = lean_usize_land(v___x_217_, v___x_220_);
v_bkt_222_ = lean_array_uget_borrowed(v_buckets_203_, v___x_221_);
lean_inc(v_bkt_222_);
lean_inc_ref(v_x_195_);
v___x_223_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_195_, v_a_200_, v_bkt_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v_size_x27_225_; lean_object* v___x_226_; lean_object* v_buckets_x27_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
lean_dec_ref(v_x_195_);
v___x_224_ = lean_unsigned_to_nat(1u);
v_size_x27_225_ = lean_nat_add(v_size_202_, v___x_224_);
lean_dec(v_size_202_);
lean_inc(v_bkt_222_);
v___x_226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_226_, 0, v_a_200_);
lean_ctor_set(v___x_226_, 1, v_b_201_);
lean_ctor_set(v___x_226_, 2, v_bkt_222_);
v_buckets_x27_227_ = lean_array_uset(v_buckets_203_, v___x_221_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(4u);
v___x_229_ = lean_nat_mul(v_size_x27_225_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(3u);
v___x_231_ = lean_nat_div(v___x_229_, v___x_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_array_get_size(v_buckets_x27_227_);
v___x_233_ = lean_nat_dec_le(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
if (v___x_233_ == 0)
{
lean_object* v_val_234_; lean_object* v___x_236_; 
v_val_234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_196_, v_buckets_x27_227_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_val_234_);
lean_ctor_set(v___x_205_, 0, v_size_x27_225_);
v___x_236_ = v___x_205_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_x27_225_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_val_234_);
v___x_236_ = v_reuseFailAlloc_239_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_box(v___x_223_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
return v___x_238_;
}
}
else
{
lean_object* v___x_241_; 
lean_dec_ref(v_x_196_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_buckets_x27_227_);
lean_ctor_set(v___x_205_, 0, v_size_x27_225_);
v___x_241_ = v___x_205_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_size_x27_225_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_buckets_x27_227_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_box(v___x_223_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
}
else
{
lean_object* v___x_245_; lean_object* v_buckets_x27_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
lean_inc(v_bkt_222_);
lean_dec_ref(v_x_196_);
v___x_245_ = lean_box(0);
v_buckets_x27_246_ = lean_array_uset(v_buckets_203_, v___x_221_, v___x_245_);
v___x_247_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_195_, v_a_200_, v_b_201_, v_bkt_222_);
v___x_248_ = lean_array_uset(v_buckets_x27_246_, v___x_221_, v___x_247_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_248_);
v___x_250_ = v___x_205_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_size_202_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_253_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_box(v___x_223_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_m_257_, lean_object* v_a_258_, lean_object* v_b_259_){
_start:
{
lean_object* v_size_260_; lean_object* v_buckets_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint64_t v___x_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v_fold_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; lean_object* v_bkt_277_; uint8_t v___x_278_; 
v_size_260_ = lean_ctor_get(v_m_257_, 0);
v_buckets_261_ = lean_ctor_get(v_m_257_, 1);
v___x_262_ = lean_array_get_size(v_buckets_261_);
lean_inc_ref(v_x_256_);
lean_inc_n(v_a_258_, 2);
v___x_263_ = lean_apply_1(v_x_256_, v_a_258_);
v___x_264_ = 32ULL;
v___x_265_ = lean_unbox_uint64(v___x_263_);
v___x_266_ = lean_uint64_shift_right(v___x_265_, v___x_264_);
v___x_267_ = lean_unbox_uint64(v___x_263_);
lean_dec_ref(v___x_263_);
v_fold_268_ = lean_uint64_xor(v___x_267_, v___x_266_);
v___x_269_ = 16ULL;
v___x_270_ = lean_uint64_shift_right(v_fold_268_, v___x_269_);
v___x_271_ = lean_uint64_xor(v_fold_268_, v___x_270_);
v___x_272_ = lean_uint64_to_usize(v___x_271_);
v___x_273_ = lean_usize_of_nat(v___x_262_);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_sub(v___x_273_, v___x_274_);
v___x_276_ = lean_usize_land(v___x_272_, v___x_275_);
v_bkt_277_ = lean_array_uget_borrowed(v_buckets_261_, v___x_276_);
lean_inc(v_bkt_277_);
v___x_278_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_255_, v_a_258_, v_bkt_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_303_; 
lean_inc_ref(v_buckets_261_);
lean_inc(v_size_260_);
v_isSharedCheck_303_ = !lean_is_exclusive(v_m_257_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_304_ = lean_ctor_get(v_m_257_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_m_257_, 0);
lean_dec(v_unused_305_);
v___x_280_ = v_m_257_;
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
else
{
lean_dec(v_m_257_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v_size_x27_283_; lean_object* v___x_284_; lean_object* v_buckets_x27_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v_size_x27_283_ = lean_nat_add(v_size_260_, v___x_282_);
lean_dec(v_size_260_);
lean_inc(v_bkt_277_);
v___x_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_284_, 0, v_a_258_);
lean_ctor_set(v___x_284_, 1, v_b_259_);
lean_ctor_set(v___x_284_, 2, v_bkt_277_);
v_buckets_x27_285_ = lean_array_uset(v_buckets_261_, v___x_276_, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(4u);
v___x_287_ = lean_nat_mul(v_size_x27_283_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(3u);
v___x_289_ = lean_nat_div(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_array_get_size(v_buckets_x27_285_);
v___x_291_ = lean_nat_dec_le(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
if (v___x_291_ == 0)
{
lean_object* v_val_292_; lean_object* v___x_294_; 
v_val_292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_256_, v_buckets_x27_285_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v_val_292_);
lean_ctor_set(v___x_280_, 0, v_size_x27_283_);
v___x_294_ = v___x_280_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_size_x27_283_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_val_292_);
v___x_294_ = v_reuseFailAlloc_297_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(v___x_278_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
return v___x_296_;
}
}
else
{
lean_object* v___x_299_; 
lean_dec_ref(v_x_256_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v_buckets_x27_285_);
lean_ctor_set(v___x_280_, 0, v_size_x27_283_);
v___x_299_ = v___x_280_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_size_x27_283_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_buckets_x27_285_);
v___x_299_ = v_reuseFailAlloc_302_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(v___x_278_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
return v___x_301_;
}
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_b_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_x_256_);
v___x_306_ = lean_box(v___x_278_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_m_257_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_m_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v_size_317_; lean_object* v_buckets_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v_fold_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v_bkt_334_; uint8_t v___x_335_; 
v_size_317_ = lean_ctor_get(v_m_314_, 0);
v_buckets_318_ = lean_ctor_get(v_m_314_, 1);
v___x_319_ = lean_array_get_size(v_buckets_318_);
lean_inc_ref(v_x_311_);
lean_inc_n(v_a_315_, 2);
v___x_320_ = lean_apply_1(v_x_311_, v_a_315_);
v___x_321_ = 32ULL;
v___x_322_ = lean_unbox_uint64(v___x_320_);
v___x_323_ = lean_uint64_shift_right(v___x_322_, v___x_321_);
v___x_324_ = lean_unbox_uint64(v___x_320_);
lean_dec_ref(v___x_320_);
v_fold_325_ = lean_uint64_xor(v___x_324_, v___x_323_);
v___x_326_ = 16ULL;
v___x_327_ = lean_uint64_shift_right(v_fold_325_, v___x_326_);
v___x_328_ = lean_uint64_xor(v_fold_325_, v___x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = lean_usize_of_nat(v___x_319_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_land(v___x_329_, v___x_332_);
v_bkt_334_ = lean_array_uget_borrowed(v_buckets_318_, v___x_333_);
lean_inc(v_bkt_334_);
v___x_335_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_310_, v_a_315_, v_bkt_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_360_; 
lean_inc_ref(v_buckets_318_);
lean_inc(v_size_317_);
v_isSharedCheck_360_ = !lean_is_exclusive(v_m_314_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_361_ = lean_ctor_get(v_m_314_, 1);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_m_314_, 0);
lean_dec(v_unused_362_);
v___x_337_ = v_m_314_;
v_isShared_338_ = v_isSharedCheck_360_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_m_314_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_360_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v_size_x27_340_; lean_object* v___x_341_; lean_object* v_buckets_x27_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v_size_x27_340_ = lean_nat_add(v_size_317_, v___x_339_);
lean_dec(v_size_317_);
lean_inc(v_bkt_334_);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v_a_315_);
lean_ctor_set(v___x_341_, 1, v_b_316_);
lean_ctor_set(v___x_341_, 2, v_bkt_334_);
v_buckets_x27_342_ = lean_array_uset(v_buckets_318_, v___x_333_, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(4u);
v___x_344_ = lean_nat_mul(v_size_x27_340_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(3u);
v___x_346_ = lean_nat_div(v___x_344_, v___x_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_array_get_size(v_buckets_x27_342_);
v___x_348_ = lean_nat_dec_le(v___x_346_, v___x_347_);
lean_dec(v___x_346_);
if (v___x_348_ == 0)
{
lean_object* v_val_349_; lean_object* v___x_351_; 
v_val_349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_311_, v_buckets_x27_342_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_val_349_);
lean_ctor_set(v___x_337_, 0, v_size_x27_340_);
v___x_351_ = v___x_337_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_size_x27_340_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_val_349_);
v___x_351_ = v_reuseFailAlloc_354_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_box(v___x_335_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
return v___x_353_;
}
}
else
{
lean_object* v___x_356_; 
lean_dec_ref(v_x_311_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_buckets_x27_342_);
lean_ctor_set(v___x_337_, 0, v_size_x27_340_);
v___x_356_ = v___x_337_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_size_x27_340_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_buckets_x27_342_);
v___x_356_ = v_reuseFailAlloc_359_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_box(v___x_335_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_b_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_x_311_);
v___x_363_ = lean_box(v___x_335_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_m_314_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_m_367_, lean_object* v_a_368_, lean_object* v_b_369_){
_start:
{
lean_object* v_size_370_; lean_object* v_buckets_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v_fold_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v_bkt_387_; lean_object* v___x_388_; 
v_size_370_ = lean_ctor_get(v_m_367_, 0);
v_buckets_371_ = lean_ctor_get(v_m_367_, 1);
v___x_372_ = lean_array_get_size(v_buckets_371_);
lean_inc_ref(v_x_366_);
lean_inc_n(v_a_368_, 2);
v___x_373_ = lean_apply_1(v_x_366_, v_a_368_);
v___x_374_ = 32ULL;
v___x_375_ = lean_unbox_uint64(v___x_373_);
v___x_376_ = lean_uint64_shift_right(v___x_375_, v___x_374_);
v___x_377_ = lean_unbox_uint64(v___x_373_);
lean_dec_ref(v___x_373_);
v_fold_378_ = lean_uint64_xor(v___x_377_, v___x_376_);
v___x_379_ = 16ULL;
v___x_380_ = lean_uint64_shift_right(v_fold_378_, v___x_379_);
v___x_381_ = lean_uint64_xor(v_fold_378_, v___x_380_);
v___x_382_ = lean_uint64_to_usize(v___x_381_);
v___x_383_ = lean_usize_of_nat(v___x_372_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_sub(v___x_383_, v___x_384_);
v___x_386_ = lean_usize_land(v___x_382_, v___x_385_);
v_bkt_387_ = lean_array_uget_borrowed(v_buckets_371_, v___x_386_);
lean_inc(v_bkt_387_);
v___x_388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_365_, v_a_368_, v_bkt_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_411_; 
lean_inc_ref(v_buckets_371_);
lean_inc(v_size_370_);
v_isSharedCheck_411_ = !lean_is_exclusive(v_m_367_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_412_ = lean_ctor_get(v_m_367_, 1);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_m_367_, 0);
lean_dec(v_unused_413_);
v___x_390_ = v_m_367_;
v_isShared_391_ = v_isSharedCheck_411_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_m_367_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_411_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v_size_x27_393_; lean_object* v___x_394_; lean_object* v_buckets_x27_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v_size_x27_393_ = lean_nat_add(v_size_370_, v___x_392_);
lean_dec(v_size_370_);
lean_inc(v_bkt_387_);
v___x_394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_394_, 0, v_a_368_);
lean_ctor_set(v___x_394_, 1, v_b_369_);
lean_ctor_set(v___x_394_, 2, v_bkt_387_);
v_buckets_x27_395_ = lean_array_uset(v_buckets_371_, v___x_386_, v___x_394_);
v___x_396_ = lean_unsigned_to_nat(4u);
v___x_397_ = lean_nat_mul(v_size_x27_393_, v___x_396_);
v___x_398_ = lean_unsigned_to_nat(3u);
v___x_399_ = lean_nat_div(v___x_397_, v___x_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_array_get_size(v_buckets_x27_395_);
v___x_401_ = lean_nat_dec_le(v___x_399_, v___x_400_);
lean_dec(v___x_399_);
if (v___x_401_ == 0)
{
lean_object* v_val_402_; lean_object* v___x_404_; 
v_val_402_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_366_, v_buckets_x27_395_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_val_402_);
lean_ctor_set(v___x_390_, 0, v_size_x27_393_);
v___x_404_ = v___x_390_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_size_x27_393_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_val_402_);
v___x_404_ = v_reuseFailAlloc_406_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_388_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
return v___x_405_;
}
}
else
{
lean_object* v___x_408_; 
lean_dec_ref(v_x_366_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_buckets_x27_395_);
lean_ctor_set(v___x_390_, 0, v_size_x27_393_);
v___x_408_ = v___x_390_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_size_x27_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_buckets_x27_395_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_388_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
}
}
}
else
{
lean_object* v___x_414_; 
lean_dec(v_b_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_x_366_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_388_);
lean_ctor_set(v___x_414_, 1, v_m_367_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_b_423_){
_start:
{
lean_object* v_size_424_; lean_object* v_buckets_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v_fold_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v_bkt_441_; lean_object* v___x_442_; 
v_size_424_ = lean_ctor_get(v_m_421_, 0);
v_buckets_425_ = lean_ctor_get(v_m_421_, 1);
v___x_426_ = lean_array_get_size(v_buckets_425_);
lean_inc_ref(v_x_418_);
lean_inc_n(v_a_422_, 2);
v___x_427_ = lean_apply_1(v_x_418_, v_a_422_);
v___x_428_ = 32ULL;
v___x_429_ = lean_unbox_uint64(v___x_427_);
v___x_430_ = lean_uint64_shift_right(v___x_429_, v___x_428_);
v___x_431_ = lean_unbox_uint64(v___x_427_);
lean_dec_ref(v___x_427_);
v_fold_432_ = lean_uint64_xor(v___x_431_, v___x_430_);
v___x_433_ = 16ULL;
v___x_434_ = lean_uint64_shift_right(v_fold_432_, v___x_433_);
v___x_435_ = lean_uint64_xor(v_fold_432_, v___x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = lean_usize_of_nat(v___x_426_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_usize_land(v___x_436_, v___x_439_);
v_bkt_441_ = lean_array_uget_borrowed(v_buckets_425_, v___x_440_);
lean_inc(v_bkt_441_);
v___x_442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_417_, v_a_422_, v_bkt_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_465_; 
lean_inc_ref(v_buckets_425_);
lean_inc(v_size_424_);
v_isSharedCheck_465_ = !lean_is_exclusive(v_m_421_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_466_ = lean_ctor_get(v_m_421_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_m_421_, 0);
lean_dec(v_unused_467_);
v___x_444_ = v_m_421_;
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
else
{
lean_dec(v_m_421_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v_size_x27_447_; lean_object* v___x_448_; lean_object* v_buckets_x27_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v_size_x27_447_ = lean_nat_add(v_size_424_, v___x_446_);
lean_dec(v_size_424_);
lean_inc(v_bkt_441_);
v___x_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_448_, 0, v_a_422_);
lean_ctor_set(v___x_448_, 1, v_b_423_);
lean_ctor_set(v___x_448_, 2, v_bkt_441_);
v_buckets_x27_449_ = lean_array_uset(v_buckets_425_, v___x_440_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(4u);
v___x_451_ = lean_nat_mul(v_size_x27_447_, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = lean_nat_div(v___x_451_, v___x_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_array_get_size(v_buckets_x27_449_);
v___x_455_ = lean_nat_dec_le(v___x_453_, v___x_454_);
lean_dec(v___x_453_);
if (v___x_455_ == 0)
{
lean_object* v_val_456_; lean_object* v___x_458_; 
v_val_456_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_418_, v_buckets_x27_449_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_val_456_);
lean_ctor_set(v___x_444_, 0, v_size_x27_447_);
v___x_458_ = v___x_444_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_size_x27_447_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_val_456_);
v___x_458_ = v_reuseFailAlloc_460_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_442_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
}
else
{
lean_object* v___x_462_; 
lean_dec_ref(v_x_418_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_buckets_x27_449_);
lean_ctor_set(v___x_444_, 0, v_size_x27_447_);
v___x_462_ = v___x_444_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_size_x27_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_buckets_x27_449_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_442_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_b_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_x_418_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_442_);
lean_ctor_set(v___x_468_, 1, v_m_421_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg(lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_m_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_469_, v_x_470_, v_m_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg___boxed(lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_m_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_ExtHashMap_get_x3f___redArg(v_x_474_, v_x_475_, v_m_476_, v_a_477_);
lean_dec(v_m_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f(lean_object* v_00_u03b1_479_, lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_m_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_481_, v_x_482_, v_m_485_, v_a_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___boxed(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_ExtHashMap_get_x3f(v_00_u03b1_488_, v_00_u03b2_489_, v_x_490_, v_x_491_, v_inst_492_, v_inst_493_, v_m_494_, v_a_495_);
lean_dec(v_m_494_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains___redArg(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_m_499_, lean_object* v_a_500_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_497_, v_x_498_, v_m_499_, v_a_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___redArg___boxed(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_m_504_, lean_object* v_a_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_Std_ExtHashMap_contains___redArg(v_x_502_, v_x_503_, v_m_504_, v_a_505_);
lean_dec(v_m_504_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_m_514_, lean_object* v_a_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_510_, v_x_511_, v_m_514_, v_a_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___boxed(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_m_523_, lean_object* v_a_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Std_ExtHashMap_contains(v_00_u03b1_517_, v_00_u03b2_518_, v_x_519_, v_x_520_, v_inst_521_, v_inst_522_, v_m_523_, v_a_524_);
lean_dec(v_m_523_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg(){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object* v___dummy_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_531_, lean_object* v_00_u03b2_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_538_, v_00_u03b2_539_, v_inst_540_, v_inst_541_, v_inst_542_, v_inst_543_);
lean_dec_ref(v_inst_541_);
lean_dec_ref(v_inst_540_);
return v_res_544_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem___redArg(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_m_547_, lean_object* v_a_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_545_, v_inst_546_, v_m_547_, v_a_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_m_552_, lean_object* v_a_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Std_ExtHashMap_instDecidableMem___redArg(v_inst_550_, v_inst_551_, v_m_552_, v_a_553_);
lean_dec(v_m_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_m_562_, lean_object* v_a_563_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_558_, v_inst_559_, v_m_562_, v_a_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_565_, lean_object* v_00_u03b2_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Std_ExtHashMap_instDecidableMem(v_00_u03b1_565_, v_00_u03b2_566_, v_inst_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_m_571_, v_a_572_);
lean_dec(v_m_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg(lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_m_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_575_, v_x_576_, v_m_577_, v_a_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg___boxed(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_m_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_ExtHashMap_get___redArg(v_x_580_, v_x_581_, v_m_582_, v_a_583_);
lean_dec(v_m_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_m_591_, lean_object* v_a_592_, lean_object* v_h_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_587_, v_x_588_, v_m_591_, v_a_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___boxed(lean_object* v_00_u03b1_595_, lean_object* v_00_u03b2_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_m_601_, lean_object* v_a_602_, lean_object* v_h_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_ExtHashMap_get(v_00_u03b1_595_, v_00_u03b2_596_, v_x_597_, v_x_598_, v_inst_599_, v_inst_600_, v_m_601_, v_a_602_, v_h_603_);
lean_dec(v_m_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg(lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_m_607_, lean_object* v_a_608_, lean_object* v_fallback_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_605_, v_x_606_, v_m_607_, v_a_608_, v_fallback_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg___boxed(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_m_613_, lean_object* v_a_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_ExtHashMap_getD___redArg(v_x_611_, v_x_612_, v_m_613_, v_a_614_, v_fallback_615_);
lean_dec(v_fallback_615_);
lean_dec(v_m_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_m_623_, lean_object* v_a_624_, lean_object* v_fallback_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_619_, v_x_620_, v_m_623_, v_a_624_, v_fallback_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___boxed(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_m_633_, lean_object* v_a_634_, lean_object* v_fallback_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_ExtHashMap_getD(v_00_u03b1_627_, v_00_u03b2_628_, v_x_629_, v_x_630_, v_inst_631_, v_inst_632_, v_m_633_, v_a_634_, v_fallback_635_);
lean_dec(v_fallback_635_);
lean_dec(v_m_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_inst_639_, lean_object* v_m_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_637_, v_x_638_, v_inst_639_, v_m_640_, v_a_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg___boxed(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_inst_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_ExtHashMap_get_x21___redArg(v_x_643_, v_x_644_, v_inst_645_, v_m_646_, v_a_647_);
lean_dec(v_m_646_);
lean_dec(v_inst_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_m_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_651_, v_x_652_, v_inst_655_, v_m_656_, v_a_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___boxed(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_m_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_ExtHashMap_get_x21(v_00_u03b1_659_, v_00_u03b2_660_, v_x_661_, v_x_662_, v_inst_663_, v_inst_664_, v_inst_665_, v_m_666_, v_a_667_);
lean_dec(v_m_666_);
lean_dec(v_inst_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_m_671_, lean_object* v_a_672_, lean_object* v_h_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_669_, v_inst_670_, v_m_671_, v_a_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_m_677_, lean_object* v_a_678_, lean_object* v_h_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_675_, v_inst_676_, v_m_677_, v_a_678_, v_h_679_);
lean_dec(v_m_677_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_m_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_681_, v_inst_682_, v_m_683_, v_a_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_m_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_686_, v_inst_687_, v_m_688_, v_a_689_);
lean_dec(v_m_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_m_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_691_, v_inst_692_, v_inst_693_, v_m_694_, v_a_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_m_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_697_, v_inst_698_, v_inst_699_, v_m_700_, v_a_701_);
lean_dec(v_m_700_);
lean_dec(v_inst_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___x_708_; 
lean_inc_ref_n(v_inst_704_, 2);
lean_inc_ref_n(v_inst_703_, 2);
v___f_705_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_705_, 0, v_inst_703_);
lean_closure_set(v___f_705_, 1, v_inst_704_);
v___f_706_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_706_, 0, v_inst_703_);
lean_closure_set(v___f_706_, 1, v_inst_704_);
v___f_707_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_707_, 0, v_inst_703_);
lean_closure_set(v___f_707_, 1, v_inst_704_);
v___x_708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_708_, 0, v___f_705_);
lean_ctor_set(v___x_708_, 1, v___f_706_);
lean_ctor_set(v___x_708_, 2, v___f_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg(v_inst_711_, v_inst_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_m_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_716_, v_x_717_, v_m_718_, v_a_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_ExtHashMap_getKey_x3f___redArg(v_x_721_, v_x_722_, v_m_723_, v_a_724_);
lean_dec(v_m_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_728_, v_x_729_, v_m_732_, v_a_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_m_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_ExtHashMap_getKey_x3f(v_00_u03b1_735_, v_00_u03b2_736_, v_x_737_, v_x_738_, v_inst_739_, v_inst_740_, v_m_741_, v_a_742_);
lean_dec(v_m_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg(lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_744_, v_x_745_, v_m_746_, v_a_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg___boxed(lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_m_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_ExtHashMap_getKey___redArg(v_x_749_, v_x_750_, v_m_751_, v_a_752_);
lean_dec(v_m_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_, lean_object* v_h_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_756_, v_x_757_, v_m_760_, v_a_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___boxed(lean_object* v_00_u03b1_764_, lean_object* v_00_u03b2_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_m_770_, lean_object* v_a_771_, lean_object* v_h_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_ExtHashMap_getKey(v_00_u03b1_764_, v_00_u03b2_765_, v_x_766_, v_x_767_, v_inst_768_, v_inst_769_, v_m_770_, v_a_771_, v_h_772_);
lean_dec(v_m_770_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg(lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_fallback_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_774_, v_x_775_, v_m_776_, v_a_777_, v_fallback_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg___boxed(lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_m_782_, lean_object* v_a_783_, lean_object* v_fallback_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_ExtHashMap_getKeyD___redArg(v_x_780_, v_x_781_, v_m_782_, v_a_783_, v_fallback_784_);
lean_dec(v_fallback_784_);
lean_dec(v_m_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_m_792_, lean_object* v_a_793_, lean_object* v_fallback_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_788_, v_x_789_, v_m_792_, v_a_793_, v_fallback_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___boxed(lean_object* v_00_u03b1_796_, lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_m_802_, lean_object* v_a_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_ExtHashMap_getKeyD(v_00_u03b1_796_, v_00_u03b2_797_, v_x_798_, v_x_799_, v_inst_800_, v_inst_801_, v_m_802_, v_a_803_, v_fallback_804_);
lean_dec(v_fallback_804_);
lean_dec(v_m_802_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg(lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_inst_808_, lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_806_, v_x_807_, v_inst_808_, v_m_809_, v_a_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg___boxed(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_inst_814_, lean_object* v_m_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_ExtHashMap_getKey_x21___redArg(v_x_812_, v_x_813_, v_inst_814_, v_m_815_, v_a_816_);
lean_dec(v_m_815_);
lean_dec(v_inst_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_820_, v_x_821_, v_inst_824_, v_m_825_, v_a_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_m_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_ExtHashMap_getKey_x21(v_00_u03b1_828_, v_00_u03b2_829_, v_x_830_, v_x_831_, v_inst_832_, v_inst_833_, v_inst_834_, v_m_835_, v_a_836_);
lean_dec(v_m_835_);
lean_dec(v_inst_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase___redArg(lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_838_, v_x_839_, v_m_840_, v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_m_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_845_, v_x_846_, v_m_849_, v_a_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg(lean_object* v_m_852_){
_start:
{
lean_object* v_size_853_; 
v_size_853_ = lean_ctor_get(v_m_852_, 0);
lean_inc(v_size_853_);
return v_size_853_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg___boxed(lean_object* v_m_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_ExtHashMap_size___redArg(v_m_854_);
lean_dec(v_m_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_m_862_){
_start:
{
lean_object* v_size_863_; 
v_size_863_ = lean_ctor_get(v_m_862_, 0);
lean_inc(v_size_863_);
return v_size_863_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___boxed(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_m_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_ExtHashMap_size(v_00_u03b1_864_, v_00_u03b2_865_, v_x_866_, v_x_867_, v_inst_868_, v_inst_869_, v_m_870_);
lean_dec(v_m_870_);
lean_dec_ref(v_x_867_);
lean_dec_ref(v_x_866_);
return v_res_871_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty___redArg(lean_object* v_m_872_){
_start:
{
lean_object* v_size_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_size_873_ = lean_ctor_get(v_m_872_, 0);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_nat_dec_eq(v_size_873_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___redArg___boxed(lean_object* v_m_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Std_ExtHashMap_isEmpty___redArg(v_m_876_);
lean_dec(v_m_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_m_885_){
_start:
{
lean_object* v_size_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_size_886_ = lean_ctor_get(v_m_885_, 0);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_nat_dec_eq(v_size_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___boxed(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_m_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Std_ExtHashMap_isEmpty(v_00_u03b1_889_, v_00_u03b2_890_, v_x_891_, v_x_892_, v_inst_893_, v_inst_894_, v_m_895_);
lean_dec(v_m_895_);
lean_dec_ref(v_x_892_);
lean_dec_ref(v_x_891_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList___redArg(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_l_923_){
_start:
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___f_924_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_925_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_924_, v_inst_921_, v_inst_922_, v___x_925_, v_l_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_l_931_){
_start:
{
lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___f_932_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_933_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_932_, v_inst_929_, v_inst_930_, v___x_933_, v_l_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList___redArg(lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_l_937_){
_start:
{
lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___f_938_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_939_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_938_, v_inst_935_, v_inst_936_, v___x_939_, v_l_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList(lean_object* v_00_u03b1_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_l_944_){
_start:
{
lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___f_945_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_946_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_945_, v_inst_942_, v_inst_943_, v___x_946_, v_l_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg(lean_object* v_f_948_, lean_object* v_m_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_948_, v_m_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter(lean_object* v_00_u03b1_951_, lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_f_957_, lean_object* v_m_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_957_, v_m_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___boxed(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_f_966_, lean_object* v_m_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_ExtHashMap_filter(v_00_u03b1_960_, v_00_u03b2_961_, v_x_962_, v_x_963_, v_inst_964_, v_inst_965_, v_f_966_, v_m_967_);
lean_dec_ref(v_x_963_);
lean_dec_ref(v_x_962_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg(lean_object* v_f_969_, lean_object* v_m_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_969_, v_m_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_00_u03b3_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_f_979_, lean_object* v_m_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_979_, v_m_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___boxed(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b2_983_, lean_object* v_00_u03b3_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_f_989_, lean_object* v_m_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std_ExtHashMap_map(v_00_u03b1_982_, v_00_u03b2_983_, v_00_u03b3_984_, v_x_985_, v_x_986_, v_inst_987_, v_inst_988_, v_f_989_, v_m_990_);
lean_dec_ref(v_x_986_);
lean_dec_ref(v_x_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg(lean_object* v_f_992_, lean_object* v_m_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_992_, v_m_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_00_u03b3_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_f_1002_, lean_object* v_m_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1002_, v_m_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_00_u03b3_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_f_1012_, lean_object* v_m_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_ExtHashMap_filterMap(v_00_u03b1_1005_, v_00_u03b2_1006_, v_00_u03b3_1007_, v_x_1008_, v_x_1009_, v_inst_1010_, v_inst_1011_, v_f_1012_, v_m_1013_);
lean_dec_ref(v_x_1009_);
lean_dec_ref(v_x_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify___redArg(lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_m_1017_, lean_object* v_a_1018_, lean_object* v_f_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1015_, v_x_1016_, v_m_1017_, v_a_1018_, v_f_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify(lean_object* v_00_u03b1_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_m_1027_, lean_object* v_a_1028_, lean_object* v_f_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1023_, v_x_1024_, v_m_1027_, v_a_1028_, v_f_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter___redArg(lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_m_1033_, lean_object* v_a_1034_, lean_object* v_f_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1031_, v_x_1032_, v_m_1033_, v_a_1034_, v_f_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter(lean_object* v_00_u03b1_1037_, lean_object* v_00_u03b2_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_m_1043_, lean_object* v_a_1044_, lean_object* v_f_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1039_, v_x_1040_, v_m_1043_, v_a_1044_, v_f_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg___lam__0(lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_____s_1050_){
_start:
{
lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v_m_1053_; lean_object* v___x_1054_; 
v_fst_1051_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_fst_1051_);
v_snd_1052_ = lean_ctor_get(v_x_1049_, 1);
lean_inc(v_snd_1052_);
lean_dec_ref(v_x_1049_);
v_m_1053_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1047_, v_x_1048_, v_____s_1050_, v_fst_1051_, v_snd_1052_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_m_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg(lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_inst_1057_, lean_object* v_m_1058_, lean_object* v_l_1059_){
_start:
{
lean_object* v___f_1060_; lean_object* v___x_1061_; 
v___f_1060_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1060_, 0, v_x_1055_);
lean_closure_set(v___f_1060_, 1, v_x_1056_);
v___x_1061_ = lean_apply_4(v_inst_1057_, lean_box(0), v_l_1059_, v_m_1058_, v___f_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany(lean_object* v_00_u03b1_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_00_u03c1_1068_, lean_object* v_inst_1069_, lean_object* v_m_1070_, lean_object* v_l_1071_){
_start:
{
lean_object* v___f_1072_; lean_object* v___x_1073_; 
v___f_1072_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1072_, 0, v_x_1064_);
lean_closure_set(v___f_1072_, 1, v_x_1065_);
v___x_1073_ = lean_apply_4(v_inst_1069_, lean_box(0), v_l_1071_, v_m_1070_, v___f_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_a_1076_, lean_object* v_____s_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v_m_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_box(0);
v_m_1079_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1074_, v_x_1075_, v_____s_1077_, v_a_1076_, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_m_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_inst_1083_, lean_object* v_m_1084_, lean_object* v_l_1085_){
_start:
{
lean_object* v___f_1086_; lean_object* v___x_1087_; 
v___f_1086_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1086_, 0, v_x_1081_);
lean_closure_set(v___f_1086_, 1, v_x_1082_);
v___x_1087_ = lean_apply_4(v_inst_1083_, lean_box(0), v_l_1085_, v_m_1084_, v___f_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_00_u03c1_1093_, lean_object* v_inst_1094_, lean_object* v_m_1095_, lean_object* v_l_1096_){
_start:
{
lean_object* v___f_1097_; lean_object* v___x_1098_; 
v___f_1097_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1097_, 0, v_x_1089_);
lean_closure_set(v___f_1097_, 1, v_x_1090_);
v___x_1098_ = lean_apply_4(v_inst_1094_, lean_box(0), v_l_1096_, v_m_1095_, v___f_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__0(lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v_acc_1103_){
_start:
{
lean_object* v_r_1104_; lean_object* v___x_1105_; 
v_r_1104_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1099_, v_x_1100_, v_acc_1103_, v_a_1101_, v_b_1102_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_r_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__1(lean_object* v___x_1106_, lean_object* v___f_1107_, lean_object* v_a_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1106_, v___f_1107_, v_a_1108_, v___y_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg(lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_m_u2081_1116_, lean_object* v_m_u2082_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v_size_1119_; lean_object* v_buckets_1120_; lean_object* v_size_1121_; uint8_t v___x_1122_; 
v___x_1118_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v_size_1119_ = lean_ctor_get(v_m_u2081_1116_, 0);
v_buckets_1120_ = lean_ctor_get(v_m_u2081_1116_, 1);
v_size_1121_ = lean_ctor_get(v_m_u2082_1117_, 0);
v___x_1122_ = lean_nat_dec_le(v_size_1119_, v_size_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1123_, v_x_1114_, v_x_1115_, v_m_u2081_1116_, v_m_u2082_1117_);
return v___x_1124_;
}
else
{
lean_object* v___f_1125_; lean_object* v___f_1126_; size_t v_sz_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
lean_inc_ref(v_buckets_1120_);
lean_dec(v_m_u2081_1116_);
v___f_1125_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1125_, 0, v_x_1114_);
lean_closure_set(v___f_1125_, 1, v_x_1115_);
v___f_1126_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1126_, 0, v___x_1118_);
lean_closure_set(v___f_1126_, 1, v___f_1125_);
v_sz_1127_ = lean_array_size(v_buckets_1120_);
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1118_, v_buckets_1120_, v___f_1126_, v_sz_1127_, v___x_1128_, v_m_u2082_1117_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_m_u2081_1136_, lean_object* v_m_u2082_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v_size_1139_; lean_object* v_buckets_1140_; lean_object* v_size_1141_; uint8_t v___x_1142_; 
v___x_1138_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v_size_1139_ = lean_ctor_get(v_m_u2081_1136_, 0);
v_buckets_1140_ = lean_ctor_get(v_m_u2081_1136_, 1);
v_size_1141_ = lean_ctor_get(v_m_u2082_1137_, 0);
v___x_1142_ = lean_nat_dec_le(v_size_1139_, v_size_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___f_1143_; lean_object* v___x_1144_; 
v___f_1143_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1143_, v_x_1132_, v_x_1133_, v_m_u2081_1136_, v_m_u2082_1137_);
return v___x_1144_;
}
else
{
lean_object* v___f_1145_; lean_object* v___f_1146_; size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
lean_inc_ref(v_buckets_1140_);
lean_dec(v_m_u2081_1136_);
v___f_1145_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1145_, 0, v_x_1132_);
lean_closure_set(v___f_1145_, 1, v_x_1133_);
v___f_1146_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1146_, 0, v___x_1138_);
lean_closure_set(v___f_1146_, 1, v___f_1145_);
v_sz_1147_ = lean_array_size(v_buckets_1140_);
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1138_, v_buckets_1140_, v___f_1146_, v_sz_1147_, v___x_1148_, v_m_u2082_1137_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_1152_, 0, lean_box(0));
lean_closure_set(v___x_1152_, 1, lean_box(0));
lean_closure_set(v___x_1152_, 2, v_x_1150_);
lean_closure_set(v___x_1152_, 3, v_x_1151_);
lean_closure_set(v___x_1152_, 4, lean_box(0));
lean_closure_set(v___x_1152_, 5, lean_box(0));
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_1159_, 0, lean_box(0));
lean_closure_set(v___x_1159_, 1, lean_box(0));
lean_closure_set(v___x_1159_, 2, v_x_1155_);
lean_closure_set(v___x_1159_, 3, v_x_1156_);
lean_closure_set(v___x_1159_, 4, lean_box(0));
lean_closure_set(v___x_1159_, 5, lean_box(0));
return v___x_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_inst_1162_, lean_object* v_m_u2081_1163_, lean_object* v_m_u2082_1164_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1160_, v_x_1161_, v_inst_1162_, v_m_u2081_1163_, v_m_u2082_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_inst_1168_, lean_object* v_m_u2081_1169_, lean_object* v_m_u2082_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_1166_, v_x_1167_, v_inst_1168_, v_m_u2081_1169_, v_m_u2082_1170_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v___f_1176_; 
v___f_1176_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1176_, 0, v_x_1173_);
lean_closure_set(v___f_1176_, 1, v_x_1174_);
lean_closure_set(v___f_1176_, 2, v_inst_1175_);
return v___f_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_){
_start:
{
lean_object* v___f_1184_; 
v___f_1184_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1184_, 0, v_x_1179_);
lean_closure_set(v___f_1184_, 1, v_x_1180_);
lean_closure_set(v___f_1184_, 2, v_inst_1183_);
return v___f_1184_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1185_, v_inst_1186_, v_inst_1187_, v_x_1188_, v_x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1191_, v_inst_1192_, v_inst_1193_, v_x_1194_, v_x_1195_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1200_, v_inst_1202_, v_inst_1203_, v_x_1205_, v_x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_1208_, v_00_u03b2_1209_, v_inst_1210_, v_inst_1211_, v_inst_1212_, v_inst_1213_, v_inst_1214_, v_x_1215_, v_x_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter___redArg(lean_object* v_x_1219_, lean_object* v_x_1220_, lean_object* v_m_u2081_1221_, lean_object* v_m_u2082_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1219_, v_x_1220_, v_m_u2081_1221_, v_m_u2082_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_m_u2081_1230_, lean_object* v_m_u2082_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1226_, v_x_1227_, v_m_u2081_1230_, v_m_u2082_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_1235_, 0, lean_box(0));
lean_closure_set(v___x_1235_, 1, lean_box(0));
lean_closure_set(v___x_1235_, 2, v_x_1233_);
lean_closure_set(v___x_1235_, 3, v_x_1234_);
lean_closure_set(v___x_1235_, 4, lean_box(0));
lean_closure_set(v___x_1235_, 5, lean_box(0));
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b2_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_1242_, 0, lean_box(0));
lean_closure_set(v___x_1242_, 1, lean_box(0));
lean_closure_set(v___x_1242_, 2, v_x_1238_);
lean_closure_set(v___x_1242_, 3, v_x_1239_);
lean_closure_set(v___x_1242_, 4, lean_box(0));
lean_closure_set(v___x_1242_, 5, lean_box(0));
return v___x_1242_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_diff___redArg___lam__0(lean_object* v_x_1243_, lean_object* v_x_1244_, lean_object* v_m_u2082_1245_, uint8_t v___x_1246_, lean_object* v_k_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1243_, v_x_1244_, v_m_u2082_1245_, v_k_1247_);
if (v___x_1249_ == 0)
{
return v___x_1246_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_m_u2082_1253_, lean_object* v___x_1254_, lean_object* v_k_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v___x_107__boxed_1257_; uint8_t v_res_1258_; lean_object* v_r_1259_; 
v___x_107__boxed_1257_ = lean_unbox(v___x_1254_);
v_res_1258_ = l_Std_ExtHashMap_diff___redArg___lam__0(v_x_1251_, v_x_1252_, v_m_u2082_1253_, v___x_107__boxed_1257_, v_k_1255_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec(v_m_u2082_1253_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg(lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_m_u2081_1262_, lean_object* v_m_u2082_1263_){
_start:
{
lean_object* v_size_1264_; lean_object* v_size_1265_; uint8_t v___x_1266_; 
v_size_1264_ = lean_ctor_get(v_m_u2081_1262_, 0);
v_size_1265_ = lean_ctor_get(v_m_u2082_1263_, 0);
v___x_1266_ = lean_nat_dec_le(v_size_1264_, v_size_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___f_1267_; lean_object* v___x_1268_; 
v___f_1267_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1267_, v_x_1260_, v_x_1261_, v_m_u2081_1262_, v_m_u2082_1263_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_box(v___x_1266_);
v___f_1270_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1270_, 0, v_x_1260_);
lean_closure_set(v___f_1270_, 1, v_x_1261_);
lean_closure_set(v___f_1270_, 2, v_m_u2082_1263_);
lean_closure_set(v___f_1270_, 3, v___x_1269_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1270_, v_m_u2081_1262_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff(lean_object* v_00_u03b1_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_m_u2081_1278_, lean_object* v_m_u2082_1279_){
_start:
{
lean_object* v_size_1280_; lean_object* v_size_1281_; uint8_t v___x_1282_; 
v_size_1280_ = lean_ctor_get(v_m_u2081_1278_, 0);
v_size_1281_ = lean_ctor_get(v_m_u2082_1279_, 0);
v___x_1282_ = lean_nat_dec_le(v_size_1280_, v_size_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___f_1283_; lean_object* v___x_1284_; 
v___f_1283_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1283_, v_x_1274_, v_x_1275_, v_m_u2081_1278_, v_m_u2082_1279_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_box(v___x_1282_);
v___f_1286_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1286_, 0, v_x_1274_);
lean_closure_set(v___f_1286_, 1, v_x_1275_);
lean_closure_set(v___f_1286_, 2, v_m_u2082_1279_);
lean_closure_set(v___f_1286_, 3, v___x_1285_);
v___x_1287_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1286_, v_m_u2081_1278_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_1290_, 0, lean_box(0));
lean_closure_set(v___x_1290_, 1, lean_box(0));
lean_closure_set(v___x_1290_, 2, v_x_1288_);
lean_closure_set(v___x_1290_, 3, v_x_1289_);
lean_closure_set(v___x_1290_, 4, lean_box(0));
lean_closure_set(v___x_1290_, 5, lean_box(0));
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1291_, lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_1297_, 0, lean_box(0));
lean_closure_set(v___x_1297_, 1, lean_box(0));
lean_closure_set(v___x_1297_, 2, v_x_1293_);
lean_closure_set(v___x_1297_, 3, v_x_1294_);
lean_closure_set(v___x_1297_, 4, lean_box(0));
lean_closure_set(v___x_1297_, 5, lean_box(0));
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray___redArg(lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_l_1304_){
_start:
{
lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___f_1305_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_1306_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1305_, v_inst_1302_, v_inst_1303_, v___x_1306_, v_l_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray(lean_object* v_00_u03b1_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_l_1311_){
_start:
{
lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___f_1312_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_1313_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_1314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1312_, v_inst_1309_, v_inst_1310_, v___x_1313_, v_l_1311_);
return v___x_1314_;
}
}
lean_object* runtime_initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
