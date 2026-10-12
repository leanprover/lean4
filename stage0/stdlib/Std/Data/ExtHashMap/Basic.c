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
lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_41_;
v_res_41_ = l_Std_ExtHashMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_ExtHashMap_instEmptyCollection___redArg();
return v_res_43_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_ExtHashMap_instEmptyCollection___redArg();
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__0, &l_Std_ExtHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_ExtHashMap_instEmptyCollection(v_00_u03b1_50_, v_00_u03b2_51_, v_inst_52_, v_inst_53_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
return v_res_54_;
}
}
lean_object* l_Std_ExtHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
return v___x_56_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_57_;
v_res_57_ = l_Std_ExtHashMap_instInhabited___redArg();
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_ExtHashMap_instInhabited___redArg();
return v_res_59_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_ExtHashMap_instInhabited___redArg();
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_inst_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Std_ExtHashMap_instInhabited___closed__0, &l_Std_ExtHashMap_instInhabited___closed__0_once, _init_l_Std_ExtHashMap_instInhabited___closed__0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___boxed(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_ExtHashMap_instInhabited(v_00_u03b1_66_, v_00_u03b2_67_, v_inst_68_, v_inst_69_);
lean_dec_ref(v_inst_69_);
lean_dec_ref(v_inst_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert___redArg(lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_m_73_, lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_71_, v_x_72_, v_m_73_, v_a_74_, v_b_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_m_83_, lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_79_, v_x_80_, v_m_83_, v_a_84_, v_b_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_fst_90_; lean_object* v_snd_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_fst_90_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_fst_90_);
v_snd_91_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_snd_91_);
lean_dec_ref(v_x_89_);
v___x_92_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_87_, v_x_88_, v___x_92_, v_fst_90_, v_snd_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v___f_96_; 
v___f_96_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_96_, 0, v_x_94_);
lean_closure_set(v___f_96_, 1, v_x_95_);
return v___f_96_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_inst_101_, lean_object* v_inst_102_){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_103_, 0, v_x_99_);
lean_closure_set(v___f_103_, 1, v_x_100_);
return v___f_103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v___x_110_; 
v_fst_108_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_fst_108_);
v_snd_109_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_snd_109_);
lean_dec_ref(v_x_106_);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_104_, v_x_105_, v_x_107_, v_fst_108_, v_snd_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___f_113_; 
v___f_113_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_113_, 0, v_x_111_);
lean_closure_set(v___f_113_, 1, v_x_112_);
return v___f_113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_inst_118_, lean_object* v_inst_119_){
_start:
{
lean_object* v___f_120_; 
v___f_120_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_120_, 0, v_x_116_);
lean_closure_set(v___f_120_, 1, v_x_117_);
return v___f_120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew___redArg(lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_m_123_, lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_121_, v_x_122_, v_m_123_, v_a_124_, v_b_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_m_133_, lean_object* v_a_134_, lean_object* v_b_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_129_, v_x_130_, v_m_133_, v_a_134_, v_b_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert___redArg(lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_m_139_, lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
lean_object* v_size_142_; lean_object* v_buckets_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_194_; 
v_size_142_ = lean_ctor_get(v_m_139_, 0);
v_buckets_143_ = lean_ctor_get(v_m_139_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_m_139_);
if (v_isSharedCheck_194_ == 0)
{
v___x_145_ = v_m_139_;
v_isShared_146_ = v_isSharedCheck_194_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_buckets_143_);
lean_inc(v_size_142_);
lean_dec(v_m_139_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_194_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v_fold_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; lean_object* v_bkt_162_; uint8_t v___x_163_; 
v___x_147_ = lean_array_get_size(v_buckets_143_);
lean_inc_ref(v_x_138_);
lean_inc_n(v_a_140_, 2);
v___x_148_ = lean_apply_1(v_x_138_, v_a_140_);
v___x_149_ = 32ULL;
v___x_150_ = lean_unbox_uint64(v___x_148_);
v___x_151_ = lean_uint64_shift_right(v___x_150_, v___x_149_);
v___x_152_ = lean_unbox_uint64(v___x_148_);
lean_dec_ref(v___x_148_);
v_fold_153_ = lean_uint64_xor(v___x_152_, v___x_151_);
v___x_154_ = 16ULL;
v___x_155_ = lean_uint64_shift_right(v_fold_153_, v___x_154_);
v___x_156_ = lean_uint64_xor(v_fold_153_, v___x_155_);
v___x_157_ = lean_uint64_to_usize(v___x_156_);
v___x_158_ = lean_usize_of_nat(v___x_147_);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_sub(v___x_158_, v___x_159_);
v___x_161_ = lean_usize_land(v___x_157_, v___x_160_);
v_bkt_162_ = lean_array_uget_borrowed(v_buckets_143_, v___x_161_);
lean_inc(v_bkt_162_);
lean_inc_ref(v_x_137_);
v___x_163_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_137_, v_a_140_, v_bkt_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v_size_x27_165_; lean_object* v___x_166_; lean_object* v_buckets_x27_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
lean_dec_ref(v_x_137_);
v___x_164_ = lean_unsigned_to_nat(1u);
v_size_x27_165_ = lean_nat_add(v_size_142_, v___x_164_);
lean_dec(v_size_142_);
lean_inc(v_bkt_162_);
v___x_166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_166_, 0, v_a_140_);
lean_ctor_set(v___x_166_, 1, v_b_141_);
lean_ctor_set(v___x_166_, 2, v_bkt_162_);
v_buckets_x27_167_ = lean_array_uset(v_buckets_143_, v___x_161_, v___x_166_);
v___x_168_ = lean_unsigned_to_nat(4u);
v___x_169_ = lean_nat_mul(v_size_x27_165_, v___x_168_);
v___x_170_ = lean_unsigned_to_nat(3u);
v___x_171_ = lean_nat_div(v___x_169_, v___x_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_array_get_size(v_buckets_x27_167_);
v___x_173_ = lean_nat_dec_le(v___x_171_, v___x_172_);
lean_dec(v___x_171_);
if (v___x_173_ == 0)
{
lean_object* v_val_174_; lean_object* v___x_176_; 
v_val_174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_138_, v_buckets_x27_167_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v_val_174_);
lean_ctor_set(v___x_145_, 0, v_size_x27_165_);
v___x_176_ = v___x_145_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_size_x27_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_val_174_);
v___x_176_ = v_reuseFailAlloc_179_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_box(v___x_163_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
return v___x_178_;
}
}
else
{
lean_object* v___x_181_; 
lean_dec_ref(v_x_138_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v_buckets_x27_167_);
lean_ctor_set(v___x_145_, 0, v_size_x27_165_);
v___x_181_ = v___x_145_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_size_x27_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_buckets_x27_167_);
v___x_181_ = v_reuseFailAlloc_184_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(v___x_163_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
return v___x_183_;
}
}
}
else
{
lean_object* v___x_185_; lean_object* v_buckets_x27_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_bkt_162_);
lean_dec_ref(v_x_138_);
v___x_185_ = lean_box(0);
v_buckets_x27_186_ = lean_array_uset(v_buckets_143_, v___x_161_, v___x_185_);
v___x_187_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_137_, v_a_140_, v_b_141_, v_bkt_162_);
v___x_188_ = lean_array_uset(v_buckets_x27_186_, v___x_161_, v___x_187_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_188_);
v___x_190_ = v___x_145_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_size_142_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_box(v___x_163_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_m_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v_size_204_; lean_object* v_buckets_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_256_; 
v_size_204_ = lean_ctor_get(v_m_201_, 0);
v_buckets_205_ = lean_ctor_get(v_m_201_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_m_201_);
if (v_isSharedCheck_256_ == 0)
{
v___x_207_ = v_m_201_;
v_isShared_208_ = v_isSharedCheck_256_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_buckets_205_);
lean_inc(v_size_204_);
lean_dec(v_m_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_256_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v_fold_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v_bkt_224_; uint8_t v___x_225_; 
v___x_209_ = lean_array_get_size(v_buckets_205_);
lean_inc_ref(v_x_198_);
lean_inc_n(v_a_202_, 2);
v___x_210_ = lean_apply_1(v_x_198_, v_a_202_);
v___x_211_ = 32ULL;
v___x_212_ = lean_unbox_uint64(v___x_210_);
v___x_213_ = lean_uint64_shift_right(v___x_212_, v___x_211_);
v___x_214_ = lean_unbox_uint64(v___x_210_);
lean_dec_ref(v___x_210_);
v_fold_215_ = lean_uint64_xor(v___x_214_, v___x_213_);
v___x_216_ = 16ULL;
v___x_217_ = lean_uint64_shift_right(v_fold_215_, v___x_216_);
v___x_218_ = lean_uint64_xor(v_fold_215_, v___x_217_);
v___x_219_ = lean_uint64_to_usize(v___x_218_);
v___x_220_ = lean_usize_of_nat(v___x_209_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_sub(v___x_220_, v___x_221_);
v___x_223_ = lean_usize_land(v___x_219_, v___x_222_);
v_bkt_224_ = lean_array_uget_borrowed(v_buckets_205_, v___x_223_);
lean_inc(v_bkt_224_);
lean_inc_ref(v_x_197_);
v___x_225_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_197_, v_a_202_, v_bkt_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v_size_x27_227_; lean_object* v___x_228_; lean_object* v_buckets_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
lean_dec_ref(v_x_197_);
v___x_226_ = lean_unsigned_to_nat(1u);
v_size_x27_227_ = lean_nat_add(v_size_204_, v___x_226_);
lean_dec(v_size_204_);
lean_inc(v_bkt_224_);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v_a_202_);
lean_ctor_set(v___x_228_, 1, v_b_203_);
lean_ctor_set(v___x_228_, 2, v_bkt_224_);
v_buckets_x27_229_ = lean_array_uset(v_buckets_205_, v___x_223_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(4u);
v___x_231_ = lean_nat_mul(v_size_x27_227_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(3u);
v___x_233_ = lean_nat_div(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_array_get_size(v_buckets_x27_229_);
v___x_235_ = lean_nat_dec_le(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
if (v___x_235_ == 0)
{
lean_object* v_val_236_; lean_object* v___x_238_; 
v_val_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_198_, v_buckets_x27_229_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_val_236_);
lean_ctor_set(v___x_207_, 0, v_size_x27_227_);
v___x_238_ = v___x_207_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_val_236_);
v___x_238_ = v_reuseFailAlloc_241_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(v___x_225_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
else
{
lean_object* v___x_243_; 
lean_dec_ref(v_x_198_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_buckets_x27_229_);
lean_ctor_set(v___x_207_, 0, v_size_x27_227_);
v___x_243_ = v___x_207_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_buckets_x27_229_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_box(v___x_225_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
return v___x_245_;
}
}
}
else
{
lean_object* v___x_247_; lean_object* v_buckets_x27_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
lean_inc(v_bkt_224_);
lean_dec_ref(v_x_198_);
v___x_247_ = lean_box(0);
v_buckets_x27_248_ = lean_array_uset(v_buckets_205_, v___x_223_, v___x_247_);
v___x_249_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_197_, v_a_202_, v_b_203_, v_bkt_224_);
v___x_250_ = lean_array_uset(v_buckets_x27_248_, v___x_223_, v___x_249_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v___x_250_);
v___x_252_ = v___x_207_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_size_204_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_255_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_box(v___x_225_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_m_259_, lean_object* v_a_260_, lean_object* v_b_261_){
_start:
{
lean_object* v_size_262_; lean_object* v_buckets_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v_fold_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_bkt_279_; uint8_t v___x_280_; 
v_size_262_ = lean_ctor_get(v_m_259_, 0);
v_buckets_263_ = lean_ctor_get(v_m_259_, 1);
v___x_264_ = lean_array_get_size(v_buckets_263_);
lean_inc_ref(v_x_258_);
lean_inc_n(v_a_260_, 2);
v___x_265_ = lean_apply_1(v_x_258_, v_a_260_);
v___x_266_ = 32ULL;
v___x_267_ = lean_unbox_uint64(v___x_265_);
v___x_268_ = lean_uint64_shift_right(v___x_267_, v___x_266_);
v___x_269_ = lean_unbox_uint64(v___x_265_);
lean_dec_ref(v___x_265_);
v_fold_270_ = lean_uint64_xor(v___x_269_, v___x_268_);
v___x_271_ = 16ULL;
v___x_272_ = lean_uint64_shift_right(v_fold_270_, v___x_271_);
v___x_273_ = lean_uint64_xor(v_fold_270_, v___x_272_);
v___x_274_ = lean_uint64_to_usize(v___x_273_);
v___x_275_ = lean_usize_of_nat(v___x_264_);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_sub(v___x_275_, v___x_276_);
v___x_278_ = lean_usize_land(v___x_274_, v___x_277_);
v_bkt_279_ = lean_array_uget_borrowed(v_buckets_263_, v___x_278_);
lean_inc(v_bkt_279_);
v___x_280_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_257_, v_a_260_, v_bkt_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_305_; 
lean_inc_ref(v_buckets_263_);
lean_inc(v_size_262_);
v_isSharedCheck_305_ = !lean_is_exclusive(v_m_259_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; lean_object* v_unused_307_; 
v_unused_306_ = lean_ctor_get(v_m_259_, 1);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_m_259_, 0);
lean_dec(v_unused_307_);
v___x_282_ = v_m_259_;
v_isShared_283_ = v_isSharedCheck_305_;
goto v_resetjp_281_;
}
else
{
lean_dec(v_m_259_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_305_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_size_x27_285_; lean_object* v___x_286_; lean_object* v_buckets_x27_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v_size_x27_285_ = lean_nat_add(v_size_262_, v___x_284_);
lean_dec(v_size_262_);
lean_inc(v_bkt_279_);
v___x_286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_286_, 0, v_a_260_);
lean_ctor_set(v___x_286_, 1, v_b_261_);
lean_ctor_set(v___x_286_, 2, v_bkt_279_);
v_buckets_x27_287_ = lean_array_uset(v_buckets_263_, v___x_278_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(4u);
v___x_289_ = lean_nat_mul(v_size_x27_285_, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(3u);
v___x_291_ = lean_nat_div(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_array_get_size(v_buckets_x27_287_);
v___x_293_ = lean_nat_dec_le(v___x_291_, v___x_292_);
lean_dec(v___x_291_);
if (v___x_293_ == 0)
{
lean_object* v_val_294_; lean_object* v___x_296_; 
v_val_294_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_258_, v_buckets_x27_287_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_val_294_);
lean_ctor_set(v___x_282_, 0, v_size_x27_285_);
v___x_296_ = v___x_282_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_size_x27_285_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_val_294_);
v___x_296_ = v_reuseFailAlloc_299_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_box(v___x_280_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
else
{
lean_object* v___x_301_; 
lean_dec_ref(v_x_258_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_buckets_x27_287_);
lean_ctor_set(v___x_282_, 0, v_size_x27_285_);
v___x_301_ = v___x_282_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_size_x27_285_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_buckets_x27_287_);
v___x_301_ = v_reuseFailAlloc_304_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_box(v___x_280_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
return v___x_303_;
}
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_b_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_x_258_);
v___x_308_ = lean_box(v___x_280_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_m_259_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_310_, lean_object* v_00_u03b2_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_m_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
lean_object* v_size_319_; lean_object* v_buckets_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v_fold_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v_bkt_336_; uint8_t v___x_337_; 
v_size_319_ = lean_ctor_get(v_m_316_, 0);
v_buckets_320_ = lean_ctor_get(v_m_316_, 1);
v___x_321_ = lean_array_get_size(v_buckets_320_);
lean_inc_ref(v_x_313_);
lean_inc_n(v_a_317_, 2);
v___x_322_ = lean_apply_1(v_x_313_, v_a_317_);
v___x_323_ = 32ULL;
v___x_324_ = lean_unbox_uint64(v___x_322_);
v___x_325_ = lean_uint64_shift_right(v___x_324_, v___x_323_);
v___x_326_ = lean_unbox_uint64(v___x_322_);
lean_dec_ref(v___x_322_);
v_fold_327_ = lean_uint64_xor(v___x_326_, v___x_325_);
v___x_328_ = 16ULL;
v___x_329_ = lean_uint64_shift_right(v_fold_327_, v___x_328_);
v___x_330_ = lean_uint64_xor(v_fold_327_, v___x_329_);
v___x_331_ = lean_uint64_to_usize(v___x_330_);
v___x_332_ = lean_usize_of_nat(v___x_321_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_sub(v___x_332_, v___x_333_);
v___x_335_ = lean_usize_land(v___x_331_, v___x_334_);
v_bkt_336_ = lean_array_uget_borrowed(v_buckets_320_, v___x_335_);
lean_inc(v_bkt_336_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_312_, v_a_317_, v_bkt_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_362_; 
lean_inc_ref(v_buckets_320_);
lean_inc(v_size_319_);
v_isSharedCheck_362_ = !lean_is_exclusive(v_m_316_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_363_ = lean_ctor_get(v_m_316_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_m_316_, 0);
lean_dec(v_unused_364_);
v___x_339_ = v_m_316_;
v_isShared_340_ = v_isSharedCheck_362_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_m_316_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_362_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v_size_x27_342_; lean_object* v___x_343_; lean_object* v_buckets_x27_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_341_ = lean_unsigned_to_nat(1u);
v_size_x27_342_ = lean_nat_add(v_size_319_, v___x_341_);
lean_dec(v_size_319_);
lean_inc(v_bkt_336_);
v___x_343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_343_, 0, v_a_317_);
lean_ctor_set(v___x_343_, 1, v_b_318_);
lean_ctor_set(v___x_343_, 2, v_bkt_336_);
v_buckets_x27_344_ = lean_array_uset(v_buckets_320_, v___x_335_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(4u);
v___x_346_ = lean_nat_mul(v_size_x27_342_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(3u);
v___x_348_ = lean_nat_div(v___x_346_, v___x_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_array_get_size(v_buckets_x27_344_);
v___x_350_ = lean_nat_dec_le(v___x_348_, v___x_349_);
lean_dec(v___x_348_);
if (v___x_350_ == 0)
{
lean_object* v_val_351_; lean_object* v___x_353_; 
v_val_351_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_313_, v_buckets_x27_344_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_val_351_);
lean_ctor_set(v___x_339_, 0, v_size_x27_342_);
v___x_353_ = v___x_339_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_size_x27_342_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_val_351_);
v___x_353_ = v_reuseFailAlloc_356_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_box(v___x_337_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
return v___x_355_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec_ref(v_x_313_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_buckets_x27_344_);
lean_ctor_set(v___x_339_, 0, v_size_x27_342_);
v___x_358_ = v___x_339_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_size_x27_342_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_buckets_x27_344_);
v___x_358_ = v_reuseFailAlloc_361_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_box(v___x_337_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
return v___x_360_;
}
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v_b_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_x_313_);
v___x_365_ = lean_box(v___x_337_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_m_316_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_m_369_, lean_object* v_a_370_, lean_object* v_b_371_){
_start:
{
lean_object* v_size_372_; lean_object* v_buckets_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v_fold_380_; uint64_t v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v_bkt_389_; lean_object* v___x_390_; 
v_size_372_ = lean_ctor_get(v_m_369_, 0);
v_buckets_373_ = lean_ctor_get(v_m_369_, 1);
v___x_374_ = lean_array_get_size(v_buckets_373_);
lean_inc_ref(v_x_368_);
lean_inc_n(v_a_370_, 2);
v___x_375_ = lean_apply_1(v_x_368_, v_a_370_);
v___x_376_ = 32ULL;
v___x_377_ = lean_unbox_uint64(v___x_375_);
v___x_378_ = lean_uint64_shift_right(v___x_377_, v___x_376_);
v___x_379_ = lean_unbox_uint64(v___x_375_);
lean_dec_ref(v___x_375_);
v_fold_380_ = lean_uint64_xor(v___x_379_, v___x_378_);
v___x_381_ = 16ULL;
v___x_382_ = lean_uint64_shift_right(v_fold_380_, v___x_381_);
v___x_383_ = lean_uint64_xor(v_fold_380_, v___x_382_);
v___x_384_ = lean_uint64_to_usize(v___x_383_);
v___x_385_ = lean_usize_of_nat(v___x_374_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_sub(v___x_385_, v___x_386_);
v___x_388_ = lean_usize_land(v___x_384_, v___x_387_);
v_bkt_389_ = lean_array_uget_borrowed(v_buckets_373_, v___x_388_);
lean_inc(v_bkt_389_);
v___x_390_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_367_, v_a_370_, v_bkt_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_413_; 
lean_inc_ref(v_buckets_373_);
lean_inc(v_size_372_);
v_isSharedCheck_413_ = !lean_is_exclusive(v_m_369_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_414_ = lean_ctor_get(v_m_369_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_m_369_, 0);
lean_dec(v_unused_415_);
v___x_392_ = v_m_369_;
v_isShared_393_ = v_isSharedCheck_413_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_m_369_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_413_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v_size_x27_395_; lean_object* v___x_396_; lean_object* v_buckets_x27_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v_size_x27_395_ = lean_nat_add(v_size_372_, v___x_394_);
lean_dec(v_size_372_);
lean_inc(v_bkt_389_);
v___x_396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_396_, 0, v_a_370_);
lean_ctor_set(v___x_396_, 1, v_b_371_);
lean_ctor_set(v___x_396_, 2, v_bkt_389_);
v_buckets_x27_397_ = lean_array_uset(v_buckets_373_, v___x_388_, v___x_396_);
v___x_398_ = lean_unsigned_to_nat(4u);
v___x_399_ = lean_nat_mul(v_size_x27_395_, v___x_398_);
v___x_400_ = lean_unsigned_to_nat(3u);
v___x_401_ = lean_nat_div(v___x_399_, v___x_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_array_get_size(v_buckets_x27_397_);
v___x_403_ = lean_nat_dec_le(v___x_401_, v___x_402_);
lean_dec(v___x_401_);
if (v___x_403_ == 0)
{
lean_object* v_val_404_; lean_object* v___x_406_; 
v_val_404_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_368_, v_buckets_x27_397_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_val_404_);
lean_ctor_set(v___x_392_, 0, v_size_x27_395_);
v___x_406_ = v___x_392_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_size_x27_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_val_404_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_390_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
return v___x_407_;
}
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v_x_368_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_buckets_x27_397_);
lean_ctor_set(v___x_392_, 0, v_size_x27_395_);
v___x_410_ = v___x_392_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_size_x27_395_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_buckets_x27_397_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_390_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
return v___x_411_;
}
}
}
}
else
{
lean_object* v___x_416_; 
lean_dec(v_b_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_x_368_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_390_);
lean_ctor_set(v___x_416_, 1, v_m_369_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_417_, lean_object* v_00_u03b2_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_m_423_, lean_object* v_a_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_size_426_; lean_object* v_buckets_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v_fold_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v_bkt_443_; lean_object* v___x_444_; 
v_size_426_ = lean_ctor_get(v_m_423_, 0);
v_buckets_427_ = lean_ctor_get(v_m_423_, 1);
v___x_428_ = lean_array_get_size(v_buckets_427_);
lean_inc_ref(v_x_420_);
lean_inc_n(v_a_424_, 2);
v___x_429_ = lean_apply_1(v_x_420_, v_a_424_);
v___x_430_ = 32ULL;
v___x_431_ = lean_unbox_uint64(v___x_429_);
v___x_432_ = lean_uint64_shift_right(v___x_431_, v___x_430_);
v___x_433_ = lean_unbox_uint64(v___x_429_);
lean_dec_ref(v___x_429_);
v_fold_434_ = lean_uint64_xor(v___x_433_, v___x_432_);
v___x_435_ = 16ULL;
v___x_436_ = lean_uint64_shift_right(v_fold_434_, v___x_435_);
v___x_437_ = lean_uint64_xor(v_fold_434_, v___x_436_);
v___x_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = lean_usize_of_nat(v___x_428_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_sub(v___x_439_, v___x_440_);
v___x_442_ = lean_usize_land(v___x_438_, v___x_441_);
v_bkt_443_ = lean_array_uget_borrowed(v_buckets_427_, v___x_442_);
lean_inc(v_bkt_443_);
v___x_444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_419_, v_a_424_, v_bkt_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_467_; 
lean_inc_ref(v_buckets_427_);
lean_inc(v_size_426_);
v_isSharedCheck_467_ = !lean_is_exclusive(v_m_423_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; 
v_unused_468_ = lean_ctor_get(v_m_423_, 1);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_m_423_, 0);
lean_dec(v_unused_469_);
v___x_446_ = v_m_423_;
v_isShared_447_ = v_isSharedCheck_467_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_m_423_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_467_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v_size_x27_449_; lean_object* v___x_450_; lean_object* v_buckets_x27_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_448_ = lean_unsigned_to_nat(1u);
v_size_x27_449_ = lean_nat_add(v_size_426_, v___x_448_);
lean_dec(v_size_426_);
lean_inc(v_bkt_443_);
v___x_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_450_, 0, v_a_424_);
lean_ctor_set(v___x_450_, 1, v_b_425_);
lean_ctor_set(v___x_450_, 2, v_bkt_443_);
v_buckets_x27_451_ = lean_array_uset(v_buckets_427_, v___x_442_, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(4u);
v___x_453_ = lean_nat_mul(v_size_x27_449_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(3u);
v___x_455_ = lean_nat_div(v___x_453_, v___x_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_array_get_size(v_buckets_x27_451_);
v___x_457_ = lean_nat_dec_le(v___x_455_, v___x_456_);
lean_dec(v___x_455_);
if (v___x_457_ == 0)
{
lean_object* v_val_458_; lean_object* v___x_460_; 
v_val_458_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_420_, v_buckets_x27_451_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_val_458_);
lean_ctor_set(v___x_446_, 0, v_size_x27_449_);
v___x_460_ = v___x_446_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_size_x27_449_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_val_458_);
v___x_460_ = v_reuseFailAlloc_462_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_444_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
return v___x_461_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v_x_420_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_buckets_x27_451_);
lean_ctor_set(v___x_446_, 0, v_size_x27_449_);
v___x_464_ = v___x_446_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_size_x27_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_buckets_x27_451_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_444_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
}
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_b_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_x_420_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_444_);
lean_ctor_set(v___x_470_, 1, v_m_423_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg(lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_m_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_471_, v_x_472_, v_m_473_, v_a_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg___boxed(lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_m_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_ExtHashMap_get_x3f___redArg(v_x_476_, v_x_477_, v_m_478_, v_a_479_);
lean_dec(v_m_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_483_, v_x_484_, v_m_487_, v_a_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___boxed(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_m_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_ExtHashMap_get_x3f(v_00_u03b1_490_, v_00_u03b2_491_, v_x_492_, v_x_493_, v_inst_494_, v_inst_495_, v_m_496_, v_a_497_);
lean_dec(v_m_496_);
return v_res_498_;
}
}
uint8_t l_Std_ExtHashMap_contains___redArg(lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_499_, v_x_500_, v_m_501_, v_a_502_);
return v___x_503_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_499_ = stack[0].m_obj;
lean_object* v_x_500_ = stack[1].m_obj;
lean_object* v_m_501_ = stack[2].m_obj;
lean_object* v_a_502_ = stack[3].m_obj;
uint8_t v_res_504_;
v_res_504_ = l_Std_ExtHashMap_contains___redArg(v_x_499_, v_x_500_, v_m_501_, v_a_502_);
stack->m_num = v_res_504_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___redArg___boxed(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_m_507_, lean_object* v_a_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_Std_ExtHashMap_contains___redArg(v_x_505_, v_x_506_, v_m_507_, v_a_508_);
lean_dec(v_m_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
uint8_t l_Std_ExtHashMap_contains(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_m_517_, lean_object* v_a_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_513_, v_x_514_, v_m_517_, v_a_518_);
return v___x_519_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_513_ = stack[2].m_obj;
lean_object* v_x_514_ = stack[3].m_obj;
lean_object* v_m_517_ = stack[6].m_obj;
lean_object* v_a_518_ = stack[7].m_obj;
uint8_t v_res_520_;
v_res_520_ = l_Std_ExtHashMap_contains(lean_box(0), lean_box(0), v_x_513_, v_x_514_, lean_box(0), lean_box(0), v_m_517_, v_a_518_);
stack->m_num = v_res_520_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___boxed(lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Std_ExtHashMap_contains(v_00_u03b1_521_, v_00_u03b2_522_, v_x_523_, v_x_524_, v_inst_525_, v_inst_526_, v_m_527_, v_a_528_);
lean_dec(v_m_527_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg(){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_533_;
v_res_533_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object* v___dummy_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_543_, v_00_u03b2_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_inst_548_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_inst_545_);
return v_res_549_;
}
}
uint8_t l_Std_ExtHashMap_instDecidableMem___redArg(lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_m_552_, lean_object* v_a_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_550_, v_inst_551_, v_m_552_, v_a_553_);
return v___x_554_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_550_ = stack[0].m_obj;
lean_object* v_inst_551_ = stack[1].m_obj;
lean_object* v_m_552_ = stack[2].m_obj;
lean_object* v_a_553_ = stack[3].m_obj;
uint8_t v_res_555_;
v_res_555_ = l_Std_ExtHashMap_instDecidableMem___redArg(v_inst_550_, v_inst_551_, v_m_552_, v_a_553_);
stack->m_num = v_res_555_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_m_558_, lean_object* v_a_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Std_ExtHashMap_instDecidableMem___redArg(v_inst_556_, v_inst_557_, v_m_558_, v_a_559_);
lean_dec(v_m_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
uint8_t l_Std_ExtHashMap_instDecidableMem(lean_object* v_00_u03b1_562_, lean_object* v_00_u03b2_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_564_, v_inst_565_, v_m_568_, v_a_569_);
return v___x_570_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_564_ = stack[2].m_obj;
lean_object* v_inst_565_ = stack[3].m_obj;
lean_object* v_m_568_ = stack[6].m_obj;
lean_object* v_a_569_ = stack[7].m_obj;
uint8_t v_res_571_;
v_res_571_ = l_Std_ExtHashMap_instDecidableMem(lean_box(0), lean_box(0), v_inst_564_, v_inst_565_, lean_box(0), lean_box(0), v_m_568_, v_a_569_);
stack->m_num = v_res_571_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_m_578_, lean_object* v_a_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l_Std_ExtHashMap_instDecidableMem(v_00_u03b1_572_, v_00_u03b2_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_m_578_, v_a_579_);
lean_dec(v_m_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg(lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_m_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_582_, v_x_583_, v_m_584_, v_a_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg___boxed(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_m_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_ExtHashMap_get___redArg(v_x_587_, v_x_588_, v_m_589_, v_a_590_);
lean_dec(v_m_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_m_598_, lean_object* v_a_599_, lean_object* v_h_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_594_, v_x_595_, v_m_598_, v_a_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___boxed(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_m_608_, lean_object* v_a_609_, lean_object* v_h_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_ExtHashMap_get(v_00_u03b1_602_, v_00_u03b2_603_, v_x_604_, v_x_605_, v_inst_606_, v_inst_607_, v_m_608_, v_a_609_, v_h_610_);
lean_dec(v_m_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_m_614_, lean_object* v_a_615_, lean_object* v_fallback_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_612_, v_x_613_, v_m_614_, v_a_615_, v_fallback_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg___boxed(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_m_620_, lean_object* v_a_621_, lean_object* v_fallback_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_ExtHashMap_getD___redArg(v_x_618_, v_x_619_, v_m_620_, v_a_621_, v_fallback_622_);
lean_dec(v_fallback_622_);
lean_dec(v_m_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_m_630_, lean_object* v_a_631_, lean_object* v_fallback_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_626_, v_x_627_, v_m_630_, v_a_631_, v_fallback_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___boxed(lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_m_640_, lean_object* v_a_641_, lean_object* v_fallback_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_ExtHashMap_getD(v_00_u03b1_634_, v_00_u03b2_635_, v_x_636_, v_x_637_, v_inst_638_, v_inst_639_, v_m_640_, v_a_641_, v_fallback_642_);
lean_dec(v_fallback_642_);
lean_dec(v_m_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg(lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_inst_646_, lean_object* v_m_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_644_, v_x_645_, v_inst_646_, v_m_647_, v_a_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg___boxed(lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_ExtHashMap_get_x21___redArg(v_x_650_, v_x_651_, v_inst_652_, v_m_653_, v_a_654_);
lean_dec(v_m_653_);
lean_dec(v_inst_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_m_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_658_, v_x_659_, v_inst_662_, v_m_663_, v_a_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___boxed(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_m_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_ExtHashMap_get_x21(v_00_u03b1_666_, v_00_u03b2_667_, v_x_668_, v_x_669_, v_inst_670_, v_inst_671_, v_inst_672_, v_m_673_, v_a_674_);
lean_dec(v_m_673_);
lean_dec(v_inst_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_m_678_, lean_object* v_a_679_, lean_object* v_h_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_676_, v_inst_677_, v_m_678_, v_a_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_m_684_, lean_object* v_a_685_, lean_object* v_h_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_682_, v_inst_683_, v_m_684_, v_a_685_, v_h_686_);
lean_dec(v_m_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_m_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_688_, v_inst_689_, v_m_690_, v_a_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_693_, v_inst_694_, v_m_695_, v_a_696_);
lean_dec(v_m_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_m_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_698_, v_inst_699_, v_inst_700_, v_m_701_, v_a_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_m_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_704_, v_inst_705_, v_inst_706_, v_m_707_, v_a_708_);
lean_dec(v_m_707_);
lean_dec(v_inst_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_710_, lean_object* v_inst_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___x_715_; 
lean_inc_ref_n(v_inst_711_, 2);
lean_inc_ref_n(v_inst_710_, 2);
v___f_712_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_712_, 0, v_inst_710_);
lean_closure_set(v___f_712_, 1, v_inst_711_);
v___f_713_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_713_, 0, v_inst_710_);
lean_closure_set(v___f_713_, 1, v_inst_711_);
v___f_714_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_714_, 0, v_inst_710_);
lean_closure_set(v___f_714_, 1, v_inst_711_);
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v___f_712_);
lean_ctor_set(v___x_715_, 1, v___f_713_);
lean_ctor_set(v___x_715_, 2, v___f_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg(v_inst_718_, v_inst_719_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_m_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_723_, v_x_724_, v_m_725_, v_a_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_m_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_ExtHashMap_getKey_x3f___redArg(v_x_728_, v_x_729_, v_m_730_, v_a_731_);
lean_dec(v_m_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_735_, v_x_736_, v_m_739_, v_a_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_ExtHashMap_getKey_x3f(v_00_u03b1_742_, v_00_u03b2_743_, v_x_744_, v_x_745_, v_inst_746_, v_inst_747_, v_m_748_, v_a_749_);
lean_dec(v_m_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg(lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_m_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_751_, v_x_752_, v_m_753_, v_a_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg___boxed(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_m_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_ExtHashMap_getKey___redArg(v_x_756_, v_x_757_, v_m_758_, v_a_759_);
lean_dec(v_m_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_m_767_, lean_object* v_a_768_, lean_object* v_h_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_763_, v_x_764_, v_m_767_, v_a_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___boxed(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_m_777_, lean_object* v_a_778_, lean_object* v_h_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_ExtHashMap_getKey(v_00_u03b1_771_, v_00_u03b2_772_, v_x_773_, v_x_774_, v_inst_775_, v_inst_776_, v_m_777_, v_a_778_, v_h_779_);
lean_dec(v_m_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg(lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_m_783_, lean_object* v_a_784_, lean_object* v_fallback_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_781_, v_x_782_, v_m_783_, v_a_784_, v_fallback_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_m_789_, lean_object* v_a_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_ExtHashMap_getKeyD___redArg(v_x_787_, v_x_788_, v_m_789_, v_a_790_, v_fallback_791_);
lean_dec(v_fallback_791_);
lean_dec(v_m_789_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD(lean_object* v_00_u03b1_793_, lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_m_799_, lean_object* v_a_800_, lean_object* v_fallback_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_795_, v_x_796_, v_m_799_, v_a_800_, v_fallback_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___boxed(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_m_809_, lean_object* v_a_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_ExtHashMap_getKeyD(v_00_u03b1_803_, v_00_u03b2_804_, v_x_805_, v_x_806_, v_inst_807_, v_inst_808_, v_m_809_, v_a_810_, v_fallback_811_);
lean_dec(v_fallback_811_);
lean_dec(v_m_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg(lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_inst_815_, lean_object* v_m_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_813_, v_x_814_, v_inst_815_, v_m_816_, v_a_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg___boxed(lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_inst_821_, lean_object* v_m_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_ExtHashMap_getKey_x21___redArg(v_x_819_, v_x_820_, v_inst_821_, v_m_822_, v_a_823_);
lean_dec(v_m_822_);
lean_dec(v_inst_821_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_m_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_827_, v_x_828_, v_inst_831_, v_m_832_, v_a_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_ExtHashMap_getKey_x21(v_00_u03b1_835_, v_00_u03b2_836_, v_x_837_, v_x_838_, v_inst_839_, v_inst_840_, v_inst_841_, v_m_842_, v_a_843_);
lean_dec(v_m_842_);
lean_dec(v_inst_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase___redArg(lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_845_, v_x_846_, v_m_847_, v_a_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_852_, v_x_853_, v_m_856_, v_a_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg(lean_object* v_m_859_){
_start:
{
lean_object* v_size_860_; 
v_size_860_ = lean_ctor_get(v_m_859_, 0);
lean_inc(v_size_860_);
return v_size_860_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg___boxed(lean_object* v_m_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_ExtHashMap_size___redArg(v_m_861_);
lean_dec(v_m_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_m_869_){
_start:
{
lean_object* v_size_870_; 
v_size_870_ = lean_ctor_get(v_m_869_, 0);
lean_inc(v_size_870_);
return v_size_870_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___boxed(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_m_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_ExtHashMap_size(v_00_u03b1_871_, v_00_u03b2_872_, v_x_873_, v_x_874_, v_inst_875_, v_inst_876_, v_m_877_);
lean_dec(v_m_877_);
lean_dec_ref(v_x_874_);
lean_dec_ref(v_x_873_);
return v_res_878_;
}
}
uint8_t l_Std_ExtHashMap_isEmpty___redArg(lean_object* v_m_879_){
_start:
{
lean_object* v_size_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_size_880_ = lean_ctor_get(v_m_879_, 0);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_nat_dec_eq(v_size_880_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_879_ = stack[0].m_obj;
uint8_t v_res_883_;
v_res_883_ = l_Std_ExtHashMap_isEmpty___redArg(v_m_879_);
stack->m_num = v_res_883_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___redArg___boxed(lean_object* v_m_884_){
_start:
{
uint8_t v_res_885_; lean_object* v_r_886_; 
v_res_885_ = l_Std_ExtHashMap_isEmpty___redArg(v_m_884_);
lean_dec(v_m_884_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
uint8_t l_Std_ExtHashMap_isEmpty(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_m_893_){
_start:
{
lean_object* v_size_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_size_894_ = lean_ctor_get(v_m_893_, 0);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v_size_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_889_ = stack[2].m_obj;
lean_object* v_x_890_ = stack[3].m_obj;
lean_object* v_m_893_ = stack[6].m_obj;
uint8_t v_res_897_;
v_res_897_ = l_Std_ExtHashMap_isEmpty(lean_box(0), lean_box(0), v_x_889_, v_x_890_, lean_box(0), lean_box(0), v_m_893_);
stack->m_num = v_res_897_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___boxed(lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_m_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_Std_ExtHashMap_isEmpty(v_00_u03b1_898_, v_00_u03b2_899_, v_x_900_, v_x_901_, v_inst_902_, v_inst_903_, v_m_904_);
lean_dec(v_m_904_);
lean_dec_ref(v_x_901_);
lean_dec_ref(v_x_900_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList___redArg(lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_l_932_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___f_933_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_934_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_933_, v_inst_930_, v_inst_931_, v___x_934_, v_l_932_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_l_940_){
_start:
{
lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___f_941_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_942_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_941_, v_inst_938_, v_inst_939_, v___x_942_, v_l_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList___redArg(lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_l_946_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___f_947_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_948_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_947_, v_inst_944_, v_inst_945_, v___x_948_, v_l_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_l_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___f_954_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_955_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_954_, v_inst_951_, v_inst_952_, v___x_955_, v_l_953_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg(lean_object* v_f_957_, lean_object* v_m_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_957_, v_m_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_f_966_, lean_object* v_m_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_966_, v_m_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___boxed(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_f_975_, lean_object* v_m_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_ExtHashMap_filter(v_00_u03b1_969_, v_00_u03b2_970_, v_x_971_, v_x_972_, v_inst_973_, v_inst_974_, v_f_975_, v_m_976_);
lean_dec_ref(v_x_972_);
lean_dec_ref(v_x_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg(lean_object* v_f_978_, lean_object* v_m_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_978_, v_m_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map(lean_object* v_00_u03b1_981_, lean_object* v_00_u03b2_982_, lean_object* v_00_u03b3_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_m_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_988_, v_m_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___boxed(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_00_u03b3_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_f_998_, lean_object* v_m_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_ExtHashMap_map(v_00_u03b1_991_, v_00_u03b2_992_, v_00_u03b3_993_, v_x_994_, v_x_995_, v_inst_996_, v_inst_997_, v_f_998_, v_m_999_);
lean_dec_ref(v_x_995_);
lean_dec_ref(v_x_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg(lean_object* v_f_1001_, lean_object* v_m_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1001_, v_m_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_00_u03b3_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_f_1011_, lean_object* v_m_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1011_, v_m_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_00_u03b3_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_f_1021_, lean_object* v_m_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_ExtHashMap_filterMap(v_00_u03b1_1014_, v_00_u03b2_1015_, v_00_u03b3_1016_, v_x_1017_, v_x_1018_, v_inst_1019_, v_inst_1020_, v_f_1021_, v_m_1022_);
lean_dec_ref(v_x_1018_);
lean_dec_ref(v_x_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify___redArg(lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_m_1026_, lean_object* v_a_1027_, lean_object* v_f_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1024_, v_x_1025_, v_m_1026_, v_a_1027_, v_f_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_m_1036_, lean_object* v_a_1037_, lean_object* v_f_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1032_, v_x_1033_, v_m_1036_, v_a_1037_, v_f_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter___redArg(lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_m_1042_, lean_object* v_a_1043_, lean_object* v_f_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1040_, v_x_1041_, v_m_1042_, v_a_1043_, v_f_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_m_1052_, lean_object* v_a_1053_, lean_object* v_f_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1048_, v_x_1049_, v_m_1052_, v_a_1053_, v_f_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg___lam__0(lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v_____s_1059_){
_start:
{
lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v_m_1062_; lean_object* v___x_1063_; 
v_fst_1060_ = lean_ctor_get(v_x_1058_, 0);
lean_inc(v_fst_1060_);
v_snd_1061_ = lean_ctor_get(v_x_1058_, 1);
lean_inc(v_snd_1061_);
lean_dec_ref(v_x_1058_);
v_m_1062_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1056_, v_x_1057_, v_____s_1059_, v_fst_1060_, v_snd_1061_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_m_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg(lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_inst_1066_, lean_object* v_m_1067_, lean_object* v_l_1068_){
_start:
{
lean_object* v___f_1069_; lean_object* v___x_1070_; 
v___f_1069_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1069_, 0, v_x_1064_);
lean_closure_set(v___f_1069_, 1, v_x_1065_);
v___x_1070_ = lean_apply_4(v_inst_1066_, lean_box(0), v_l_1068_, v_m_1067_, v___f_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_00_u03c1_1077_, lean_object* v_inst_1078_, lean_object* v_m_1079_, lean_object* v_l_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; 
v___f_1081_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1081_, 0, v_x_1073_);
lean_closure_set(v___f_1081_, 1, v_x_1074_);
v___x_1082_ = lean_apply_4(v_inst_1078_, lean_box(0), v_l_1080_, v_m_1079_, v___f_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_a_1085_, lean_object* v_____s_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v_m_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
v_m_1088_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1083_, v_x_1084_, v_____s_1086_, v_a_1085_, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_m_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_inst_1092_, lean_object* v_m_1093_, lean_object* v_l_1094_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1095_, 0, v_x_1090_);
lean_closure_set(v___f_1095_, 1, v_x_1091_);
v___x_1096_ = lean_apply_4(v_inst_1092_, lean_box(0), v_l_1094_, v_m_1093_, v___f_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_00_u03c1_1102_, lean_object* v_inst_1103_, lean_object* v_m_1104_, lean_object* v_l_1105_){
_start:
{
lean_object* v___f_1106_; lean_object* v___x_1107_; 
v___f_1106_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1106_, 0, v_x_1098_);
lean_closure_set(v___f_1106_, 1, v_x_1099_);
v___x_1107_ = lean_apply_4(v_inst_1103_, lean_box(0), v_l_1105_, v_m_1104_, v___f_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__0(lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_a_1110_, lean_object* v_b_1111_, lean_object* v_acc_1112_){
_start:
{
lean_object* v_r_1113_; lean_object* v___x_1114_; 
v_r_1113_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1108_, v_x_1109_, v_acc_1112_, v_a_1110_, v_b_1111_);
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_r_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__1(lean_object* v___x_1115_, lean_object* v___f_1116_, lean_object* v_a_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1115_, v___f_1116_, v_a_1117_, v___y_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg(lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_m_u2081_1125_, lean_object* v_m_u2082_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v_size_1128_; lean_object* v_buckets_1129_; lean_object* v_size_1130_; uint8_t v___x_1131_; 
v___x_1127_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v_size_1128_ = lean_ctor_get(v_m_u2081_1125_, 0);
v_buckets_1129_ = lean_ctor_get(v_m_u2081_1125_, 1);
v_size_1130_ = lean_ctor_get(v_m_u2082_1126_, 0);
v___x_1131_ = lean_nat_dec_le(v_size_1128_, v_size_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1132_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1132_, v_x_1123_, v_x_1124_, v_m_u2081_1125_, v_m_u2082_1126_);
return v___x_1133_;
}
else
{
lean_object* v___f_1134_; lean_object* v___f_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
lean_inc_ref(v_buckets_1129_);
lean_dec(v_m_u2081_1125_);
v___f_1134_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1134_, 0, v_x_1123_);
lean_closure_set(v___f_1134_, 1, v_x_1124_);
v___f_1135_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1135_, 0, v___x_1127_);
lean_closure_set(v___f_1135_, 1, v___f_1134_);
v_sz_1136_ = lean_array_size(v_buckets_1129_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1127_, v_buckets_1129_, v___f_1135_, v_sz_1136_, v___x_1137_, v_m_u2082_1126_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_m_u2081_1145_, lean_object* v_m_u2082_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v_size_1148_; lean_object* v_buckets_1149_; lean_object* v_size_1150_; uint8_t v___x_1151_; 
v___x_1147_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v_size_1148_ = lean_ctor_get(v_m_u2081_1145_, 0);
v_buckets_1149_ = lean_ctor_get(v_m_u2081_1145_, 1);
v_size_1150_ = lean_ctor_get(v_m_u2082_1146_, 0);
v___x_1151_ = lean_nat_dec_le(v_size_1148_, v_size_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___f_1152_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1152_, v_x_1141_, v_x_1142_, v_m_u2081_1145_, v_m_u2082_1146_);
return v___x_1153_;
}
else
{
lean_object* v___f_1154_; lean_object* v___f_1155_; size_t v_sz_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
lean_inc_ref(v_buckets_1149_);
lean_dec(v_m_u2081_1145_);
v___f_1154_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1154_, 0, v_x_1141_);
lean_closure_set(v___f_1154_, 1, v_x_1142_);
v___f_1155_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1155_, 0, v___x_1147_);
lean_closure_set(v___f_1155_, 1, v___f_1154_);
v_sz_1156_ = lean_array_size(v_buckets_1149_);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1147_, v_buckets_1149_, v___f_1155_, v_sz_1156_, v___x_1157_, v_m_u2082_1146_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_1161_, 0, lean_box(0));
lean_closure_set(v___x_1161_, 1, lean_box(0));
lean_closure_set(v___x_1161_, 2, v_x_1159_);
lean_closure_set(v___x_1161_, 3, v_x_1160_);
lean_closure_set(v___x_1161_, 4, lean_box(0));
lean_closure_set(v___x_1161_, 5, lean_box(0));
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_1168_, 0, lean_box(0));
lean_closure_set(v___x_1168_, 1, lean_box(0));
lean_closure_set(v___x_1168_, 2, v_x_1164_);
lean_closure_set(v___x_1168_, 3, v_x_1165_);
lean_closure_set(v___x_1168_, 4, lean_box(0));
lean_closure_set(v___x_1168_, 5, lean_box(0));
return v___x_1168_;
}
}
uint8_t l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_inst_1171_, lean_object* v_m_u2081_1172_, lean_object* v_m_u2082_1173_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1169_, v_x_1170_, v_inst_1171_, v_m_u2081_1172_, v_m_u2082_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1169_ = stack[0].m_obj;
lean_object* v_x_1170_ = stack[1].m_obj;
lean_object* v_inst_1171_ = stack[2].m_obj;
lean_object* v_m_u2081_1172_ = stack[3].m_obj;
lean_object* v_m_u2082_1173_ = stack[4].m_obj;
uint8_t v_res_1175_;
v_res_1175_ = l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_1169_, v_x_1170_, v_inst_1171_, v_m_u2081_1172_, v_m_u2082_1173_);
stack->m_num = v_res_1175_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_inst_1178_, lean_object* v_m_u2081_1179_, lean_object* v_m_u2082_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_1176_, v_x_1177_, v_inst_1178_, v_m_u2081_1179_, v_m_u2082_1180_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v___f_1186_; 
v___f_1186_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1186_, 0, v_x_1183_);
lean_closure_set(v___f_1186_, 1, v_x_1184_);
lean_closure_set(v___f_1186_, 2, v_inst_1185_);
return v___f_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1187_, lean_object* v_00_u03b2_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v___f_1194_; 
v___f_1194_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1194_, 0, v_x_1189_);
lean_closure_set(v___f_1194_, 1, v_x_1190_);
lean_closure_set(v___f_1194_, 2, v_inst_1193_);
return v___f_1194_;
}
}
uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1195_, v_inst_1196_, v_inst_1197_, v_x_1198_, v_x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1195_ = stack[0].m_obj;
lean_object* v_inst_1196_ = stack[1].m_obj;
lean_object* v_inst_1197_ = stack[2].m_obj;
lean_object* v_x_1198_ = stack[3].m_obj;
lean_object* v_x_1199_ = stack[4].m_obj;
uint8_t v_res_1201_;
v_res_1201_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1195_, v_inst_1196_, v_inst_1197_, v_x_1198_, v_x_1199_);
stack->m_num = v_res_1201_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1202_, v_inst_1203_, v_inst_1204_, v_x_1205_, v_x_1206_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_){
_start:
{
uint8_t v___x_1218_; 
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1211_, v_inst_1213_, v_inst_1214_, v_x_1216_, v_x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT void l_Std_ExtHashMap_instDecidableEqOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1211_ = stack[2].m_obj;
lean_object* v_inst_1213_ = stack[4].m_obj;
lean_object* v_inst_1214_ = stack[5].m_obj;
lean_object* v_x_1216_ = stack[7].m_obj;
lean_object* v_x_1217_ = stack[8].m_obj;
uint8_t v_res_1219_;
v_res_1219_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(lean_box(0), lean_box(0), v_inst_1211_, lean_box(0), v_inst_1213_, v_inst_1214_, lean_box(0), v_x_1216_, v_x_1217_);
stack->m_num = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_1220_, v_00_u03b2_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_inst_1225_, v_inst_1226_, v_x_1227_, v_x_1228_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter___redArg(lean_object* v_x_1231_, lean_object* v_x_1232_, lean_object* v_m_u2081_1233_, lean_object* v_m_u2082_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1231_, v_x_1232_, v_m_u2081_1233_, v_m_u2082_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b2_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_m_u2081_1242_, lean_object* v_m_u2082_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1238_, v_x_1239_, v_m_u2081_1242_, v_m_u2082_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_1247_, 0, lean_box(0));
lean_closure_set(v___x_1247_, 1, lean_box(0));
lean_closure_set(v___x_1247_, 2, v_x_1245_);
lean_closure_set(v___x_1247_, 3, v_x_1246_);
lean_closure_set(v___x_1247_, 4, lean_box(0));
lean_closure_set(v___x_1247_, 5, lean_box(0));
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_1254_, 0, lean_box(0));
lean_closure_set(v___x_1254_, 1, lean_box(0));
lean_closure_set(v___x_1254_, 2, v_x_1250_);
lean_closure_set(v___x_1254_, 3, v_x_1251_);
lean_closure_set(v___x_1254_, 4, lean_box(0));
lean_closure_set(v___x_1254_, 5, lean_box(0));
return v___x_1254_;
}
}
uint8_t l_Std_ExtHashMap_diff___redArg___lam__0(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_m_u2082_1257_, uint8_t v___x_1258_, lean_object* v_k_1259_, lean_object* v_x_1260_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1255_, v_x_1256_, v_m_u2082_1257_, v_k_1259_);
if (v___x_1261_ == 0)
{
return v___x_1258_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = 0;
return v___x_1262_;
}
}
}
LEAN_EXPORT void l_Std_ExtHashMap_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1255_ = stack[0].m_obj;
lean_object* v_x_1256_ = stack[1].m_obj;
lean_object* v_m_u2082_1257_ = stack[2].m_obj;
uint8_t v___x_1258_ = stack[3].m_num;
lean_object* v_k_1259_ = stack[4].m_obj;
lean_object* v_x_1260_ = stack[5].m_obj;
uint8_t v_res_1263_;
v_res_1263_ = l_Std_ExtHashMap_diff___redArg___lam__0(v_x_1255_, v_x_1256_, v_m_u2082_1257_, v___x_1258_, v_k_1259_, v_x_1260_);
stack->m_num = v_res_1263_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_m_u2082_1266_, lean_object* v___x_1267_, lean_object* v_k_1268_, lean_object* v_x_1269_){
_start:
{
uint8_t v___x_107__boxed_1270_; uint8_t v_res_1271_; lean_object* v_r_1272_; 
v___x_107__boxed_1270_ = lean_unbox(v___x_1267_);
v_res_1271_ = l_Std_ExtHashMap_diff___redArg___lam__0(v_x_1264_, v_x_1265_, v_m_u2082_1266_, v___x_107__boxed_1270_, v_k_1268_, v_x_1269_);
lean_dec(v_x_1269_);
lean_dec(v_m_u2082_1266_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg(lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_m_u2081_1275_, lean_object* v_m_u2082_1276_){
_start:
{
lean_object* v_size_1277_; lean_object* v_size_1278_; uint8_t v___x_1279_; 
v_size_1277_ = lean_ctor_get(v_m_u2081_1275_, 0);
v_size_1278_ = lean_ctor_get(v_m_u2082_1276_, 0);
v___x_1279_ = lean_nat_dec_le(v_size_1277_, v_size_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___f_1280_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1280_, v_x_1273_, v_x_1274_, v_m_u2081_1275_, v_m_u2082_1276_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(v___x_1279_);
v___f_1283_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1283_, 0, v_x_1273_);
lean_closure_set(v___f_1283_, 1, v_x_1274_);
lean_closure_set(v___f_1283_, 2, v_m_u2082_1276_);
lean_closure_set(v___f_1283_, 3, v___x_1282_);
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1283_, v_m_u2081_1275_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_m_u2081_1291_, lean_object* v_m_u2082_1292_){
_start:
{
lean_object* v_size_1293_; lean_object* v_size_1294_; uint8_t v___x_1295_; 
v_size_1293_ = lean_ctor_get(v_m_u2081_1291_, 0);
v_size_1294_ = lean_ctor_get(v_m_u2082_1292_, 0);
v___x_1295_ = lean_nat_dec_le(v_size_1293_, v_size_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___f_1296_; lean_object* v___x_1297_; 
v___f_1296_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1296_, v_x_1287_, v_x_1288_, v_m_u2081_1291_, v_m_u2082_1292_);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_box(v___x_1295_);
v___f_1299_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1299_, 0, v_x_1287_);
lean_closure_set(v___f_1299_, 1, v_x_1288_);
lean_closure_set(v___f_1299_, 2, v_m_u2082_1292_);
lean_closure_set(v___f_1299_, 3, v___x_1298_);
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1299_, v_m_u2081_1291_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_1303_, 0, lean_box(0));
lean_closure_set(v___x_1303_, 1, lean_box(0));
lean_closure_set(v___x_1303_, 2, v_x_1301_);
lean_closure_set(v___x_1303_, 3, v_x_1302_);
lean_closure_set(v___x_1303_, 4, lean_box(0));
lean_closure_set(v___x_1303_, 5, lean_box(0));
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_1310_, 0, lean_box(0));
lean_closure_set(v___x_1310_, 1, lean_box(0));
lean_closure_set(v___x_1310_, 2, v_x_1306_);
lean_closure_set(v___x_1310_, 3, v_x_1307_);
lean_closure_set(v___x_1310_, 4, lean_box(0));
lean_closure_set(v___x_1310_, 5, lean_box(0));
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray___redArg(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_l_1317_){
_start:
{
lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___f_1318_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_1319_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1318_, v_inst_1315_, v_inst_1316_, v___x_1319_, v_l_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray(lean_object* v_00_u03b1_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_l_1324_){
_start:
{
lean_object* v___f_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___f_1325_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_1326_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___redArg___closed__1);
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1325_, v_inst_1322_, v_inst_1323_, v___x_1326_, v_l_1324_);
return v___x_1327_;
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
