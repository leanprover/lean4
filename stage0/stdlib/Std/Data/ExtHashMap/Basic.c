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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___closed__1;
static lean_once_cell_t l_Std_ExtHashMap_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instEmptyCollection___closed__2;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3;
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
static lean_once_cell_t l_Std_ExtHashMap_unitOfList___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_unitOfList___redArg___closed__0;
static lean_once_cell_t l_Std_ExtHashMap_unitOfList___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashMap_unitOfList___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_ExtHashMap_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashMap_ofList___redArg___closed__9_value)} };
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
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_ExtHashMap_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_capacity_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_cellCount_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_20_ = lean_unsigned_to_nat(4u);
v___x_21_ = lean_nat_mul(v_capacity_19_, v___x_20_);
v___x_22_ = lean_unsigned_to_nat(2u);
v___x_23_ = lean_nat_add(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_unsigned_to_nat(3u);
v___x_25_ = lean_nat_div(v___x_23_, v___x_24_);
lean_dec(v___x_23_);
v_cellCount_26_ = l_Nat_nextPowerOfTwo(v___x_25_);
lean_dec(v___x_25_);
v___x_27_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_26_);
v___x_28_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_26_);
v___x_29_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_26_);
v___x_30_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_30_, 0, v___x_27_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_emptyWithCapacity___boxed(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_capacity_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_ExtHashMap_emptyWithCapacity(v_00_u03b1_31_, v_00_u03b2_32_, v_inst_33_, v_inst_34_, v_capacity_35_);
lean_dec(v_capacity_35_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_36_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_37_; lean_object* v___x_38_; 
v_cellCount_37_ = lean_unsigned_to_nat(16u);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_39_; lean_object* v___x_40_; 
v_cellCount_39_ = lean_unsigned_to_nat(16u);
v___x_40_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__1, &l_Std_ExtHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__1);
v___x_42_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__0, &l_Std_ExtHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__0);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instEmptyCollection(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__2, &l_Std_ExtHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__2);
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
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_inst_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__2, &l_Std_ExtHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__2);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInhabited___boxed(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_, lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_ExtHashMap_instInhabited(v_00_u03b1_60_, v_00_u03b2_61_, v_inst_62_, v_inst_63_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert___redArg(lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_m_67_, lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
lean_object* v___y_71_; lean_object* v_i_72_; lean_object* v___y_88_; lean_object* v_i_89_; lean_object* v___y_95_; lean_object* v___x_104_; 
lean_inc(v_a_68_);
lean_inc_ref(v_x_66_);
lean_inc_ref(v_x_65_);
v___x_104_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_65_, v_x_66_, v_m_67_, v_a_68_);
switch(lean_obj_tag(v___x_104_))
{
case 0:
{
lean_object* v_index_105_; lean_object* v_size_106_; lean_object* v___x_107_; 
lean_dec_ref(v_x_66_);
lean_dec_ref(v_x_65_);
v_index_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_index_105_);
lean_dec_ref_known(v___x_104_, 3);
v_size_106_ = lean_ctor_get(v_m_67_, 0);
lean_inc(v_size_106_);
v___x_107_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_67_, v_size_106_, v_index_105_, v_a_68_, v_b_69_);
lean_dec(v_index_105_);
return v___x_107_;
}
case 1:
{
lean_object* v_index_108_; lean_object* v_size_109_; lean_object* v_keyArray_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_index_108_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_index_108_);
lean_dec_ref_known(v___x_104_, 1);
v_size_109_ = lean_ctor_get(v_m_67_, 0);
v_keyArray_110_ = lean_ctor_get(v_m_67_, 1);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_size_109_, v___x_111_);
v___x_113_ = lean_array_get_size(v_keyArray_110_);
v___x_114_ = lean_nat_dec_lt(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec(v___x_112_);
lean_dec(v_index_108_);
goto v___jp_77_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_115_ = lean_unsigned_to_nat(4u);
v___x_116_ = lean_nat_mul(v___x_112_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_118_ = lean_nat_mul(v___x_113_, v___x_117_);
v___x_119_ = lean_nat_dec_le(v___x_116_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_116_);
if (v___x_119_ == 0)
{
lean_dec(v___x_112_);
lean_dec(v_index_108_);
goto v___jp_77_;
}
else
{
lean_object* v___x_120_; 
lean_dec_ref(v_x_66_);
lean_dec_ref(v_x_65_);
v___x_120_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_67_, v___x_112_, v_index_108_, v_a_68_, v_b_69_);
lean_dec(v_index_108_);
return v___x_120_;
}
}
}
default: 
{
lean_object* v_size_121_; lean_object* v_keyArray_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_size_121_ = lean_ctor_get(v_m_67_, 0);
v_keyArray_122_ = lean_ctor_get(v_m_67_, 1);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_size_121_, v___x_123_);
v___x_125_ = lean_array_get_size(v_keyArray_122_);
v___x_126_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_124_);
lean_inc_ref(v_x_66_);
lean_inc_ref(v_x_65_);
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_65_, v_x_66_, v_m_67_);
v___y_95_ = v___x_127_;
goto v___jp_94_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_mul(v___x_124_, v___x_128_);
lean_dec(v___x_124_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = lean_nat_mul(v___x_125_, v___x_130_);
v___x_132_ = lean_nat_dec_le(v___x_129_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_129_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_inc_ref(v_x_66_);
lean_inc_ref(v_x_65_);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_65_, v_x_66_, v_m_67_);
v___y_95_ = v___x_133_;
goto v___jp_94_;
}
else
{
v___y_95_ = v_m_67_;
goto v___jp_94_;
}
}
}
}
v___jp_70_:
{
lean_object* v_size_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_size_73_ = lean_ctor_get(v___y_71_, 0);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_size_73_, v___x_74_);
v___x_76_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_71_, v___x_75_, v_i_72_, v_a_68_, v_b_69_);
lean_dec(v_i_72_);
return v___x_76_;
}
v___jp_77_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_inc_ref(v_x_66_);
lean_inc_ref(v_x_65_);
v___x_78_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_65_, v_x_66_, v_m_67_);
lean_inc(v_a_68_);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_65_, v_x_66_, v___x_78_, v_a_68_);
switch(lean_obj_tag(v___x_79_))
{
case 0:
{
lean_object* v_index_80_; lean_object* v_size_81_; lean_object* v___x_82_; 
v_index_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_index_80_);
lean_dec_ref_known(v___x_79_, 3);
v_size_81_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_size_81_);
v___x_82_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_78_, v_size_81_, v_index_80_, v_a_68_, v_b_69_);
lean_dec(v_index_80_);
return v___x_82_;
}
case 1:
{
lean_object* v_index_83_; 
v_index_83_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_index_83_);
lean_dec_ref_known(v___x_79_, 1);
v___y_71_ = v___x_78_;
v_i_72_ = v_index_83_;
goto v___jp_70_;
}
default: 
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_78_, v___x_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_index_86_; 
v_index_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_index_86_);
lean_dec_ref_known(v___x_85_, 1);
v___y_71_ = v___x_78_;
v_i_72_ = v_index_86_;
goto v___jp_70_;
}
else
{
lean_dec(v_b_69_);
lean_dec(v_a_68_);
return v___x_78_;
}
}
}
}
v___jp_87_:
{
lean_object* v_size_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_size_90_ = lean_ctor_get(v___y_88_, 0);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_size_90_, v___x_91_);
v___x_93_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_88_, v___x_92_, v_i_89_, v_a_68_, v_b_69_);
lean_dec(v_i_89_);
return v___x_93_;
}
v___jp_94_:
{
lean_object* v___x_96_; 
lean_inc(v_a_68_);
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_65_, v_x_66_, v___y_95_, v_a_68_);
switch(lean_obj_tag(v___x_96_))
{
case 0:
{
lean_object* v_index_97_; lean_object* v_size_98_; lean_object* v___x_99_; 
v_index_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_index_97_);
lean_dec_ref_known(v___x_96_, 3);
v_size_98_ = lean_ctor_get(v___y_95_, 0);
lean_inc(v_size_98_);
v___x_99_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_95_, v_size_98_, v_index_97_, v_a_68_, v_b_69_);
lean_dec(v_index_97_);
return v___x_99_;
}
case 1:
{
lean_object* v_index_100_; 
v_index_100_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_index_100_);
lean_dec_ref_known(v___x_96_, 1);
v___y_88_ = v___y_95_;
v_i_89_ = v_index_100_;
goto v___jp_87_;
}
default: 
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_95_, v___x_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_index_103_; 
v_index_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_index_103_);
lean_dec_ref_known(v___x_102_, 1);
v___y_88_ = v___y_95_;
v_i_89_ = v_index_103_;
goto v___jp_87_;
}
else
{
lean_dec(v_b_69_);
lean_dec(v_a_68_);
return v___y_95_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insert(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_m_140_, lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
lean_object* v___y_144_; lean_object* v_i_145_; lean_object* v___y_161_; lean_object* v_i_162_; lean_object* v___y_168_; lean_object* v___x_177_; 
lean_inc(v_a_141_);
lean_inc_ref(v_x_137_);
lean_inc_ref(v_x_136_);
v___x_177_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_136_, v_x_137_, v_m_140_, v_a_141_);
switch(lean_obj_tag(v___x_177_))
{
case 0:
{
lean_object* v_index_178_; lean_object* v_size_179_; lean_object* v___x_180_; 
lean_dec_ref(v_x_137_);
lean_dec_ref(v_x_136_);
v_index_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_index_178_);
lean_dec_ref_known(v___x_177_, 3);
v_size_179_ = lean_ctor_get(v_m_140_, 0);
lean_inc(v_size_179_);
v___x_180_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_140_, v_size_179_, v_index_178_, v_a_141_, v_b_142_);
lean_dec(v_index_178_);
return v___x_180_;
}
case 1:
{
lean_object* v_index_181_; lean_object* v_size_182_; lean_object* v_keyArray_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_index_181_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_index_181_);
lean_dec_ref_known(v___x_177_, 1);
v_size_182_ = lean_ctor_get(v_m_140_, 0);
v_keyArray_183_ = lean_ctor_get(v_m_140_, 1);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_size_182_, v___x_184_);
v___x_186_ = lean_array_get_size(v_keyArray_183_);
v___x_187_ = lean_nat_dec_lt(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v___x_185_);
lean_dec(v_index_181_);
goto v___jp_150_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_188_ = lean_unsigned_to_nat(4u);
v___x_189_ = lean_nat_mul(v___x_185_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(3u);
v___x_191_ = lean_nat_mul(v___x_186_, v___x_190_);
v___x_192_ = lean_nat_dec_le(v___x_189_, v___x_191_);
lean_dec(v___x_191_);
lean_dec(v___x_189_);
if (v___x_192_ == 0)
{
lean_dec(v___x_185_);
lean_dec(v_index_181_);
goto v___jp_150_;
}
else
{
lean_object* v___x_193_; 
lean_dec_ref(v_x_137_);
lean_dec_ref(v_x_136_);
v___x_193_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_140_, v___x_185_, v_index_181_, v_a_141_, v_b_142_);
lean_dec(v_index_181_);
return v___x_193_;
}
}
}
default: 
{
lean_object* v_size_194_; lean_object* v_keyArray_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_size_194_ = lean_ctor_get(v_m_140_, 0);
v_keyArray_195_ = lean_ctor_get(v_m_140_, 1);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_size_194_, v___x_196_);
v___x_198_ = lean_array_get_size(v_keyArray_195_);
v___x_199_ = lean_nat_dec_lt(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec(v___x_197_);
lean_inc_ref(v_x_137_);
lean_inc_ref(v_x_136_);
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_136_, v_x_137_, v_m_140_);
v___y_168_ = v___x_200_;
goto v___jp_167_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_201_ = lean_unsigned_to_nat(4u);
v___x_202_ = lean_nat_mul(v___x_197_, v___x_201_);
lean_dec(v___x_197_);
v___x_203_ = lean_unsigned_to_nat(3u);
v___x_204_ = lean_nat_mul(v___x_198_, v___x_203_);
v___x_205_ = lean_nat_dec_le(v___x_202_, v___x_204_);
lean_dec(v___x_204_);
lean_dec(v___x_202_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_inc_ref(v_x_137_);
lean_inc_ref(v_x_136_);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_136_, v_x_137_, v_m_140_);
v___y_168_ = v___x_206_;
goto v___jp_167_;
}
else
{
v___y_168_ = v_m_140_;
goto v___jp_167_;
}
}
}
}
v___jp_143_:
{
lean_object* v_size_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_size_146_ = lean_ctor_get(v___y_144_, 0);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_add(v_size_146_, v___x_147_);
v___x_149_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_144_, v___x_148_, v_i_145_, v_a_141_, v_b_142_);
lean_dec(v_i_145_);
return v___x_149_;
}
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_inc_ref(v_x_137_);
lean_inc_ref(v_x_136_);
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_136_, v_x_137_, v_m_140_);
lean_inc(v_a_141_);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_136_, v_x_137_, v___x_151_, v_a_141_);
switch(lean_obj_tag(v___x_152_))
{
case 0:
{
lean_object* v_index_153_; lean_object* v_size_154_; lean_object* v___x_155_; 
v_index_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_index_153_);
lean_dec_ref_known(v___x_152_, 3);
v_size_154_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_size_154_);
v___x_155_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_151_, v_size_154_, v_index_153_, v_a_141_, v_b_142_);
lean_dec(v_index_153_);
return v___x_155_;
}
case 1:
{
lean_object* v_index_156_; 
v_index_156_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_index_156_);
lean_dec_ref_known(v___x_152_, 1);
v___y_144_ = v___x_151_;
v_i_145_ = v_index_156_;
goto v___jp_143_;
}
default: 
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_151_, v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_index_159_; 
v_index_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_index_159_);
lean_dec_ref_known(v___x_158_, 1);
v___y_144_ = v___x_151_;
v_i_145_ = v_index_159_;
goto v___jp_143_;
}
else
{
lean_dec(v_b_142_);
lean_dec(v_a_141_);
return v___x_151_;
}
}
}
}
v___jp_160_:
{
lean_object* v_size_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_size_163_ = lean_ctor_get(v___y_161_, 0);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_add(v_size_163_, v___x_164_);
v___x_166_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_161_, v___x_165_, v_i_162_, v_a_141_, v_b_142_);
lean_dec(v_i_162_);
return v___x_166_;
}
v___jp_167_:
{
lean_object* v___x_169_; 
lean_inc(v_a_141_);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_136_, v_x_137_, v___y_168_, v_a_141_);
switch(lean_obj_tag(v___x_169_))
{
case 0:
{
lean_object* v_index_170_; lean_object* v_size_171_; lean_object* v___x_172_; 
v_index_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_index_170_);
lean_dec_ref_known(v___x_169_, 3);
v_size_171_ = lean_ctor_get(v___y_168_, 0);
lean_inc(v_size_171_);
v___x_172_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_168_, v_size_171_, v_index_170_, v_a_141_, v_b_142_);
lean_dec(v_index_170_);
return v___x_172_;
}
case 1:
{
lean_object* v_index_173_; 
v_index_173_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_index_173_);
lean_dec_ref_known(v___x_169_, 1);
v___y_161_ = v___y_168_;
v_i_162_ = v_index_173_;
goto v___jp_160_;
}
default: 
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_168_, v___x_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_index_176_; 
v_index_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_index_176_);
lean_dec_ref_known(v___x_175_, 1);
v___y_161_ = v___y_168_;
v_i_162_ = v_index_176_;
goto v___jp_160_;
}
else
{
lean_dec(v_b_142_);
lean_dec(v_a_141_);
return v___y_168_;
}
}
}
}
}
}
static lean_object* _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__0, &l_Std_ExtHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__0);
v___x_208_ = lean_array_get_size(v___x_207_);
return v___x_208_;
}
}
static uint8_t _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_obj_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_dec_lt(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_unsigned_to_nat(3u);
v___x_213_ = lean_obj_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_214_ = lean_nat_mul(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static uint8_t _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_215_ = lean_obj_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2);
v___x_216_ = lean_unsigned_to_nat(4u);
v___x_217_ = lean_nat_dec_le(v___x_216_, v___x_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___y_224_; lean_object* v_i_225_; lean_object* v___y_231_; lean_object* v_i_232_; lean_object* v___y_238_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_258_; 
v_fst_221_ = lean_ctor_get(v_x_220_, 0);
lean_inc_n(v_fst_221_, 2);
v_snd_222_ = lean_ctor_get(v_x_220_, 1);
lean_inc(v_snd_222_);
lean_dec_ref(v_x_220_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__2, &l_Std_ExtHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__2);
lean_inc_ref(v_x_219_);
lean_inc_ref(v_x_218_);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_218_, v_x_219_, v___x_248_, v_fst_221_);
switch(lean_obj_tag(v___x_258_))
{
case 0:
{
lean_object* v_index_259_; lean_object* v___x_260_; 
lean_dec_ref(v_x_219_);
lean_dec_ref(v_x_218_);
v_index_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_index_259_);
lean_dec_ref_known(v___x_258_, 3);
v___x_260_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_248_, v___x_247_, v_index_259_, v_fst_221_, v_snd_222_);
lean_dec(v_index_259_);
return v___x_260_;
}
case 1:
{
lean_object* v_index_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_index_261_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_index_261_);
lean_dec_ref_known(v___x_258_, 1);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_uint8_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1);
if (v___x_263_ == 0)
{
lean_dec(v_index_261_);
goto v___jp_249_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = lean_uint8_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3);
if (v___x_264_ == 0)
{
lean_dec(v_index_261_);
goto v___jp_249_;
}
else
{
lean_object* v___x_265_; 
lean_dec_ref(v_x_219_);
lean_dec_ref(v_x_218_);
v___x_265_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_248_, v___x_262_, v_index_261_, v_fst_221_, v_snd_222_);
lean_dec(v_index_261_);
return v___x_265_;
}
}
}
default: 
{
uint8_t v___x_266_; 
v___x_266_ = lean_uint8_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_inc_ref(v_x_219_);
lean_inc_ref(v_x_218_);
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_218_, v_x_219_, v___x_248_);
v___y_238_ = v___x_267_;
goto v___jp_237_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = lean_uint8_once(&l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3, &l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once, _init_l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_inc_ref(v_x_219_);
lean_inc_ref(v_x_218_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_218_, v_x_219_, v___x_248_);
v___y_238_ = v___x_269_;
goto v___jp_237_;
}
else
{
v___y_238_ = v___x_248_;
goto v___jp_237_;
}
}
}
}
v___jp_223_:
{
lean_object* v_size_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_size_226_ = lean_ctor_get(v___y_224_, 0);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_size_226_, v___x_227_);
v___x_229_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_224_, v___x_228_, v_i_225_, v_fst_221_, v_snd_222_);
lean_dec(v_i_225_);
return v___x_229_;
}
v___jp_230_:
{
lean_object* v_size_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_size_233_ = lean_ctor_get(v___y_231_, 0);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_size_233_, v___x_234_);
v___x_236_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_231_, v___x_235_, v_i_232_, v_fst_221_, v_snd_222_);
lean_dec(v_i_232_);
return v___x_236_;
}
v___jp_237_:
{
lean_object* v___x_239_; 
lean_inc(v_fst_221_);
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_218_, v_x_219_, v___y_238_, v_fst_221_);
switch(lean_obj_tag(v___x_239_))
{
case 0:
{
lean_object* v_index_240_; lean_object* v_size_241_; lean_object* v___x_242_; 
v_index_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_index_240_);
lean_dec_ref_known(v___x_239_, 3);
v_size_241_ = lean_ctor_get(v___y_238_, 0);
lean_inc(v_size_241_);
v___x_242_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_238_, v_size_241_, v_index_240_, v_fst_221_, v_snd_222_);
lean_dec(v_index_240_);
return v___x_242_;
}
case 1:
{
lean_object* v_index_243_; 
v_index_243_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_index_243_);
lean_dec_ref_known(v___x_239_, 1);
v___y_231_ = v___y_238_;
v_i_232_ = v_index_243_;
goto v___jp_230_;
}
default: 
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_238_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_index_246_; 
v_index_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_index_246_);
lean_dec_ref_known(v___x_245_, 1);
v___y_231_ = v___y_238_;
v_i_232_ = v_index_246_;
goto v___jp_230_;
}
else
{
lean_dec(v_snd_222_);
lean_dec(v_fst_221_);
return v___y_238_;
}
}
}
}
v___jp_249_:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_inc_ref(v_x_219_);
lean_inc_ref(v_x_218_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_218_, v_x_219_, v___x_248_);
lean_inc(v_fst_221_);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_218_, v_x_219_, v___x_250_, v_fst_221_);
switch(lean_obj_tag(v___x_251_))
{
case 0:
{
lean_object* v_index_252_; lean_object* v_size_253_; lean_object* v___x_254_; 
v_index_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_index_252_);
lean_dec_ref_known(v___x_251_, 3);
v_size_253_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_size_253_);
v___x_254_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_250_, v_size_253_, v_index_252_, v_fst_221_, v_snd_222_);
lean_dec(v_index_252_);
return v___x_254_;
}
case 1:
{
lean_object* v_index_255_; 
v_index_255_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_index_255_);
lean_dec_ref_known(v___x_251_, 1);
v___y_224_ = v___x_250_;
v_i_225_ = v_index_255_;
goto v___jp_223_;
}
default: 
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_250_, v___x_247_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_index_257_; 
v_index_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_index_257_);
lean_dec_ref_known(v___x_256_, 1);
v___y_224_ = v___x_250_;
v_i_225_ = v_index_257_;
goto v___jp_223_;
}
else
{
lean_dec(v_snd_222_);
lean_dec(v_fst_221_);
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___f_272_; 
v___f_272_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_272_, 0, v_x_270_);
lean_closure_set(v___f_272_, 1, v_x_271_);
return v___f_272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_inst_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___f_279_; 
v___f_279_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_279_, 0, v_x_275_);
lean_closure_set(v___f_279_, 1, v_x_276_);
return v___f_279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v_fst_284_; lean_object* v_snd_285_; lean_object* v___y_287_; lean_object* v_i_288_; lean_object* v___y_294_; lean_object* v___y_304_; lean_object* v_i_305_; lean_object* v___x_320_; 
v_fst_284_ = lean_ctor_get(v_x_282_, 0);
lean_inc_n(v_fst_284_, 2);
v_snd_285_ = lean_ctor_get(v_x_282_, 1);
lean_inc(v_snd_285_);
lean_dec_ref(v_x_282_);
lean_inc_ref(v_x_281_);
lean_inc_ref(v_x_280_);
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_280_, v_x_281_, v_x_283_, v_fst_284_);
switch(lean_obj_tag(v___x_320_))
{
case 0:
{
lean_object* v_index_321_; lean_object* v_size_322_; lean_object* v___x_323_; 
lean_dec_ref(v_x_281_);
lean_dec_ref(v_x_280_);
v_index_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_index_321_);
lean_dec_ref_known(v___x_320_, 3);
v_size_322_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_size_322_);
v___x_323_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_283_, v_size_322_, v_index_321_, v_fst_284_, v_snd_285_);
lean_dec(v_index_321_);
return v___x_323_;
}
case 1:
{
lean_object* v_index_324_; lean_object* v_size_325_; lean_object* v_keyArray_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_index_324_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_index_324_);
lean_dec_ref_known(v___x_320_, 1);
v_size_325_ = lean_ctor_get(v_x_283_, 0);
v_keyArray_326_ = lean_ctor_get(v_x_283_, 1);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_size_325_, v___x_327_);
v___x_329_ = lean_array_get_size(v_keyArray_326_);
v___x_330_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_dec(v___x_328_);
lean_dec(v_index_324_);
goto v___jp_310_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_331_ = lean_unsigned_to_nat(4u);
v___x_332_ = lean_nat_mul(v___x_328_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(3u);
v___x_334_ = lean_nat_mul(v___x_329_, v___x_333_);
v___x_335_ = lean_nat_dec_le(v___x_332_, v___x_334_);
lean_dec(v___x_334_);
lean_dec(v___x_332_);
if (v___x_335_ == 0)
{
lean_dec(v___x_328_);
lean_dec(v_index_324_);
goto v___jp_310_;
}
else
{
lean_object* v___x_336_; 
lean_dec_ref(v_x_281_);
lean_dec_ref(v_x_280_);
v___x_336_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_283_, v___x_328_, v_index_324_, v_fst_284_, v_snd_285_);
lean_dec(v_index_324_);
return v___x_336_;
}
}
}
default: 
{
lean_object* v_size_337_; lean_object* v_keyArray_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_size_337_ = lean_ctor_get(v_x_283_, 0);
v_keyArray_338_ = lean_ctor_get(v_x_283_, 1);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_size_337_, v___x_339_);
v___x_341_ = lean_array_get_size(v_keyArray_338_);
v___x_342_ = lean_nat_dec_lt(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v___x_340_);
lean_inc_ref(v_x_281_);
lean_inc_ref(v_x_280_);
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_280_, v_x_281_, v_x_283_);
v___y_294_ = v___x_343_;
goto v___jp_293_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_344_ = lean_unsigned_to_nat(4u);
v___x_345_ = lean_nat_mul(v___x_340_, v___x_344_);
lean_dec(v___x_340_);
v___x_346_ = lean_unsigned_to_nat(3u);
v___x_347_ = lean_nat_mul(v___x_341_, v___x_346_);
v___x_348_ = lean_nat_dec_le(v___x_345_, v___x_347_);
lean_dec(v___x_347_);
lean_dec(v___x_345_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_inc_ref(v_x_281_);
lean_inc_ref(v_x_280_);
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_280_, v_x_281_, v_x_283_);
v___y_294_ = v___x_349_;
goto v___jp_293_;
}
else
{
v___y_294_ = v_x_283_;
goto v___jp_293_;
}
}
}
}
v___jp_286_:
{
lean_object* v_size_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_size_289_ = lean_ctor_get(v___y_287_, 0);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_size_289_, v___x_290_);
v___x_292_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_287_, v___x_291_, v_i_288_, v_fst_284_, v_snd_285_);
lean_dec(v_i_288_);
return v___x_292_;
}
v___jp_293_:
{
lean_object* v___x_295_; 
lean_inc(v_fst_284_);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_280_, v_x_281_, v___y_294_, v_fst_284_);
switch(lean_obj_tag(v___x_295_))
{
case 0:
{
lean_object* v_index_296_; lean_object* v_size_297_; lean_object* v___x_298_; 
v_index_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_index_296_);
lean_dec_ref_known(v___x_295_, 3);
v_size_297_ = lean_ctor_get(v___y_294_, 0);
lean_inc(v_size_297_);
v___x_298_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_294_, v_size_297_, v_index_296_, v_fst_284_, v_snd_285_);
lean_dec(v_index_296_);
return v___x_298_;
}
case 1:
{
lean_object* v_index_299_; 
v_index_299_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_index_299_);
lean_dec_ref_known(v___x_295_, 1);
v___y_287_ = v___y_294_;
v_i_288_ = v_index_299_;
goto v___jp_286_;
}
default: 
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_294_, v___x_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_index_302_; 
v_index_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_index_302_);
lean_dec_ref_known(v___x_301_, 1);
v___y_287_ = v___y_294_;
v_i_288_ = v_index_302_;
goto v___jp_286_;
}
else
{
lean_dec(v_snd_285_);
lean_dec(v_fst_284_);
return v___y_294_;
}
}
}
}
v___jp_303_:
{
lean_object* v_size_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_size_306_ = lean_ctor_get(v___y_304_, 0);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_size_306_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_304_, v___x_308_, v_i_305_, v_fst_284_, v_snd_285_);
lean_dec(v_i_305_);
return v___x_309_;
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_inc_ref(v_x_281_);
lean_inc_ref(v_x_280_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_280_, v_x_281_, v_x_283_);
lean_inc(v_fst_284_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_280_, v_x_281_, v___x_311_, v_fst_284_);
switch(lean_obj_tag(v___x_312_))
{
case 0:
{
lean_object* v_index_313_; lean_object* v_size_314_; lean_object* v___x_315_; 
v_index_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_index_313_);
lean_dec_ref_known(v___x_312_, 3);
v_size_314_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_size_314_);
v___x_315_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_311_, v_size_314_, v_index_313_, v_fst_284_, v_snd_285_);
lean_dec(v_index_313_);
return v___x_315_;
}
case 1:
{
lean_object* v_index_316_; 
v_index_316_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_index_316_);
lean_dec_ref_known(v___x_312_, 1);
v___y_304_ = v___x_311_;
v_i_305_ = v_index_316_;
goto v___jp_303_;
}
default: 
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_311_, v___x_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_index_319_; 
v_index_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_index_319_);
lean_dec_ref_known(v___x_318_, 1);
v___y_304_ = v___x_311_;
v_i_305_ = v_index_319_;
goto v___jp_303_;
}
else
{
lean_dec(v_snd_285_);
lean_dec(v_fst_284_);
return v___x_311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___f_352_; 
v___f_352_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_352_, 0, v_x_350_);
lean_closure_set(v___f_352_, 1, v_x_351_);
return v___f_352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_inst_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v___f_359_; 
v___f_359_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_359_, 0, v_x_355_);
lean_closure_set(v___f_359_, 1, v_x_356_);
return v___f_359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew___redArg(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_m_362_, lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
lean_object* v___y_366_; lean_object* v_i_367_; lean_object* v___y_383_; lean_object* v_i_384_; lean_object* v___y_390_; lean_object* v___x_399_; 
lean_inc(v_a_363_);
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_360_, v_x_361_, v_m_362_, v_a_363_);
switch(lean_obj_tag(v___x_399_))
{
case 0:
{
lean_dec_ref_known(v___x_399_, 3);
lean_dec(v_b_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_x_361_);
lean_dec_ref(v_x_360_);
return v_m_362_;
}
case 1:
{
lean_object* v_index_400_; lean_object* v_size_401_; lean_object* v_keyArray_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_index_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_index_400_);
lean_dec_ref_known(v___x_399_, 1);
v_size_401_ = lean_ctor_get(v_m_362_, 0);
v_keyArray_402_ = lean_ctor_get(v_m_362_, 1);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_size_401_, v___x_403_);
v___x_405_ = lean_array_get_size(v_keyArray_402_);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v___x_404_);
lean_dec(v_index_400_);
goto v___jp_372_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_407_ = lean_unsigned_to_nat(4u);
v___x_408_ = lean_nat_mul(v___x_404_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(3u);
v___x_410_ = lean_nat_mul(v___x_405_, v___x_409_);
v___x_411_ = lean_nat_dec_le(v___x_408_, v___x_410_);
lean_dec(v___x_410_);
lean_dec(v___x_408_);
if (v___x_411_ == 0)
{
lean_dec(v___x_404_);
lean_dec(v_index_400_);
goto v___jp_372_;
}
else
{
lean_object* v___x_412_; 
lean_dec_ref(v_x_361_);
lean_dec_ref(v_x_360_);
v___x_412_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_362_, v___x_404_, v_index_400_, v_a_363_, v_b_364_);
lean_dec(v_index_400_);
return v___x_412_;
}
}
}
default: 
{
lean_object* v_size_413_; lean_object* v_keyArray_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_size_413_ = lean_ctor_get(v_m_362_, 0);
v_keyArray_414_ = lean_ctor_get(v_m_362_, 1);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_size_413_, v___x_415_);
v___x_417_ = lean_array_get_size(v_keyArray_414_);
v___x_418_ = lean_nat_dec_lt(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v___x_416_);
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_360_, v_x_361_, v_m_362_);
v___y_390_ = v___x_419_;
goto v___jp_389_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_420_ = lean_unsigned_to_nat(4u);
v___x_421_ = lean_nat_mul(v___x_416_, v___x_420_);
lean_dec(v___x_416_);
v___x_422_ = lean_unsigned_to_nat(3u);
v___x_423_ = lean_nat_mul(v___x_417_, v___x_422_);
v___x_424_ = lean_nat_dec_le(v___x_421_, v___x_423_);
lean_dec(v___x_423_);
lean_dec(v___x_421_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_360_, v_x_361_, v_m_362_);
v___y_390_ = v___x_425_;
goto v___jp_389_;
}
else
{
v___y_390_ = v_m_362_;
goto v___jp_389_;
}
}
}
}
v___jp_365_:
{
lean_object* v_size_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_size_368_ = lean_ctor_get(v___y_366_, 0);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_size_368_, v___x_369_);
v___x_371_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_366_, v___x_370_, v_i_367_, v_a_363_, v_b_364_);
lean_dec(v_i_367_);
return v___x_371_;
}
v___jp_372_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_360_, v_x_361_, v_m_362_);
lean_inc(v_a_363_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_360_, v_x_361_, v___x_373_, v_a_363_);
switch(lean_obj_tag(v___x_374_))
{
case 0:
{
lean_object* v_index_375_; lean_object* v_size_376_; lean_object* v___x_377_; 
v_index_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_index_375_);
lean_dec_ref_known(v___x_374_, 3);
v_size_376_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_size_376_);
v___x_377_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_373_, v_size_376_, v_index_375_, v_a_363_, v_b_364_);
lean_dec(v_index_375_);
return v___x_377_;
}
case 1:
{
lean_object* v_index_378_; 
v_index_378_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_index_378_);
lean_dec_ref_known(v___x_374_, 1);
v___y_366_ = v___x_373_;
v_i_367_ = v_index_378_;
goto v___jp_365_;
}
default: 
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_373_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_index_381_; 
v_index_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_index_381_);
lean_dec_ref_known(v___x_380_, 1);
v___y_366_ = v___x_373_;
v_i_367_ = v_index_381_;
goto v___jp_365_;
}
else
{
lean_dec(v_b_364_);
lean_dec(v_a_363_);
return v___x_373_;
}
}
}
}
v___jp_382_:
{
lean_object* v_size_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_size_385_ = lean_ctor_get(v___y_383_, 0);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_size_385_, v___x_386_);
v___x_388_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_383_, v___x_387_, v_i_384_, v_a_363_, v_b_364_);
lean_dec(v_i_384_);
return v___x_388_;
}
v___jp_389_:
{
lean_object* v___x_391_; 
lean_inc(v_a_363_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_360_, v_x_361_, v___y_390_, v_a_363_);
switch(lean_obj_tag(v___x_391_))
{
case 0:
{
lean_object* v_index_392_; lean_object* v_size_393_; lean_object* v___x_394_; 
v_index_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_index_392_);
lean_dec_ref_known(v___x_391_, 3);
v_size_393_ = lean_ctor_get(v___y_390_, 0);
lean_inc(v_size_393_);
v___x_394_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_390_, v_size_393_, v_index_392_, v_a_363_, v_b_364_);
lean_dec(v_index_392_);
return v___x_394_;
}
case 1:
{
lean_object* v_index_395_; 
v_index_395_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_index_395_);
lean_dec_ref_known(v___x_391_, 1);
v___y_383_ = v___y_390_;
v_i_384_ = v_index_395_;
goto v___jp_382_;
}
default: 
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_390_, v___x_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_index_398_; 
v_index_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_index_398_);
lean_dec_ref_known(v___x_397_, 1);
v___y_383_ = v___y_390_;
v_i_384_ = v_index_398_;
goto v___jp_382_;
}
else
{
lean_dec(v_b_364_);
lean_dec(v_a_363_);
return v___y_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertIfNew(lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_m_432_, lean_object* v_a_433_, lean_object* v_b_434_){
_start:
{
lean_object* v___y_436_; lean_object* v_i_437_; lean_object* v___y_453_; lean_object* v_i_454_; lean_object* v___y_460_; lean_object* v___x_469_; 
lean_inc(v_a_433_);
lean_inc_ref(v_x_429_);
lean_inc_ref(v_x_428_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_428_, v_x_429_, v_m_432_, v_a_433_);
switch(lean_obj_tag(v___x_469_))
{
case 0:
{
lean_dec_ref_known(v___x_469_, 3);
lean_dec(v_b_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_428_);
return v_m_432_;
}
case 1:
{
lean_object* v_index_470_; lean_object* v_size_471_; lean_object* v_keyArray_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_index_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_index_470_);
lean_dec_ref_known(v___x_469_, 1);
v_size_471_ = lean_ctor_get(v_m_432_, 0);
v_keyArray_472_ = lean_ctor_get(v_m_432_, 1);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_size_471_, v___x_473_);
v___x_475_ = lean_array_get_size(v_keyArray_472_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_dec(v___x_474_);
lean_dec(v_index_470_);
goto v___jp_442_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_477_ = lean_unsigned_to_nat(4u);
v___x_478_ = lean_nat_mul(v___x_474_, v___x_477_);
v___x_479_ = lean_unsigned_to_nat(3u);
v___x_480_ = lean_nat_mul(v___x_475_, v___x_479_);
v___x_481_ = lean_nat_dec_le(v___x_478_, v___x_480_);
lean_dec(v___x_480_);
lean_dec(v___x_478_);
if (v___x_481_ == 0)
{
lean_dec(v___x_474_);
lean_dec(v_index_470_);
goto v___jp_442_;
}
else
{
lean_object* v___x_482_; 
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_428_);
v___x_482_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_432_, v___x_474_, v_index_470_, v_a_433_, v_b_434_);
lean_dec(v_index_470_);
return v___x_482_;
}
}
}
default: 
{
lean_object* v_size_483_; lean_object* v_keyArray_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_size_483_ = lean_ctor_get(v_m_432_, 0);
v_keyArray_484_ = lean_ctor_get(v_m_432_, 1);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_size_483_, v___x_485_);
v___x_487_ = lean_array_get_size(v_keyArray_484_);
v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v___x_486_);
lean_inc_ref(v_x_429_);
lean_inc_ref(v_x_428_);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_428_, v_x_429_, v_m_432_);
v___y_460_ = v___x_489_;
goto v___jp_459_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_490_ = lean_unsigned_to_nat(4u);
v___x_491_ = lean_nat_mul(v___x_486_, v___x_490_);
lean_dec(v___x_486_);
v___x_492_ = lean_unsigned_to_nat(3u);
v___x_493_ = lean_nat_mul(v___x_487_, v___x_492_);
v___x_494_ = lean_nat_dec_le(v___x_491_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___x_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_inc_ref(v_x_429_);
lean_inc_ref(v_x_428_);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_428_, v_x_429_, v_m_432_);
v___y_460_ = v___x_495_;
goto v___jp_459_;
}
else
{
v___y_460_ = v_m_432_;
goto v___jp_459_;
}
}
}
}
v___jp_435_:
{
lean_object* v_size_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_size_438_ = lean_ctor_get(v___y_436_, 0);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_size_438_, v___x_439_);
v___x_441_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_436_, v___x_440_, v_i_437_, v_a_433_, v_b_434_);
lean_dec(v_i_437_);
return v___x_441_;
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc_ref(v_x_429_);
lean_inc_ref(v_x_428_);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_428_, v_x_429_, v_m_432_);
lean_inc(v_a_433_);
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_428_, v_x_429_, v___x_443_, v_a_433_);
switch(lean_obj_tag(v___x_444_))
{
case 0:
{
lean_object* v_index_445_; lean_object* v_size_446_; lean_object* v___x_447_; 
v_index_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_index_445_);
lean_dec_ref_known(v___x_444_, 3);
v_size_446_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_size_446_);
v___x_447_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_443_, v_size_446_, v_index_445_, v_a_433_, v_b_434_);
lean_dec(v_index_445_);
return v___x_447_;
}
case 1:
{
lean_object* v_index_448_; 
v_index_448_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_index_448_);
lean_dec_ref_known(v___x_444_, 1);
v___y_436_ = v___x_443_;
v_i_437_ = v_index_448_;
goto v___jp_435_;
}
default: 
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_443_, v___x_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_index_451_; 
v_index_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_451_);
lean_dec_ref_known(v___x_450_, 1);
v___y_436_ = v___x_443_;
v_i_437_ = v_index_451_;
goto v___jp_435_;
}
else
{
lean_dec(v_b_434_);
lean_dec(v_a_433_);
return v___x_443_;
}
}
}
}
v___jp_452_:
{
lean_object* v_size_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_size_455_ = lean_ctor_get(v___y_453_, 0);
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_size_455_, v___x_456_);
v___x_458_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_453_, v___x_457_, v_i_454_, v_a_433_, v_b_434_);
lean_dec(v_i_454_);
return v___x_458_;
}
v___jp_459_:
{
lean_object* v___x_461_; 
lean_inc(v_a_433_);
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_428_, v_x_429_, v___y_460_, v_a_433_);
switch(lean_obj_tag(v___x_461_))
{
case 0:
{
lean_object* v_index_462_; lean_object* v_size_463_; lean_object* v___x_464_; 
v_index_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_index_462_);
lean_dec_ref_known(v___x_461_, 3);
v_size_463_ = lean_ctor_get(v___y_460_, 0);
lean_inc(v_size_463_);
v___x_464_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_460_, v_size_463_, v_index_462_, v_a_433_, v_b_434_);
lean_dec(v_index_462_);
return v___x_464_;
}
case 1:
{
lean_object* v_index_465_; 
v_index_465_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_index_465_);
lean_dec_ref_known(v___x_461_, 1);
v___y_453_ = v___y_460_;
v_i_454_ = v_index_465_;
goto v___jp_452_;
}
default: 
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_460_, v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_index_468_; 
v_index_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_index_468_);
lean_dec_ref_known(v___x_467_, 1);
v___y_453_ = v___y_460_;
v_i_454_ = v_index_468_;
goto v___jp_452_;
}
else
{
lean_dec(v_b_434_);
lean_dec(v_a_433_);
return v___y_460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert___redArg(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
lean_object* v___x_501_; 
lean_inc(v_a_499_);
lean_inc_ref(v_x_497_);
lean_inc_ref(v_x_496_);
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_496_, v_x_497_, v_m_498_, v_a_499_);
switch(lean_obj_tag(v___x_501_))
{
case 0:
{
lean_object* v_index_502_; lean_object* v_size_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v_x_497_);
lean_dec_ref(v_x_496_);
v_index_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_index_502_);
lean_dec_ref_known(v___x_501_, 3);
v_size_503_ = lean_ctor_get(v_m_498_, 0);
lean_inc(v_size_503_);
v___x_504_ = 1;
v___x_505_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_498_, v_size_503_, v_index_502_, v_a_499_, v_b_500_);
lean_dec(v_index_502_);
v___x_506_ = lean_box(v___x_504_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
return v___x_507_;
}
case 1:
{
lean_object* v_index_508_; lean_object* v_size_509_; lean_object* v_keyArray_510_; uint8_t v___x_511_; lean_object* v___y_513_; lean_object* v_i_514_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_index_508_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_index_508_);
lean_dec_ref_known(v___x_501_, 1);
v_size_509_ = lean_ctor_get(v_m_498_, 0);
v_keyArray_510_ = lean_ctor_get(v_m_498_, 1);
v___x_511_ = 0;
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_509_, v___x_535_);
v___x_537_ = lean_array_get_size(v_keyArray_510_);
v___x_538_ = lean_nat_dec_lt(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v___x_536_);
lean_dec(v_index_508_);
goto v___jp_521_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_539_ = lean_unsigned_to_nat(4u);
v___x_540_ = lean_nat_mul(v___x_536_, v___x_539_);
v___x_541_ = lean_unsigned_to_nat(3u);
v___x_542_ = lean_nat_mul(v___x_537_, v___x_541_);
v___x_543_ = lean_nat_dec_le(v___x_540_, v___x_542_);
lean_dec(v___x_542_);
lean_dec(v___x_540_);
if (v___x_543_ == 0)
{
lean_dec(v___x_536_);
lean_dec(v_index_508_);
goto v___jp_521_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec_ref(v_x_497_);
lean_dec_ref(v_x_496_);
v___x_544_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_498_, v___x_536_, v_index_508_, v_a_499_, v_b_500_);
lean_dec(v_index_508_);
v___x_545_ = lean_box(v___x_511_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
return v___x_546_;
}
}
v___jp_512_:
{
lean_object* v_size_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_size_515_ = lean_ctor_get(v___y_513_, 0);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_size_515_, v___x_516_);
v___x_518_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_513_, v___x_517_, v_i_514_, v_a_499_, v_b_500_);
lean_dec(v_i_514_);
v___x_519_ = lean_box(v___x_511_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
return v___x_520_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc_ref(v_x_497_);
lean_inc_ref(v_x_496_);
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_496_, v_x_497_, v_m_498_);
lean_inc(v_a_499_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_496_, v_x_497_, v___x_522_, v_a_499_);
switch(lean_obj_tag(v___x_523_))
{
case 0:
{
lean_object* v_index_524_; lean_object* v_size_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_index_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_index_524_);
lean_dec_ref_known(v___x_523_, 3);
v_size_525_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_size_525_);
v___x_526_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_522_, v_size_525_, v_index_524_, v_a_499_, v_b_500_);
lean_dec(v_index_524_);
v___x_527_ = lean_box(v___x_511_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
return v___x_528_;
}
case 1:
{
lean_object* v_index_529_; 
v_index_529_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_index_529_);
lean_dec_ref_known(v___x_523_, 1);
v___y_513_ = v___x_522_;
v_i_514_ = v_index_529_;
goto v___jp_512_;
}
default: 
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_522_, v___x_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_index_532_; 
v_index_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_index_532_);
lean_dec_ref_known(v___x_531_, 1);
v___y_513_ = v___x_522_;
v_i_514_ = v_index_532_;
goto v___jp_512_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_b_500_);
lean_dec(v_a_499_);
v___x_533_ = lean_box(v___x_511_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_522_);
return v___x_534_;
}
}
}
}
}
default: 
{
lean_object* v_size_547_; lean_object* v_keyArray_548_; uint8_t v___x_549_; lean_object* v___y_551_; lean_object* v_i_552_; lean_object* v___y_560_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_size_547_ = lean_ctor_get(v_m_498_, 0);
v_keyArray_548_ = lean_ctor_get(v_m_498_, 1);
v___x_549_ = 0;
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_size_547_, v___x_573_);
v___x_575_ = lean_array_get_size(v_keyArray_548_);
v___x_576_ = lean_nat_dec_lt(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v___x_574_);
lean_inc_ref(v_x_497_);
lean_inc_ref(v_x_496_);
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_496_, v_x_497_, v_m_498_);
v___y_560_ = v___x_577_;
goto v___jp_559_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_578_ = lean_unsigned_to_nat(4u);
v___x_579_ = lean_nat_mul(v___x_574_, v___x_578_);
lean_dec(v___x_574_);
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = lean_nat_mul(v___x_575_, v___x_580_);
v___x_582_ = lean_nat_dec_le(v___x_579_, v___x_581_);
lean_dec(v___x_581_);
lean_dec(v___x_579_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_inc_ref(v_x_497_);
lean_inc_ref(v_x_496_);
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_496_, v_x_497_, v_m_498_);
v___y_560_ = v___x_583_;
goto v___jp_559_;
}
else
{
v___y_560_ = v_m_498_;
goto v___jp_559_;
}
}
v___jp_550_:
{
lean_object* v_size_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_size_553_ = lean_ctor_get(v___y_551_, 0);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_size_553_, v___x_554_);
v___x_556_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_551_, v___x_555_, v_i_552_, v_a_499_, v_b_500_);
lean_dec(v_i_552_);
v___x_557_ = lean_box(v___x_549_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
return v___x_558_;
}
v___jp_559_:
{
lean_object* v___x_561_; 
lean_inc(v_a_499_);
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_496_, v_x_497_, v___y_560_, v_a_499_);
switch(lean_obj_tag(v___x_561_))
{
case 0:
{
lean_object* v_index_562_; lean_object* v_size_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_index_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_index_562_);
lean_dec_ref_known(v___x_561_, 3);
v_size_563_ = lean_ctor_get(v___y_560_, 0);
lean_inc(v_size_563_);
v___x_564_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_560_, v_size_563_, v_index_562_, v_a_499_, v_b_500_);
lean_dec(v_index_562_);
v___x_565_ = lean_box(v___x_549_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
return v___x_566_;
}
case 1:
{
lean_object* v_index_567_; 
v_index_567_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_index_567_);
lean_dec_ref_known(v___x_561_, 1);
v___y_551_ = v___y_560_;
v_i_552_ = v_index_567_;
goto v___jp_550_;
}
default: 
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_560_, v___x_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_index_570_; 
v_index_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_index_570_);
lean_dec_ref_known(v___x_569_, 1);
v___y_551_ = v___y_560_;
v_i_552_ = v_index_570_;
goto v___jp_550_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_b_500_);
lean_dec(v_a_499_);
v___x_571_ = lean_box(v___x_549_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___y_560_);
return v___x_572_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsert(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_m_590_, lean_object* v_a_591_, lean_object* v_b_592_){
_start:
{
lean_object* v___x_593_; 
lean_inc(v_a_591_);
lean_inc_ref(v_x_587_);
lean_inc_ref(v_x_586_);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_586_, v_x_587_, v_m_590_, v_a_591_);
switch(lean_obj_tag(v___x_593_))
{
case 0:
{
lean_object* v_index_594_; lean_object* v_size_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec_ref(v_x_587_);
lean_dec_ref(v_x_586_);
v_index_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_index_594_);
lean_dec_ref_known(v___x_593_, 3);
v_size_595_ = lean_ctor_get(v_m_590_, 0);
lean_inc(v_size_595_);
v___x_596_ = 1;
v___x_597_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_590_, v_size_595_, v_index_594_, v_a_591_, v_b_592_);
lean_dec(v_index_594_);
v___x_598_ = lean_box(v___x_596_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
return v___x_599_;
}
case 1:
{
lean_object* v_index_600_; lean_object* v_size_601_; lean_object* v_keyArray_602_; uint8_t v___x_603_; lean_object* v___y_605_; lean_object* v_i_606_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_index_600_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_index_600_);
lean_dec_ref_known(v___x_593_, 1);
v_size_601_ = lean_ctor_get(v_m_590_, 0);
v_keyArray_602_ = lean_ctor_get(v_m_590_, 1);
v___x_603_ = 0;
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_size_601_, v___x_627_);
v___x_629_ = lean_array_get_size(v_keyArray_602_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v___x_628_);
lean_dec(v_index_600_);
goto v___jp_613_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_631_ = lean_unsigned_to_nat(4u);
v___x_632_ = lean_nat_mul(v___x_628_, v___x_631_);
v___x_633_ = lean_unsigned_to_nat(3u);
v___x_634_ = lean_nat_mul(v___x_629_, v___x_633_);
v___x_635_ = lean_nat_dec_le(v___x_632_, v___x_634_);
lean_dec(v___x_634_);
lean_dec(v___x_632_);
if (v___x_635_ == 0)
{
lean_dec(v___x_628_);
lean_dec(v_index_600_);
goto v___jp_613_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_x_587_);
lean_dec_ref(v_x_586_);
v___x_636_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_590_, v___x_628_, v_index_600_, v_a_591_, v_b_592_);
lean_dec(v_index_600_);
v___x_637_ = lean_box(v___x_603_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
return v___x_638_;
}
}
v___jp_604_:
{
lean_object* v_size_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_size_607_ = lean_ctor_get(v___y_605_, 0);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_size_607_, v___x_608_);
v___x_610_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_605_, v___x_609_, v_i_606_, v_a_591_, v_b_592_);
lean_dec(v_i_606_);
v___x_611_ = lean_box(v___x_603_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
return v___x_612_;
}
v___jp_613_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc_ref(v_x_587_);
lean_inc_ref(v_x_586_);
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_586_, v_x_587_, v_m_590_);
lean_inc(v_a_591_);
v___x_615_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_586_, v_x_587_, v___x_614_, v_a_591_);
switch(lean_obj_tag(v___x_615_))
{
case 0:
{
lean_object* v_index_616_; lean_object* v_size_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_index_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_index_616_);
lean_dec_ref_known(v___x_615_, 3);
v_size_617_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_size_617_);
v___x_618_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_614_, v_size_617_, v_index_616_, v_a_591_, v_b_592_);
lean_dec(v_index_616_);
v___x_619_ = lean_box(v___x_603_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
return v___x_620_;
}
case 1:
{
lean_object* v_index_621_; 
v_index_621_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_index_621_);
lean_dec_ref_known(v___x_615_, 1);
v___y_605_ = v___x_614_;
v_i_606_ = v_index_621_;
goto v___jp_604_;
}
default: 
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_614_, v___x_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_index_624_; 
v_index_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_index_624_);
lean_dec_ref_known(v___x_623_, 1);
v___y_605_ = v___x_614_;
v_i_606_ = v_index_624_;
goto v___jp_604_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_b_592_);
lean_dec(v_a_591_);
v___x_625_ = lean_box(v___x_603_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_614_);
return v___x_626_;
}
}
}
}
}
default: 
{
lean_object* v_size_639_; lean_object* v_keyArray_640_; uint8_t v___x_641_; lean_object* v___y_643_; lean_object* v_i_644_; lean_object* v___y_652_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_size_639_ = lean_ctor_get(v_m_590_, 0);
v_keyArray_640_ = lean_ctor_get(v_m_590_, 1);
v___x_641_ = 0;
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_size_639_, v___x_665_);
v___x_667_ = lean_array_get_size(v_keyArray_640_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec(v___x_666_);
lean_inc_ref(v_x_587_);
lean_inc_ref(v_x_586_);
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_586_, v_x_587_, v_m_590_);
v___y_652_ = v___x_669_;
goto v___jp_651_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_670_ = lean_unsigned_to_nat(4u);
v___x_671_ = lean_nat_mul(v___x_666_, v___x_670_);
lean_dec(v___x_666_);
v___x_672_ = lean_unsigned_to_nat(3u);
v___x_673_ = lean_nat_mul(v___x_667_, v___x_672_);
v___x_674_ = lean_nat_dec_le(v___x_671_, v___x_673_);
lean_dec(v___x_673_);
lean_dec(v___x_671_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_inc_ref(v_x_587_);
lean_inc_ref(v_x_586_);
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_586_, v_x_587_, v_m_590_);
v___y_652_ = v___x_675_;
goto v___jp_651_;
}
else
{
v___y_652_ = v_m_590_;
goto v___jp_651_;
}
}
v___jp_642_:
{
lean_object* v_size_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_size_645_ = lean_ctor_get(v___y_643_, 0);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_size_645_, v___x_646_);
v___x_648_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_643_, v___x_647_, v_i_644_, v_a_591_, v_b_592_);
lean_dec(v_i_644_);
v___x_649_ = lean_box(v___x_641_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
return v___x_650_;
}
v___jp_651_:
{
lean_object* v___x_653_; 
lean_inc(v_a_591_);
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_586_, v_x_587_, v___y_652_, v_a_591_);
switch(lean_obj_tag(v___x_653_))
{
case 0:
{
lean_object* v_index_654_; lean_object* v_size_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_index_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_index_654_);
lean_dec_ref_known(v___x_653_, 3);
v_size_655_ = lean_ctor_get(v___y_652_, 0);
lean_inc(v_size_655_);
v___x_656_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_652_, v_size_655_, v_index_654_, v_a_591_, v_b_592_);
lean_dec(v_index_654_);
v___x_657_ = lean_box(v___x_641_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
return v___x_658_;
}
case 1:
{
lean_object* v_index_659_; 
v_index_659_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_index_659_);
lean_dec_ref_known(v___x_653_, 1);
v___y_643_ = v___y_652_;
v_i_644_ = v_index_659_;
goto v___jp_642_;
}
default: 
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_652_, v___x_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_index_662_; 
v_index_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_index_662_);
lean_dec_ref_known(v___x_661_, 1);
v___y_643_ = v___y_652_;
v_i_644_ = v_index_662_;
goto v___jp_642_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v_b_592_);
lean_dec(v_a_591_);
v___x_663_ = lean_box(v___x_641_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___y_652_);
return v___x_664_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_m_678_, lean_object* v_a_679_, lean_object* v_b_680_){
_start:
{
lean_object* v___x_681_; 
lean_inc(v_a_679_);
lean_inc_ref(v_x_677_);
lean_inc_ref(v_x_676_);
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_676_, v_x_677_, v_m_678_, v_a_679_);
switch(lean_obj_tag(v___x_681_))
{
case 0:
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref_known(v___x_681_, 3);
lean_dec(v_b_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_x_677_);
lean_dec_ref(v_x_676_);
v___x_682_ = 1;
v___x_683_ = lean_box(v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_m_678_);
return v___x_684_;
}
case 1:
{
lean_object* v_index_685_; lean_object* v_size_686_; lean_object* v_keyArray_687_; uint8_t v___x_688_; lean_object* v___y_690_; lean_object* v_i_691_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_index_685_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_index_685_);
lean_dec_ref_known(v___x_681_, 1);
v_size_686_ = lean_ctor_get(v_m_678_, 0);
v_keyArray_687_ = lean_ctor_get(v_m_678_, 1);
v___x_688_ = 0;
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_size_686_, v___x_712_);
v___x_714_ = lean_array_get_size(v_keyArray_687_);
v___x_715_ = lean_nat_dec_lt(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_dec(v___x_713_);
lean_dec(v_index_685_);
goto v___jp_698_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = lean_nat_mul(v___x_713_, v___x_716_);
v___x_718_ = lean_unsigned_to_nat(3u);
v___x_719_ = lean_nat_mul(v___x_714_, v___x_718_);
v___x_720_ = lean_nat_dec_le(v___x_717_, v___x_719_);
lean_dec(v___x_719_);
lean_dec(v___x_717_);
if (v___x_720_ == 0)
{
lean_dec(v___x_713_);
lean_dec(v_index_685_);
goto v___jp_698_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec_ref(v_x_677_);
lean_dec_ref(v_x_676_);
v___x_721_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_678_, v___x_713_, v_index_685_, v_a_679_, v_b_680_);
lean_dec(v_index_685_);
v___x_722_ = lean_box(v___x_688_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_721_);
return v___x_723_;
}
}
v___jp_689_:
{
lean_object* v_size_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_size_692_ = lean_ctor_get(v___y_690_, 0);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_add(v_size_692_, v___x_693_);
v___x_695_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_690_, v___x_694_, v_i_691_, v_a_679_, v_b_680_);
lean_dec(v_i_691_);
v___x_696_ = lean_box(v___x_688_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_695_);
return v___x_697_;
}
v___jp_698_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_inc_ref(v_x_677_);
lean_inc_ref(v_x_676_);
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_676_, v_x_677_, v_m_678_);
lean_inc(v_a_679_);
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_676_, v_x_677_, v___x_699_, v_a_679_);
switch(lean_obj_tag(v___x_700_))
{
case 0:
{
lean_object* v_index_701_; lean_object* v_size_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_index_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_index_701_);
lean_dec_ref_known(v___x_700_, 3);
v_size_702_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_size_702_);
v___x_703_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_699_, v_size_702_, v_index_701_, v_a_679_, v_b_680_);
lean_dec(v_index_701_);
v___x_704_ = lean_box(v___x_688_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
return v___x_705_;
}
case 1:
{
lean_object* v_index_706_; 
v_index_706_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_index_706_);
lean_dec_ref_known(v___x_700_, 1);
v___y_690_ = v___x_699_;
v_i_691_ = v_index_706_;
goto v___jp_689_;
}
default: 
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_699_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_index_709_; 
v_index_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_index_709_);
lean_dec_ref_known(v___x_708_, 1);
v___y_690_ = v___x_699_;
v_i_691_ = v_index_709_;
goto v___jp_689_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_b_680_);
lean_dec(v_a_679_);
v___x_710_ = lean_box(v___x_688_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_699_);
return v___x_711_;
}
}
}
}
}
default: 
{
lean_object* v_size_724_; lean_object* v_keyArray_725_; uint8_t v___x_726_; lean_object* v___y_728_; lean_object* v_i_729_; lean_object* v___y_737_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_size_724_ = lean_ctor_get(v_m_678_, 0);
v_keyArray_725_ = lean_ctor_get(v_m_678_, 1);
v___x_726_ = 0;
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_size_724_, v___x_750_);
v___x_752_ = lean_array_get_size(v_keyArray_725_);
v___x_753_ = lean_nat_dec_lt(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec(v___x_751_);
lean_inc_ref(v_x_677_);
lean_inc_ref(v_x_676_);
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_676_, v_x_677_, v_m_678_);
v___y_737_ = v___x_754_;
goto v___jp_736_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_755_ = lean_unsigned_to_nat(4u);
v___x_756_ = lean_nat_mul(v___x_751_, v___x_755_);
lean_dec(v___x_751_);
v___x_757_ = lean_unsigned_to_nat(3u);
v___x_758_ = lean_nat_mul(v___x_752_, v___x_757_);
v___x_759_ = lean_nat_dec_le(v___x_756_, v___x_758_);
lean_dec(v___x_758_);
lean_dec(v___x_756_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_inc_ref(v_x_677_);
lean_inc_ref(v_x_676_);
v___x_760_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_676_, v_x_677_, v_m_678_);
v___y_737_ = v___x_760_;
goto v___jp_736_;
}
else
{
v___y_737_ = v_m_678_;
goto v___jp_736_;
}
}
v___jp_727_:
{
lean_object* v_size_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_size_730_ = lean_ctor_get(v___y_728_, 0);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_size_730_, v___x_731_);
v___x_733_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_728_, v___x_732_, v_i_729_, v_a_679_, v_b_680_);
lean_dec(v_i_729_);
v___x_734_ = lean_box(v___x_726_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
return v___x_735_;
}
v___jp_736_:
{
lean_object* v___x_738_; 
lean_inc(v_a_679_);
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_676_, v_x_677_, v___y_737_, v_a_679_);
switch(lean_obj_tag(v___x_738_))
{
case 0:
{
lean_object* v_index_739_; lean_object* v_size_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_index_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_index_739_);
lean_dec_ref_known(v___x_738_, 3);
v_size_740_ = lean_ctor_get(v___y_737_, 0);
lean_inc(v_size_740_);
v___x_741_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_737_, v_size_740_, v_index_739_, v_a_679_, v_b_680_);
lean_dec(v_index_739_);
v___x_742_ = lean_box(v___x_726_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
return v___x_743_;
}
case 1:
{
lean_object* v_index_744_; 
v_index_744_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_index_744_);
lean_dec_ref_known(v___x_738_, 1);
v___y_728_ = v___y_737_;
v_i_729_ = v_index_744_;
goto v___jp_727_;
}
default: 
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_737_, v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_index_747_; 
v_index_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_index_747_);
lean_dec_ref_known(v___x_746_, 1);
v___y_728_ = v___y_737_;
v_i_729_ = v_index_747_;
goto v___jp_727_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_b_680_);
lean_dec(v_a_679_);
v___x_748_ = lean_box(v___x_726_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___y_737_);
return v___x_749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_m_767_, lean_object* v_a_768_, lean_object* v_b_769_){
_start:
{
lean_object* v___x_770_; 
lean_inc(v_a_768_);
lean_inc_ref(v_x_764_);
lean_inc_ref(v_x_763_);
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_763_, v_x_764_, v_m_767_, v_a_768_);
switch(lean_obj_tag(v___x_770_))
{
case 0:
{
uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref_known(v___x_770_, 3);
lean_dec(v_b_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_x_764_);
lean_dec_ref(v_x_763_);
v___x_771_ = 1;
v___x_772_ = lean_box(v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_m_767_);
return v___x_773_;
}
case 1:
{
lean_object* v_index_774_; lean_object* v_size_775_; lean_object* v_keyArray_776_; uint8_t v___x_777_; lean_object* v___y_779_; lean_object* v_i_780_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_index_774_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_index_774_);
lean_dec_ref_known(v___x_770_, 1);
v_size_775_ = lean_ctor_get(v_m_767_, 0);
v_keyArray_776_ = lean_ctor_get(v_m_767_, 1);
v___x_777_ = 0;
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_size_775_, v___x_801_);
v___x_803_ = lean_array_get_size(v_keyArray_776_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v_index_774_);
goto v___jp_787_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_805_ = lean_unsigned_to_nat(4u);
v___x_806_ = lean_nat_mul(v___x_802_, v___x_805_);
v___x_807_ = lean_unsigned_to_nat(3u);
v___x_808_ = lean_nat_mul(v___x_803_, v___x_807_);
v___x_809_ = lean_nat_dec_le(v___x_806_, v___x_808_);
lean_dec(v___x_808_);
lean_dec(v___x_806_);
if (v___x_809_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v_index_774_);
goto v___jp_787_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_x_764_);
lean_dec_ref(v_x_763_);
v___x_810_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_767_, v___x_802_, v_index_774_, v_a_768_, v_b_769_);
lean_dec(v_index_774_);
v___x_811_ = lean_box(v___x_777_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___x_810_);
return v___x_812_;
}
}
v___jp_778_:
{
lean_object* v_size_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_size_781_ = lean_ctor_get(v___y_779_, 0);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_add(v_size_781_, v___x_782_);
v___x_784_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_779_, v___x_783_, v_i_780_, v_a_768_, v_b_769_);
lean_dec(v_i_780_);
v___x_785_ = lean_box(v___x_777_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
return v___x_786_;
}
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_inc_ref(v_x_764_);
lean_inc_ref(v_x_763_);
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_763_, v_x_764_, v_m_767_);
lean_inc(v_a_768_);
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_763_, v_x_764_, v___x_788_, v_a_768_);
switch(lean_obj_tag(v___x_789_))
{
case 0:
{
lean_object* v_index_790_; lean_object* v_size_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_index_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_index_790_);
lean_dec_ref_known(v___x_789_, 3);
v_size_791_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_size_791_);
v___x_792_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_788_, v_size_791_, v_index_790_, v_a_768_, v_b_769_);
lean_dec(v_index_790_);
v___x_793_ = lean_box(v___x_777_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_792_);
return v___x_794_;
}
case 1:
{
lean_object* v_index_795_; 
v_index_795_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_index_795_);
lean_dec_ref_known(v___x_789_, 1);
v___y_779_ = v___x_788_;
v_i_780_ = v_index_795_;
goto v___jp_778_;
}
default: 
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_788_, v___x_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_index_798_; 
v_index_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_index_798_);
lean_dec_ref_known(v___x_797_, 1);
v___y_779_ = v___x_788_;
v_i_780_ = v_index_798_;
goto v___jp_778_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_b_769_);
lean_dec(v_a_768_);
v___x_799_ = lean_box(v___x_777_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_788_);
return v___x_800_;
}
}
}
}
}
default: 
{
lean_object* v_size_813_; lean_object* v_keyArray_814_; uint8_t v___x_815_; lean_object* v___y_817_; lean_object* v_i_818_; lean_object* v___y_826_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_size_813_ = lean_ctor_get(v_m_767_, 0);
v_keyArray_814_ = lean_ctor_get(v_m_767_, 1);
v___x_815_ = 0;
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_nat_add(v_size_813_, v___x_839_);
v___x_841_ = lean_array_get_size(v_keyArray_814_);
v___x_842_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v___x_840_);
lean_inc_ref(v_x_764_);
lean_inc_ref(v_x_763_);
v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_763_, v_x_764_, v_m_767_);
v___y_826_ = v___x_843_;
goto v___jp_825_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_844_ = lean_unsigned_to_nat(4u);
v___x_845_ = lean_nat_mul(v___x_840_, v___x_844_);
lean_dec(v___x_840_);
v___x_846_ = lean_unsigned_to_nat(3u);
v___x_847_ = lean_nat_mul(v___x_841_, v___x_846_);
v___x_848_ = lean_nat_dec_le(v___x_845_, v___x_847_);
lean_dec(v___x_847_);
lean_dec(v___x_845_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_inc_ref(v_x_764_);
lean_inc_ref(v_x_763_);
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_763_, v_x_764_, v_m_767_);
v___y_826_ = v___x_849_;
goto v___jp_825_;
}
else
{
v___y_826_ = v_m_767_;
goto v___jp_825_;
}
}
v___jp_816_:
{
lean_object* v_size_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_size_819_ = lean_ctor_get(v___y_817_, 0);
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = lean_nat_add(v_size_819_, v___x_820_);
v___x_822_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_817_, v___x_821_, v_i_818_, v_a_768_, v_b_769_);
lean_dec(v_i_818_);
v___x_823_ = lean_box(v___x_815_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_822_);
return v___x_824_;
}
v___jp_825_:
{
lean_object* v___x_827_; 
lean_inc(v_a_768_);
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_763_, v_x_764_, v___y_826_, v_a_768_);
switch(lean_obj_tag(v___x_827_))
{
case 0:
{
lean_object* v_index_828_; lean_object* v_size_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_index_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_index_828_);
lean_dec_ref_known(v___x_827_, 3);
v_size_829_ = lean_ctor_get(v___y_826_, 0);
lean_inc(v_size_829_);
v___x_830_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_826_, v_size_829_, v_index_828_, v_a_768_, v_b_769_);
lean_dec(v_index_828_);
v___x_831_ = lean_box(v___x_815_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
return v___x_832_;
}
case 1:
{
lean_object* v_index_833_; 
v_index_833_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_index_833_);
lean_dec_ref_known(v___x_827_, 1);
v___y_817_ = v___y_826_;
v_i_818_ = v_index_833_;
goto v___jp_816_;
}
default: 
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_826_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_index_836_; 
v_index_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_836_);
lean_dec_ref_known(v___x_835_, 1);
v___y_817_ = v___y_826_;
v_i_818_ = v_index_836_;
goto v___jp_816_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_b_769_);
lean_dec(v_a_768_);
v___x_837_ = lean_box(v___x_815_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___y_826_);
return v___x_838_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_m_852_, lean_object* v_a_853_, lean_object* v_b_854_){
_start:
{
lean_object* v___x_855_; 
lean_inc(v_a_853_);
lean_inc_ref(v_x_851_);
lean_inc_ref(v_x_850_);
v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_850_, v_x_851_, v_m_852_, v_a_853_);
switch(lean_obj_tag(v___x_855_))
{
case 0:
{
lean_object* v_value_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_b_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_x_851_);
lean_dec_ref(v_x_850_);
v_value_856_ = lean_ctor_get(v___x_855_, 2);
lean_inc(v_value_856_);
lean_dec_ref_known(v___x_855_, 3);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_value_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_m_852_);
return v___x_858_;
}
case 1:
{
lean_object* v_index_859_; lean_object* v_size_860_; lean_object* v_keyArray_861_; lean_object* v___x_862_; lean_object* v___y_864_; lean_object* v_i_865_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_index_859_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_index_859_);
lean_dec_ref_known(v___x_855_, 1);
v_size_860_ = lean_ctor_get(v_m_852_, 0);
v_keyArray_861_ = lean_ctor_get(v_m_852_, 1);
v___x_862_ = lean_box(0);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_add(v_size_860_, v___x_883_);
v___x_885_ = lean_array_get_size(v_keyArray_861_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_dec(v___x_884_);
lean_dec(v_index_859_);
goto v___jp_871_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_887_ = lean_unsigned_to_nat(4u);
v___x_888_ = lean_nat_mul(v___x_884_, v___x_887_);
v___x_889_ = lean_unsigned_to_nat(3u);
v___x_890_ = lean_nat_mul(v___x_885_, v___x_889_);
v___x_891_ = lean_nat_dec_le(v___x_888_, v___x_890_);
lean_dec(v___x_890_);
lean_dec(v___x_888_);
if (v___x_891_ == 0)
{
lean_dec(v___x_884_);
lean_dec(v_index_859_);
goto v___jp_871_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v_x_851_);
lean_dec_ref(v_x_850_);
v___x_892_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_852_, v___x_884_, v_index_859_, v_a_853_, v_b_854_);
lean_dec(v_index_859_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_862_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
return v___x_893_;
}
}
v___jp_863_:
{
lean_object* v_size_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_size_866_ = lean_ctor_get(v___y_864_, 0);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_size_866_, v___x_867_);
v___x_869_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_864_, v___x_868_, v_i_865_, v_a_853_, v_b_854_);
lean_dec(v_i_865_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_862_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
return v___x_870_;
}
v___jp_871_:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_inc_ref(v_x_851_);
lean_inc_ref(v_x_850_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_850_, v_x_851_, v_m_852_);
lean_inc(v_a_853_);
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_850_, v_x_851_, v___x_872_, v_a_853_);
switch(lean_obj_tag(v___x_873_))
{
case 0:
{
lean_object* v_index_874_; lean_object* v_size_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_index_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_index_874_);
lean_dec_ref_known(v___x_873_, 3);
v_size_875_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_size_875_);
v___x_876_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_872_, v_size_875_, v_index_874_, v_a_853_, v_b_854_);
lean_dec(v_index_874_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_862_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
return v___x_877_;
}
case 1:
{
lean_object* v_index_878_; 
v_index_878_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_index_878_);
lean_dec_ref_known(v___x_873_, 1);
v___y_864_ = v___x_872_;
v_i_865_ = v_index_878_;
goto v___jp_863_;
}
default: 
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_872_, v___x_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_index_881_; 
v_index_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_index_881_);
lean_dec_ref_known(v___x_880_, 1);
v___y_864_ = v___x_872_;
v_i_865_ = v_index_881_;
goto v___jp_863_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_b_854_);
lean_dec(v_a_853_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_862_);
lean_ctor_set(v___x_882_, 1, v___x_872_);
return v___x_882_;
}
}
}
}
}
default: 
{
lean_object* v_size_894_; lean_object* v_keyArray_895_; lean_object* v___x_896_; lean_object* v___y_898_; lean_object* v_i_899_; lean_object* v___y_906_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_size_894_ = lean_ctor_get(v_m_852_, 0);
v_keyArray_895_ = lean_ctor_get(v_m_852_, 1);
v___x_896_ = lean_box(0);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_add(v_size_894_, v___x_917_);
v___x_919_ = lean_array_get_size(v_keyArray_895_);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_dec(v___x_918_);
lean_inc_ref(v_x_851_);
lean_inc_ref(v_x_850_);
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_850_, v_x_851_, v_m_852_);
v___y_906_ = v___x_921_;
goto v___jp_905_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_922_ = lean_unsigned_to_nat(4u);
v___x_923_ = lean_nat_mul(v___x_918_, v___x_922_);
lean_dec(v___x_918_);
v___x_924_ = lean_unsigned_to_nat(3u);
v___x_925_ = lean_nat_mul(v___x_919_, v___x_924_);
v___x_926_ = lean_nat_dec_le(v___x_923_, v___x_925_);
lean_dec(v___x_925_);
lean_dec(v___x_923_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_inc_ref(v_x_851_);
lean_inc_ref(v_x_850_);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_850_, v_x_851_, v_m_852_);
v___y_906_ = v___x_927_;
goto v___jp_905_;
}
else
{
v___y_906_ = v_m_852_;
goto v___jp_905_;
}
}
v___jp_897_:
{
lean_object* v_size_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_size_900_ = lean_ctor_get(v___y_898_, 0);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_add(v_size_900_, v___x_901_);
v___x_903_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_898_, v___x_902_, v_i_899_, v_a_853_, v_b_854_);
lean_dec(v_i_899_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_896_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
return v___x_904_;
}
v___jp_905_:
{
lean_object* v___x_907_; 
lean_inc(v_a_853_);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_850_, v_x_851_, v___y_906_, v_a_853_);
switch(lean_obj_tag(v___x_907_))
{
case 0:
{
lean_object* v_index_908_; lean_object* v_size_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_index_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_index_908_);
lean_dec_ref_known(v___x_907_, 3);
v_size_909_ = lean_ctor_get(v___y_906_, 0);
lean_inc(v_size_909_);
v___x_910_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_906_, v_size_909_, v_index_908_, v_a_853_, v_b_854_);
lean_dec(v_index_908_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_896_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
return v___x_911_;
}
case 1:
{
lean_object* v_index_912_; 
v_index_912_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_index_912_);
lean_dec_ref_known(v___x_907_, 1);
v___y_898_ = v___y_906_;
v_i_899_ = v_index_912_;
goto v___jp_897_;
}
default: 
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_906_, v___x_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_index_915_; 
v_index_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_index_915_);
lean_dec_ref_known(v___x_914_, 1);
v___y_898_ = v___y_906_;
v_i_899_ = v_index_915_;
goto v___jp_897_;
}
else
{
lean_object* v___x_916_; 
lean_dec(v_b_854_);
lean_dec(v_a_853_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_896_);
lean_ctor_set(v___x_916_, 1, v___y_906_);
return v___x_916_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_m_934_, lean_object* v_a_935_, lean_object* v_b_936_){
_start:
{
lean_object* v___x_937_; 
lean_inc(v_a_935_);
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_930_, v_x_931_, v_m_934_, v_a_935_);
switch(lean_obj_tag(v___x_937_))
{
case 0:
{
lean_object* v_value_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_b_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_x_931_);
lean_dec_ref(v_x_930_);
v_value_938_ = lean_ctor_get(v___x_937_, 2);
lean_inc(v_value_938_);
lean_dec_ref_known(v___x_937_, 3);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v_value_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_m_934_);
return v___x_940_;
}
case 1:
{
lean_object* v_index_941_; lean_object* v_size_942_; lean_object* v_keyArray_943_; lean_object* v___x_944_; lean_object* v___y_946_; lean_object* v_i_947_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_index_941_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_index_941_);
lean_dec_ref_known(v___x_937_, 1);
v_size_942_ = lean_ctor_get(v_m_934_, 0);
v_keyArray_943_ = lean_ctor_get(v_m_934_, 1);
v___x_944_ = lean_box(0);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v_size_942_, v___x_965_);
v___x_967_ = lean_array_get_size(v_keyArray_943_);
v___x_968_ = lean_nat_dec_lt(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v___x_966_);
lean_dec(v_index_941_);
goto v___jp_953_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_969_ = lean_unsigned_to_nat(4u);
v___x_970_ = lean_nat_mul(v___x_966_, v___x_969_);
v___x_971_ = lean_unsigned_to_nat(3u);
v___x_972_ = lean_nat_mul(v___x_967_, v___x_971_);
v___x_973_ = lean_nat_dec_le(v___x_970_, v___x_972_);
lean_dec(v___x_972_);
lean_dec(v___x_970_);
if (v___x_973_ == 0)
{
lean_dec(v___x_966_);
lean_dec(v_index_941_);
goto v___jp_953_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec_ref(v_x_931_);
lean_dec_ref(v_x_930_);
v___x_974_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_934_, v___x_966_, v_index_941_, v_a_935_, v_b_936_);
lean_dec(v_index_941_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_944_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
return v___x_975_;
}
}
v___jp_945_:
{
lean_object* v_size_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_size_948_ = lean_ctor_get(v___y_946_, 0);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_add(v_size_948_, v___x_949_);
v___x_951_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_946_, v___x_950_, v_i_947_, v_a_935_, v_b_936_);
lean_dec(v_i_947_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_944_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
return v___x_952_;
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_930_, v_x_931_, v_m_934_);
lean_inc(v_a_935_);
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_930_, v_x_931_, v___x_954_, v_a_935_);
switch(lean_obj_tag(v___x_955_))
{
case 0:
{
lean_object* v_index_956_; lean_object* v_size_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_index_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_956_);
lean_dec_ref_known(v___x_955_, 3);
v_size_957_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_size_957_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_954_, v_size_957_, v_index_956_, v_a_935_, v_b_936_);
lean_dec(v_index_956_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_944_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
return v___x_959_;
}
case 1:
{
lean_object* v_index_960_; 
v_index_960_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_960_);
lean_dec_ref_known(v___x_955_, 1);
v___y_946_ = v___x_954_;
v_i_947_ = v_index_960_;
goto v___jp_945_;
}
default: 
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_954_, v___x_961_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_index_963_; 
v_index_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_index_963_);
lean_dec_ref_known(v___x_962_, 1);
v___y_946_ = v___x_954_;
v_i_947_ = v_index_963_;
goto v___jp_945_;
}
else
{
lean_object* v___x_964_; 
lean_dec(v_b_936_);
lean_dec(v_a_935_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_944_);
lean_ctor_set(v___x_964_, 1, v___x_954_);
return v___x_964_;
}
}
}
}
}
default: 
{
lean_object* v_size_976_; lean_object* v_keyArray_977_; lean_object* v___x_978_; lean_object* v___y_980_; lean_object* v_i_981_; lean_object* v___y_988_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v_size_976_ = lean_ctor_get(v_m_934_, 0);
v_keyArray_977_ = lean_ctor_get(v_m_934_, 1);
v___x_978_ = lean_box(0);
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_add(v_size_976_, v___x_999_);
v___x_1001_ = lean_array_get_size(v_keyArray_977_);
v___x_1002_ = lean_nat_dec_lt(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
lean_dec(v___x_1000_);
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_930_, v_x_931_, v_m_934_);
v___y_988_ = v___x_1003_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1004_ = lean_unsigned_to_nat(4u);
v___x_1005_ = lean_nat_mul(v___x_1000_, v___x_1004_);
lean_dec(v___x_1000_);
v___x_1006_ = lean_unsigned_to_nat(3u);
v___x_1007_ = lean_nat_mul(v___x_1001_, v___x_1006_);
v___x_1008_ = lean_nat_dec_le(v___x_1005_, v___x_1007_);
lean_dec(v___x_1007_);
lean_dec(v___x_1005_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_1009_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_930_, v_x_931_, v_m_934_);
v___y_988_ = v___x_1009_;
goto v___jp_987_;
}
else
{
v___y_988_ = v_m_934_;
goto v___jp_987_;
}
}
v___jp_979_:
{
lean_object* v_size_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_size_982_ = lean_ctor_get(v___y_980_, 0);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_size_982_, v___x_983_);
v___x_985_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_980_, v___x_984_, v_i_981_, v_a_935_, v_b_936_);
lean_dec(v_i_981_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_978_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
return v___x_986_;
}
v___jp_987_:
{
lean_object* v___x_989_; 
lean_inc(v_a_935_);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_930_, v_x_931_, v___y_988_, v_a_935_);
switch(lean_obj_tag(v___x_989_))
{
case 0:
{
lean_object* v_index_990_; lean_object* v_size_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_index_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_index_990_);
lean_dec_ref_known(v___x_989_, 3);
v_size_991_ = lean_ctor_get(v___y_988_, 0);
lean_inc(v_size_991_);
v___x_992_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_988_, v_size_991_, v_index_990_, v_a_935_, v_b_936_);
lean_dec(v_index_990_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_978_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
return v___x_993_;
}
case 1:
{
lean_object* v_index_994_; 
v_index_994_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_index_994_);
lean_dec_ref_known(v___x_989_, 1);
v___y_980_ = v___y_988_;
v_i_981_ = v_index_994_;
goto v___jp_979_;
}
default: 
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_988_, v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_index_997_; 
v_index_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_index_997_);
lean_dec_ref_known(v___x_996_, 1);
v___y_980_ = v___y_988_;
v_i_981_ = v_index_997_;
goto v___jp_979_;
}
else
{
lean_object* v___x_998_; 
lean_dec(v_b_936_);
lean_dec(v_a_935_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_978_);
lean_ctor_set(v___x_998_, 1, v___y_988_);
return v___x_998_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg(lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_m_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1010_, v_x_1011_, v_m_1012_, v_a_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___redArg___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_m_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_ExtHashMap_get_x3f___redArg(v_x_1015_, v_x_1016_, v_m_1017_, v_a_1018_);
lean_dec(v_m_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_m_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1022_, v_x_1023_, v_m_1026_, v_a_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x3f___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_m_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_ExtHashMap_get_x3f(v_00_u03b1_1029_, v_00_u03b2_1030_, v_x_1031_, v_x_1032_, v_inst_1033_, v_inst_1034_, v_m_1035_, v_a_1036_);
lean_dec(v_m_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains___redArg(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_m_1040_, lean_object* v_a_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1038_, v_x_1039_, v_m_1040_, v_a_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___redArg___boxed(lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_m_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Std_ExtHashMap_contains___redArg(v_x_1043_, v_x_1044_, v_m_1045_, v_a_1046_);
lean_dec(v_m_1045_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_contains(lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_m_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1051_, v_x_1052_, v_m_1055_, v_a_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_contains___boxed(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_m_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Std_ExtHashMap_contains(v_00_u03b1_1058_, v_00_u03b2_1059_, v_x_1060_, v_x_1061_, v_inst_1062_, v_inst_1063_, v_m_1064_, v_a_1065_);
lean_dec(v_m_1064_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_ExtHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_1075_, v_00_u03b2_1076_, v_inst_1077_, v_inst_1078_, v_inst_1079_, v_inst_1080_);
lean_dec_ref(v_inst_1078_);
lean_dec_ref(v_inst_1077_);
return v_res_1081_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem___redArg(lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_m_1084_, lean_object* v_a_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1082_, v_inst_1083_, v_m_1084_, v_a_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_m_1089_, lean_object* v_a_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Std_ExtHashMap_instDecidableMem___redArg(v_inst_1087_, v_inst_1088_, v_m_1089_, v_a_1090_);
lean_dec(v_m_1089_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableMem(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_m_1099_, lean_object* v_a_1100_){
_start:
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1095_, v_inst_1096_, v_m_1099_, v_a_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Std_ExtHashMap_instDecidableMem(v_00_u03b1_1102_, v_00_u03b2_1103_, v_inst_1104_, v_inst_1105_, v_inst_1106_, v_inst_1107_, v_m_1108_, v_a_1109_);
lean_dec(v_m_1108_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg(lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v_val_1117_; 
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1112_, v_x_1113_, v_m_1114_, v_a_1115_);
v_val_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1117_);
lean_dec(v___x_1116_);
return v_val_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___redArg___boxed(lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_m_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_ExtHashMap_get___redArg(v_x_1118_, v_x_1119_, v_m_1120_, v_a_1121_);
lean_dec(v_m_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_m_1129_, lean_object* v_a_1130_, lean_object* v_h_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v_val_1133_; 
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1125_, v_x_1126_, v_m_1129_, v_a_1130_);
v_val_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_val_1133_);
lean_dec(v___x_1132_);
return v_val_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_m_1140_, lean_object* v_a_1141_, lean_object* v_h_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_ExtHashMap_get(v_00_u03b1_1134_, v_00_u03b2_1135_, v_x_1136_, v_x_1137_, v_inst_1138_, v_inst_1139_, v_m_1140_, v_a_1141_, v_h_1142_);
lean_dec(v_m_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg(lean_object* v_x_1144_, lean_object* v_x_1145_, lean_object* v_m_1146_, lean_object* v_a_1147_, lean_object* v_fallback_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_1144_, v_x_1145_, v_m_1146_, v_a_1147_, v_fallback_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___redArg___boxed(lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_m_1152_, lean_object* v_a_1153_, lean_object* v_fallback_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_ExtHashMap_getD___redArg(v_x_1150_, v_x_1151_, v_m_1152_, v_a_1153_, v_fallback_1154_);
lean_dec(v_fallback_1154_);
lean_dec(v_m_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD(lean_object* v_00_u03b1_1156_, lean_object* v_00_u03b2_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_m_1162_, lean_object* v_a_1163_, lean_object* v_fallback_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_1158_, v_x_1159_, v_m_1162_, v_a_1163_, v_fallback_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getD___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_m_1172_, lean_object* v_a_1173_, lean_object* v_fallback_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_ExtHashMap_getD(v_00_u03b1_1166_, v_00_u03b2_1167_, v_x_1168_, v_x_1169_, v_inst_1170_, v_inst_1171_, v_m_1172_, v_a_1173_, v_fallback_1174_);
lean_dec(v_fallback_1174_);
lean_dec(v_m_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg(lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_inst_1178_, lean_object* v_m_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_1176_, v_x_1177_, v_inst_1178_, v_m_1179_, v_a_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___redArg___boxed(lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_inst_1184_, lean_object* v_m_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_ExtHashMap_get_x21___redArg(v_x_1182_, v_x_1183_, v_inst_1184_, v_m_1185_, v_a_1186_);
lean_dec(v_m_1185_);
lean_dec(v_inst_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21(lean_object* v_00_u03b1_1188_, lean_object* v_00_u03b2_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_m_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_1190_, v_x_1191_, v_inst_1194_, v_m_1195_, v_a_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_get_x21___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_ExtHashMap_get_x21(v_00_u03b1_1198_, v_00_u03b2_1199_, v_x_1200_, v_x_1201_, v_inst_1202_, v_inst_1203_, v_inst_1204_, v_m_1205_, v_a_1206_);
lean_dec(v_m_1205_);
lean_dec(v_inst_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_m_1210_, lean_object* v_a_1211_, lean_object* v_h_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v_val_1214_; 
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1208_, v_inst_1209_, v_m_1210_, v_a_1211_);
v_val_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1214_);
lean_dec(v___x_1213_);
return v_val_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_m_1217_, lean_object* v_a_1218_, lean_object* v_h_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_1215_, v_inst_1216_, v_m_1217_, v_a_1218_, v_h_1219_);
lean_dec(v_m_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1221_, v_inst_1222_, v_m_1223_, v_a_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_1226_, v_inst_1227_, v_m_1228_, v_a_1229_);
lean_dec(v_m_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_m_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1231_, v_inst_1232_, v_inst_1233_, v_m_1234_, v_a_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_1237_, v_inst_1238_, v_inst_1239_, v_m_1240_, v_a_1241_);
lean_dec(v_m_1240_);
lean_dec(v_inst_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_1243_, lean_object* v_inst_1244_){
_start:
{
lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; 
lean_inc_ref_n(v_inst_1244_, 2);
lean_inc_ref_n(v_inst_1243_, 2);
v___f_1245_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1245_, 0, v_inst_1243_);
lean_closure_set(v___f_1245_, 1, v_inst_1244_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1246_, 0, v_inst_1243_);
lean_closure_set(v___f_1246_, 1, v_inst_1244_);
v___f_1247_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1247_, 0, v_inst_1243_);
lean_closure_set(v___f_1247_, 1, v_inst_1244_);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v___f_1245_);
lean_ctor_set(v___x_1248_, 1, v___f_1246_);
lean_ctor_set(v___x_1248_, 2, v___f_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_ExtHashMap_instGetElem_x3fMem___redArg(v_inst_1251_, v_inst_1252_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg(lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_m_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1256_, v_x_1257_, v_m_1258_, v_a_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_m_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Std_ExtHashMap_getKey_x3f___redArg(v_x_1261_, v_x_1262_, v_m_1263_, v_a_1264_);
lean_dec(v_m_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f(lean_object* v_00_u03b1_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_m_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1268_, v_x_1269_, v_m_1272_, v_a_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_ExtHashMap_getKey_x3f(v_00_u03b1_1275_, v_00_u03b2_1276_, v_x_1277_, v_x_1278_, v_inst_1279_, v_inst_1280_, v_m_1281_, v_a_1282_);
lean_dec(v_m_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg(lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v_val_1289_; 
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1284_, v_x_1285_, v_m_1286_, v_a_1287_);
v_val_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1289_);
lean_dec(v___x_1288_);
return v_val_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___redArg___boxed(lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_m_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Std_ExtHashMap_getKey___redArg(v_x_1290_, v_x_1291_, v_m_1292_, v_a_1293_);
lean_dec(v_m_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_h_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v_val_1305_; 
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1297_, v_x_1298_, v_m_1301_, v_a_1302_);
v_val_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_val_1305_);
lean_dec(v___x_1304_);
return v_val_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_m_1312_, lean_object* v_a_1313_, lean_object* v_h_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Std_ExtHashMap_getKey(v_00_u03b1_1306_, v_00_u03b2_1307_, v_x_1308_, v_x_1309_, v_inst_1310_, v_inst_1311_, v_m_1312_, v_a_1313_, v_h_1314_);
lean_dec(v_m_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg(lean_object* v_x_1316_, lean_object* v_x_1317_, lean_object* v_m_1318_, lean_object* v_a_1319_, lean_object* v_fallback_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1316_, v_x_1317_, v_m_1318_, v_a_1319_, v_fallback_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___redArg___boxed(lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_m_1324_, lean_object* v_a_1325_, lean_object* v_fallback_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_ExtHashMap_getKeyD___redArg(v_x_1322_, v_x_1323_, v_m_1324_, v_a_1325_, v_fallback_1326_);
lean_dec(v_fallback_1326_);
lean_dec(v_m_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_m_1334_, lean_object* v_a_1335_, lean_object* v_fallback_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1330_, v_x_1331_, v_m_1334_, v_a_1335_, v_fallback_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKeyD___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_m_1344_, lean_object* v_a_1345_, lean_object* v_fallback_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_ExtHashMap_getKeyD(v_00_u03b1_1338_, v_00_u03b2_1339_, v_x_1340_, v_x_1341_, v_inst_1342_, v_inst_1343_, v_m_1344_, v_a_1345_, v_fallback_1346_);
lean_dec(v_fallback_1346_);
lean_dec(v_m_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg(lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_inst_1350_, lean_object* v_m_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1348_, v_x_1349_, v_inst_1350_, v_m_1351_, v_a_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___redArg___boxed(lean_object* v_x_1354_, lean_object* v_x_1355_, lean_object* v_inst_1356_, lean_object* v_m_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_ExtHashMap_getKey_x21___redArg(v_x_1354_, v_x_1355_, v_inst_1356_, v_m_1357_, v_a_1358_);
lean_dec(v_m_1357_);
lean_dec(v_inst_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_m_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1362_, v_x_1363_, v_inst_1366_, v_m_1367_, v_a_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_m_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_ExtHashMap_getKey_x21(v_00_u03b1_1370_, v_00_u03b2_1371_, v_x_1372_, v_x_1373_, v_inst_1374_, v_inst_1375_, v_inst_1376_, v_m_1377_, v_a_1378_);
lean_dec(v_m_1377_);
lean_dec(v_inst_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase___redArg(lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v_m_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_1380_, v_x_1381_, v_m_1382_, v_a_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_erase(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_m_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_1387_, v_x_1388_, v_m_1391_, v_a_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg(lean_object* v_m_1394_){
_start:
{
lean_object* v_size_1395_; 
v_size_1395_ = lean_ctor_get(v_m_1394_, 0);
lean_inc(v_size_1395_);
return v_size_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___redArg___boxed(lean_object* v_m_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_ExtHashMap_size___redArg(v_m_1396_);
lean_dec(v_m_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_m_1404_){
_start:
{
lean_object* v_size_1405_; 
v_size_1405_ = lean_ctor_get(v_m_1404_, 0);
lean_inc(v_size_1405_);
return v_size_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_size___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_m_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_ExtHashMap_size(v_00_u03b1_1406_, v_00_u03b2_1407_, v_x_1408_, v_x_1409_, v_inst_1410_, v_inst_1411_, v_m_1412_);
lean_dec(v_m_1412_);
lean_dec_ref(v_x_1409_);
lean_dec_ref(v_x_1408_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty___redArg(lean_object* v_m_1414_){
_start:
{
lean_object* v_size_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_size_1415_ = lean_ctor_get(v_m_1414_, 0);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_nat_dec_eq(v_size_1415_, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___redArg___boxed(lean_object* v_m_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Std_ExtHashMap_isEmpty___redArg(v_m_1418_);
lean_dec(v_m_1418_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_isEmpty(lean_object* v_00_u03b1_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_m_1427_){
_start:
{
lean_object* v_size_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v_size_1428_ = lean_ctor_get(v_m_1427_, 0);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_nat_dec_eq(v_size_1428_, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_isEmpty___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_m_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Std_ExtHashMap_isEmpty(v_00_u03b1_1431_, v_00_u03b2_1432_, v_x_1433_, v_x_1434_, v_inst_1435_, v_inst_1436_, v_m_1437_);
lean_dec(v_m_1437_);
lean_dec_ref(v_x_1434_);
lean_dec_ref(v_x_1433_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList___redArg(lean_object* v_inst_1463_, lean_object* v_inst_1464_, lean_object* v_l_1465_){
_start:
{
lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___f_1466_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_1467_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__2, &l_Std_ExtHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__2);
v___x_1468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1466_, v_inst_1463_, v_inst_1464_, v___x_1467_, v_l_1465_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_ofList(lean_object* v_00_u03b1_1469_, lean_object* v_00_u03b2_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_l_1473_){
_start:
{
lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___f_1474_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_1475_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__2, &l_Std_ExtHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__2);
v___x_1476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1474_, v_inst_1471_, v_inst_1472_, v___x_1475_, v_l_1473_);
return v___x_1476_;
}
}
static lean_object* _init_l_Std_ExtHashMap_unitOfList___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_1477_; lean_object* v___x_1478_; 
v_cellCount_1477_ = lean_unsigned_to_nat(16u);
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Std_ExtHashMap_unitOfList___redArg___closed__1(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1479_ = lean_obj_once(&l_Std_ExtHashMap_unitOfList___redArg___closed__0, &l_Std_ExtHashMap_unitOfList___redArg___closed__0_once, _init_l_Std_ExtHashMap_unitOfList___redArg___closed__0);
v___x_1480_ = lean_obj_once(&l_Std_ExtHashMap_instEmptyCollection___closed__0, &l_Std_ExtHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashMap_instEmptyCollection___closed__0);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1479_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList___redArg(lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_l_1485_){
_start:
{
lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___f_1486_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_1487_ = lean_obj_once(&l_Std_ExtHashMap_unitOfList___redArg___closed__1, &l_Std_ExtHashMap_unitOfList___redArg___closed__1_once, _init_l_Std_ExtHashMap_unitOfList___redArg___closed__1);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1486_, v_inst_1483_, v_inst_1484_, v___x_1487_, v_l_1485_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfList(lean_object* v_00_u03b1_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_l_1492_){
_start:
{
lean_object* v___f_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___f_1493_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__11));
v___x_1494_ = lean_obj_once(&l_Std_ExtHashMap_unitOfList___redArg___closed__1, &l_Std_ExtHashMap_unitOfList___redArg___closed__1_once, _init_l_Std_ExtHashMap_unitOfList___redArg___closed__1);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1493_, v_inst_1490_, v_inst_1491_, v___x_1494_, v_l_1492_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg(lean_object* v_f_1496_, lean_object* v_m_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1496_, v_m_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___redArg___boxed(lean_object* v_f_1499_, lean_object* v_m_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Std_ExtHashMap_filter___redArg(v_f_1499_, v_m_1500_);
lean_dec(v_m_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter(lean_object* v_00_u03b1_1502_, lean_object* v_00_u03b2_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_f_1508_, lean_object* v_m_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1508_, v_m_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filter___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_00_u03b2_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_f_1517_, lean_object* v_m_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Std_ExtHashMap_filter(v_00_u03b1_1511_, v_00_u03b2_1512_, v_x_1513_, v_x_1514_, v_inst_1515_, v_inst_1516_, v_f_1517_, v_m_1518_);
lean_dec(v_m_1518_);
lean_dec_ref(v_x_1514_);
lean_dec_ref(v_x_1513_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg(lean_object* v_f_1520_, lean_object* v_m_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1520_, v_m_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___redArg___boxed(lean_object* v_f_1523_, lean_object* v_m_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_ExtHashMap_map___redArg(v_f_1523_, v_m_1524_);
lean_dec(v_m_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_00_u03b3_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_f_1533_, lean_object* v_m_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1533_, v_m_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_map___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_00_u03b3_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_f_1543_, lean_object* v_m_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Std_ExtHashMap_map(v_00_u03b1_1536_, v_00_u03b2_1537_, v_00_u03b3_1538_, v_x_1539_, v_x_1540_, v_inst_1541_, v_inst_1542_, v_f_1543_, v_m_1544_);
lean_dec(v_m_1544_);
lean_dec_ref(v_x_1540_);
lean_dec_ref(v_x_1539_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg(lean_object* v_f_1546_, lean_object* v_m_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1546_, v_m_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___redArg___boxed(lean_object* v_f_1549_, lean_object* v_m_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_ExtHashMap_filterMap___redArg(v_f_1549_, v_m_1550_);
lean_dec(v_m_1550_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap(lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_00_u03b3_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_m_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1559_, v_m_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_filterMap___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_00_u03b2_1563_, lean_object* v_00_u03b3_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_f_1569_, lean_object* v_m_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_ExtHashMap_filterMap(v_00_u03b1_1562_, v_00_u03b2_1563_, v_00_u03b3_1564_, v_x_1565_, v_x_1566_, v_inst_1567_, v_inst_1568_, v_f_1569_, v_m_1570_);
lean_dec(v_m_1570_);
lean_dec_ref(v_x_1566_);
lean_dec_ref(v_x_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify___redArg(lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_m_1574_, lean_object* v_a_1575_, lean_object* v_f_1576_){
_start:
{
lean_object* v___x_1577_; 
lean_inc(v_a_1575_);
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1572_, v_x_1573_, v_m_1574_, v_a_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_index_1578_; lean_object* v_value_1579_; lean_object* v_size_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_index_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_index_1578_);
v_value_1579_ = lean_ctor_get(v___x_1577_, 2);
lean_inc(v_value_1579_);
lean_dec_ref_known(v___x_1577_, 3);
v_size_1580_ = lean_ctor_get(v_m_1574_, 0);
lean_inc(v_size_1580_);
v___x_1581_ = lean_apply_1(v_f_1576_, v_value_1579_);
v___x_1582_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1574_, v_size_1580_, v_index_1578_, v_a_1575_, v___x_1581_);
lean_dec(v_index_1578_);
return v___x_1582_;
}
else
{
lean_dec(v___x_1577_);
lean_dec(v_f_1576_);
lean_dec(v_a_1575_);
return v_m_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_modify(lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_m_1589_, lean_object* v_a_1590_, lean_object* v_f_1591_){
_start:
{
lean_object* v___x_1592_; 
lean_inc(v_a_1590_);
v___x_1592_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1585_, v_x_1586_, v_m_1589_, v_a_1590_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_index_1593_; lean_object* v_value_1594_; lean_object* v_size_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_index_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_index_1593_);
v_value_1594_ = lean_ctor_get(v___x_1592_, 2);
lean_inc(v_value_1594_);
lean_dec_ref_known(v___x_1592_, 3);
v_size_1595_ = lean_ctor_get(v_m_1589_, 0);
lean_inc(v_size_1595_);
v___x_1596_ = lean_apply_1(v_f_1591_, v_value_1594_);
v___x_1597_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1589_, v_size_1595_, v_index_1593_, v_a_1590_, v___x_1596_);
lean_dec(v_index_1593_);
return v___x_1597_;
}
else
{
lean_dec(v___x_1592_);
lean_dec(v_f_1591_);
lean_dec(v_a_1590_);
return v_m_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter___redArg(lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_m_1600_, lean_object* v_a_1601_, lean_object* v_f_1602_){
_start:
{
lean_object* v___x_1603_; 
lean_inc(v_a_1601_);
lean_inc_ref(v_x_1599_);
lean_inc_ref(v_x_1598_);
v___x_1603_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1598_, v_x_1599_, v_m_1600_, v_a_1601_);
switch(lean_obj_tag(v___x_1603_))
{
case 0:
{
lean_object* v_index_1604_; lean_object* v_value_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v_x_1599_);
lean_dec_ref(v_x_1598_);
v_index_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_index_1604_);
v_value_1605_ = lean_ctor_get(v___x_1603_, 2);
lean_inc(v_value_1605_);
lean_dec_ref_known(v___x_1603_, 3);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_value_1605_);
v___x_1607_ = lean_apply_1(v_f_1602_, v___x_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_size_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v_a_1601_);
v_size_1608_ = lean_ctor_get(v_m_1600_, 0);
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_sub(v_size_1608_, v___x_1609_);
v___x_1611_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1600_, v___x_1610_, v_index_1604_);
lean_dec(v_index_1604_);
return v___x_1611_;
}
else
{
lean_object* v_val_1612_; lean_object* v_size_1613_; lean_object* v___x_1614_; 
v_val_1612_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v___x_1607_, 1);
v_size_1613_ = lean_ctor_get(v_m_1600_, 0);
lean_inc(v_size_1613_);
v___x_1614_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1600_, v_size_1613_, v_index_1604_, v_a_1601_, v_val_1612_);
lean_dec(v_index_1604_);
return v___x_1614_;
}
}
case 1:
{
lean_object* v_index_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_index_1615_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_index_1615_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_apply_1(v_f_1602_, v___x_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec(v_index_1615_);
lean_dec(v_a_1601_);
lean_dec_ref(v_x_1599_);
lean_dec_ref(v_x_1598_);
return v_m_1600_;
}
else
{
lean_object* v_val_1618_; lean_object* v___y_1620_; lean_object* v_i_1621_; lean_object* v_size_1636_; lean_object* v_keyArray_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_val_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v_size_1636_ = lean_ctor_get(v_m_1600_, 0);
v_keyArray_1637_ = lean_ctor_get(v_m_1600_, 1);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_size_1636_, v___x_1638_);
v___x_1640_ = lean_array_get_size(v_keyArray_1637_);
v___x_1641_ = lean_nat_dec_lt(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_dec(v___x_1639_);
lean_dec(v_index_1615_);
goto v___jp_1626_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1642_ = lean_unsigned_to_nat(4u);
v___x_1643_ = lean_nat_mul(v___x_1639_, v___x_1642_);
v___x_1644_ = lean_unsigned_to_nat(3u);
v___x_1645_ = lean_nat_mul(v___x_1640_, v___x_1644_);
v___x_1646_ = lean_nat_dec_le(v___x_1643_, v___x_1645_);
lean_dec(v___x_1645_);
lean_dec(v___x_1643_);
if (v___x_1646_ == 0)
{
lean_dec(v___x_1639_);
lean_dec(v_index_1615_);
goto v___jp_1626_;
}
else
{
lean_object* v___x_1647_; 
lean_dec_ref(v_x_1599_);
lean_dec_ref(v_x_1598_);
v___x_1647_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1600_, v___x_1639_, v_index_1615_, v_a_1601_, v_val_1618_);
lean_dec(v_index_1615_);
return v___x_1647_;
}
}
v___jp_1619_:
{
lean_object* v_size_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_size_1622_ = lean_ctor_get(v___y_1620_, 0);
v___x_1623_ = lean_unsigned_to_nat(1u);
v___x_1624_ = lean_nat_add(v_size_1622_, v___x_1623_);
v___x_1625_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1620_, v___x_1624_, v_i_1621_, v_a_1601_, v_val_1618_);
lean_dec(v_i_1621_);
return v___x_1625_;
}
v___jp_1626_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_inc_ref(v_x_1599_);
lean_inc_ref(v_x_1598_);
v___x_1627_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1598_, v_x_1599_, v_m_1600_);
lean_inc(v_a_1601_);
v___x_1628_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1598_, v_x_1599_, v___x_1627_, v_a_1601_);
switch(lean_obj_tag(v___x_1628_))
{
case 0:
{
lean_object* v_index_1629_; lean_object* v_size_1630_; lean_object* v___x_1631_; 
v_index_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_index_1629_);
lean_dec_ref_known(v___x_1628_, 3);
v_size_1630_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_size_1630_);
v___x_1631_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1627_, v_size_1630_, v_index_1629_, v_a_1601_, v_val_1618_);
lean_dec(v_index_1629_);
return v___x_1631_;
}
case 1:
{
lean_object* v_index_1632_; 
v_index_1632_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_index_1632_);
lean_dec_ref_known(v___x_1628_, 1);
v___y_1620_ = v___x_1627_;
v_i_1621_ = v_index_1632_;
goto v___jp_1619_;
}
default: 
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1627_, v___x_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_index_1635_; 
v_index_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_index_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___y_1620_ = v___x_1627_;
v_i_1621_ = v_index_1635_;
goto v___jp_1619_;
}
else
{
lean_dec(v_val_1618_);
lean_dec(v_a_1601_);
return v___x_1627_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_apply_1(v_f_1602_, v___x_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_dec(v_a_1601_);
lean_dec_ref(v_x_1599_);
lean_dec_ref(v_x_1598_);
return v_m_1600_;
}
else
{
lean_object* v_val_1650_; lean_object* v___y_1652_; lean_object* v_i_1653_; lean_object* v___y_1659_; lean_object* v_size_1668_; lean_object* v_keyArray_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v_size_1668_ = lean_ctor_get(v_m_1600_, 0);
v_keyArray_1669_ = lean_ctor_get(v_m_1600_, 1);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_add(v_size_1668_, v___x_1670_);
v___x_1672_ = lean_array_get_size(v_keyArray_1669_);
v___x_1673_ = lean_nat_dec_lt(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec(v___x_1671_);
lean_inc_ref(v_x_1599_);
lean_inc_ref(v_x_1598_);
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1598_, v_x_1599_, v_m_1600_);
v___y_1659_ = v___x_1674_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1675_ = lean_unsigned_to_nat(4u);
v___x_1676_ = lean_nat_mul(v___x_1671_, v___x_1675_);
lean_dec(v___x_1671_);
v___x_1677_ = lean_unsigned_to_nat(3u);
v___x_1678_ = lean_nat_mul(v___x_1672_, v___x_1677_);
v___x_1679_ = lean_nat_dec_le(v___x_1676_, v___x_1678_);
lean_dec(v___x_1678_);
lean_dec(v___x_1676_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
lean_inc_ref(v_x_1599_);
lean_inc_ref(v_x_1598_);
v___x_1680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1598_, v_x_1599_, v_m_1600_);
v___y_1659_ = v___x_1680_;
goto v___jp_1658_;
}
else
{
v___y_1659_ = v_m_1600_;
goto v___jp_1658_;
}
}
v___jp_1651_:
{
lean_object* v_size_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_size_1654_ = lean_ctor_get(v___y_1652_, 0);
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_nat_add(v_size_1654_, v___x_1655_);
v___x_1657_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1652_, v___x_1656_, v_i_1653_, v_a_1601_, v_val_1650_);
lean_dec(v_i_1653_);
return v___x_1657_;
}
v___jp_1658_:
{
lean_object* v___x_1660_; 
lean_inc(v_a_1601_);
v___x_1660_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1598_, v_x_1599_, v___y_1659_, v_a_1601_);
switch(lean_obj_tag(v___x_1660_))
{
case 0:
{
lean_object* v_index_1661_; lean_object* v_size_1662_; lean_object* v___x_1663_; 
v_index_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_index_1661_);
lean_dec_ref_known(v___x_1660_, 3);
v_size_1662_ = lean_ctor_get(v___y_1659_, 0);
lean_inc(v_size_1662_);
v___x_1663_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1659_, v_size_1662_, v_index_1661_, v_a_1601_, v_val_1650_);
lean_dec(v_index_1661_);
return v___x_1663_;
}
case 1:
{
lean_object* v_index_1664_; 
v_index_1664_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_index_1664_);
lean_dec_ref_known(v___x_1660_, 1);
v___y_1652_ = v___y_1659_;
v_i_1653_ = v_index_1664_;
goto v___jp_1651_;
}
default: 
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1659_, v___x_1665_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_index_1667_; 
v_index_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_index_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___y_1652_ = v___y_1659_;
v_i_1653_ = v_index_1667_;
goto v___jp_1651_;
}
else
{
lean_dec(v_val_1650_);
lean_dec(v_a_1601_);
return v___y_1659_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_alter(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_m_1687_, lean_object* v_a_1688_, lean_object* v_f_1689_){
_start:
{
lean_object* v___x_1690_; 
lean_inc(v_a_1688_);
lean_inc_ref(v_x_1684_);
lean_inc_ref(v_x_1683_);
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1683_, v_x_1684_, v_m_1687_, v_a_1688_);
switch(lean_obj_tag(v___x_1690_))
{
case 0:
{
lean_object* v_index_1691_; lean_object* v_value_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec_ref(v_x_1684_);
lean_dec_ref(v_x_1683_);
v_index_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_index_1691_);
v_value_1692_ = lean_ctor_get(v___x_1690_, 2);
lean_inc(v_value_1692_);
lean_dec_ref_known(v___x_1690_, 3);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_value_1692_);
v___x_1694_ = lean_apply_1(v_f_1689_, v___x_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_size_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec(v_a_1688_);
v_size_1695_ = lean_ctor_get(v_m_1687_, 0);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_sub(v_size_1695_, v___x_1696_);
v___x_1698_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1687_, v___x_1697_, v_index_1691_);
lean_dec(v_index_1691_);
return v___x_1698_;
}
else
{
lean_object* v_val_1699_; lean_object* v_size_1700_; lean_object* v___x_1701_; 
v_val_1699_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_val_1699_);
lean_dec_ref_known(v___x_1694_, 1);
v_size_1700_ = lean_ctor_get(v_m_1687_, 0);
lean_inc(v_size_1700_);
v___x_1701_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1687_, v_size_1700_, v_index_1691_, v_a_1688_, v_val_1699_);
lean_dec(v_index_1691_);
return v___x_1701_;
}
}
case 1:
{
lean_object* v_index_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_index_1702_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_index_1702_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_apply_1(v_f_1689_, v___x_1703_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_dec(v_index_1702_);
lean_dec(v_a_1688_);
lean_dec_ref(v_x_1684_);
lean_dec_ref(v_x_1683_);
return v_m_1687_;
}
else
{
lean_object* v_val_1705_; lean_object* v___y_1707_; lean_object* v_i_1708_; lean_object* v_size_1723_; lean_object* v_keyArray_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_val_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v_size_1723_ = lean_ctor_get(v_m_1687_, 0);
v_keyArray_1724_ = lean_ctor_get(v_m_1687_, 1);
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_add(v_size_1723_, v___x_1725_);
v___x_1727_ = lean_array_get_size(v_keyArray_1724_);
v___x_1728_ = lean_nat_dec_lt(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_dec(v___x_1726_);
lean_dec(v_index_1702_);
goto v___jp_1713_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1729_ = lean_unsigned_to_nat(4u);
v___x_1730_ = lean_nat_mul(v___x_1726_, v___x_1729_);
v___x_1731_ = lean_unsigned_to_nat(3u);
v___x_1732_ = lean_nat_mul(v___x_1727_, v___x_1731_);
v___x_1733_ = lean_nat_dec_le(v___x_1730_, v___x_1732_);
lean_dec(v___x_1732_);
lean_dec(v___x_1730_);
if (v___x_1733_ == 0)
{
lean_dec(v___x_1726_);
lean_dec(v_index_1702_);
goto v___jp_1713_;
}
else
{
lean_object* v___x_1734_; 
lean_dec_ref(v_x_1684_);
lean_dec_ref(v_x_1683_);
v___x_1734_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1687_, v___x_1726_, v_index_1702_, v_a_1688_, v_val_1705_);
lean_dec(v_index_1702_);
return v___x_1734_;
}
}
v___jp_1706_:
{
lean_object* v_size_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_size_1709_ = lean_ctor_get(v___y_1707_, 0);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_add(v_size_1709_, v___x_1710_);
v___x_1712_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1707_, v___x_1711_, v_i_1708_, v_a_1688_, v_val_1705_);
lean_dec(v_i_1708_);
return v___x_1712_;
}
v___jp_1713_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_inc_ref(v_x_1684_);
lean_inc_ref(v_x_1683_);
v___x_1714_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1683_, v_x_1684_, v_m_1687_);
lean_inc(v_a_1688_);
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1683_, v_x_1684_, v___x_1714_, v_a_1688_);
switch(lean_obj_tag(v___x_1715_))
{
case 0:
{
lean_object* v_index_1716_; lean_object* v_size_1717_; lean_object* v___x_1718_; 
v_index_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_index_1716_);
lean_dec_ref_known(v___x_1715_, 3);
v_size_1717_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_size_1717_);
v___x_1718_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1714_, v_size_1717_, v_index_1716_, v_a_1688_, v_val_1705_);
lean_dec(v_index_1716_);
return v___x_1718_;
}
case 1:
{
lean_object* v_index_1719_; 
v_index_1719_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_index_1719_);
lean_dec_ref_known(v___x_1715_, 1);
v___y_1707_ = v___x_1714_;
v_i_1708_ = v_index_1719_;
goto v___jp_1706_;
}
default: 
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_unsigned_to_nat(0u);
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1714_, v___x_1720_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_index_1722_; 
v_index_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_index_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___y_1707_ = v___x_1714_;
v_i_1708_ = v_index_1722_;
goto v___jp_1706_;
}
else
{
lean_dec(v_val_1705_);
lean_dec(v_a_1688_);
return v___x_1714_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_apply_1(v_f_1689_, v___x_1735_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_dec(v_a_1688_);
lean_dec_ref(v_x_1684_);
lean_dec_ref(v_x_1683_);
return v_m_1687_;
}
else
{
lean_object* v_val_1737_; lean_object* v___y_1739_; lean_object* v_i_1740_; lean_object* v___y_1746_; lean_object* v_size_1755_; lean_object* v_keyArray_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_val_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v_size_1755_ = lean_ctor_get(v_m_1687_, 0);
v_keyArray_1756_ = lean_ctor_get(v_m_1687_, 1);
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_nat_add(v_size_1755_, v___x_1757_);
v___x_1759_ = lean_array_get_size(v_keyArray_1756_);
v___x_1760_ = lean_nat_dec_lt(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec(v___x_1758_);
lean_inc_ref(v_x_1684_);
lean_inc_ref(v_x_1683_);
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1683_, v_x_1684_, v_m_1687_);
v___y_1746_ = v___x_1761_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1762_ = lean_unsigned_to_nat(4u);
v___x_1763_ = lean_nat_mul(v___x_1758_, v___x_1762_);
lean_dec(v___x_1758_);
v___x_1764_ = lean_unsigned_to_nat(3u);
v___x_1765_ = lean_nat_mul(v___x_1759_, v___x_1764_);
v___x_1766_ = lean_nat_dec_le(v___x_1763_, v___x_1765_);
lean_dec(v___x_1765_);
lean_dec(v___x_1763_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_inc_ref(v_x_1684_);
lean_inc_ref(v_x_1683_);
v___x_1767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1683_, v_x_1684_, v_m_1687_);
v___y_1746_ = v___x_1767_;
goto v___jp_1745_;
}
else
{
v___y_1746_ = v_m_1687_;
goto v___jp_1745_;
}
}
v___jp_1738_:
{
lean_object* v_size_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_size_1741_ = lean_ctor_get(v___y_1739_, 0);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_size_1741_, v___x_1742_);
v___x_1744_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1739_, v___x_1743_, v_i_1740_, v_a_1688_, v_val_1737_);
lean_dec(v_i_1740_);
return v___x_1744_;
}
v___jp_1745_:
{
lean_object* v___x_1747_; 
lean_inc(v_a_1688_);
v___x_1747_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1683_, v_x_1684_, v___y_1746_, v_a_1688_);
switch(lean_obj_tag(v___x_1747_))
{
case 0:
{
lean_object* v_index_1748_; lean_object* v_size_1749_; lean_object* v___x_1750_; 
v_index_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_index_1748_);
lean_dec_ref_known(v___x_1747_, 3);
v_size_1749_ = lean_ctor_get(v___y_1746_, 0);
lean_inc(v_size_1749_);
v___x_1750_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1746_, v_size_1749_, v_index_1748_, v_a_1688_, v_val_1737_);
lean_dec(v_index_1748_);
return v___x_1750_;
}
case 1:
{
lean_object* v_index_1751_; 
v_index_1751_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_index_1751_);
lean_dec_ref_known(v___x_1747_, 1);
v___y_1739_ = v___y_1746_;
v_i_1740_ = v_index_1751_;
goto v___jp_1738_;
}
default: 
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1746_, v___x_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_index_1754_; 
v_index_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_index_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___y_1739_ = v___y_1746_;
v_i_1740_ = v_index_1754_;
goto v___jp_1738_;
}
else
{
lean_dec(v_val_1737_);
lean_dec(v_a_1688_);
return v___y_1746_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg___lam__0(lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v_____s_1771_){
_start:
{
lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___y_1775_; lean_object* v_i_1776_; lean_object* v___y_1783_; lean_object* v___y_1795_; lean_object* v_i_1796_; lean_object* v___x_1814_; 
v_fst_1772_ = lean_ctor_get(v_x_1770_, 0);
lean_inc_n(v_fst_1772_, 2);
v_snd_1773_ = lean_ctor_get(v_x_1770_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v_x_1770_);
lean_inc_ref(v_x_1769_);
lean_inc_ref(v_x_1768_);
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1768_, v_x_1769_, v_____s_1771_, v_fst_1772_);
switch(lean_obj_tag(v___x_1814_))
{
case 0:
{
lean_object* v_index_1815_; lean_object* v_size_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v_x_1769_);
lean_dec_ref(v_x_1768_);
v_index_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_index_1815_);
lean_dec_ref_known(v___x_1814_, 3);
v_size_1816_ = lean_ctor_get(v_____s_1771_, 0);
lean_inc(v_size_1816_);
v___x_1817_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_1771_, v_size_1816_, v_index_1815_, v_fst_1772_, v_snd_1773_);
lean_dec(v_index_1815_);
v___x_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
case 1:
{
lean_object* v_index_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1838_; 
v_index_1819_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1821_ = v___x_1814_;
v_isShared_1822_ = v_isSharedCheck_1838_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_index_1819_);
lean_dec(v___x_1814_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1838_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_size_1823_; lean_object* v_keyArray_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_size_1823_ = lean_ctor_get(v_____s_1771_, 0);
v_keyArray_1824_ = lean_ctor_get(v_____s_1771_, 1);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_size_1823_, v___x_1825_);
v___x_1827_ = lean_array_get_size(v_keyArray_1824_);
v___x_1828_ = lean_nat_dec_lt(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec(v___x_1826_);
lean_del_object(v___x_1821_);
lean_dec(v_index_1819_);
goto v___jp_1802_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1829_ = lean_unsigned_to_nat(4u);
v___x_1830_ = lean_nat_mul(v___x_1826_, v___x_1829_);
v___x_1831_ = lean_unsigned_to_nat(3u);
v___x_1832_ = lean_nat_mul(v___x_1827_, v___x_1831_);
v___x_1833_ = lean_nat_dec_le(v___x_1830_, v___x_1832_);
lean_dec(v___x_1832_);
lean_dec(v___x_1830_);
if (v___x_1833_ == 0)
{
lean_dec(v___x_1826_);
lean_del_object(v___x_1821_);
lean_dec(v_index_1819_);
goto v___jp_1802_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec_ref(v_x_1769_);
lean_dec_ref(v_x_1768_);
v___x_1834_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_1771_, v___x_1826_, v_index_1819_, v_fst_1772_, v_snd_1773_);
lean_dec(v_index_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1834_);
v___x_1836_ = v___x_1821_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
default: 
{
lean_object* v_size_1839_; lean_object* v_keyArray_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_size_1839_ = lean_ctor_get(v_____s_1771_, 0);
v_keyArray_1840_ = lean_ctor_get(v_____s_1771_, 1);
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_add(v_size_1839_, v___x_1841_);
v___x_1843_ = lean_array_get_size(v_keyArray_1840_);
v___x_1844_ = lean_nat_dec_lt(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v___x_1842_);
lean_inc_ref(v_x_1769_);
lean_inc_ref(v_x_1768_);
v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1768_, v_x_1769_, v_____s_1771_);
v___y_1783_ = v___x_1845_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1846_ = lean_unsigned_to_nat(4u);
v___x_1847_ = lean_nat_mul(v___x_1842_, v___x_1846_);
lean_dec(v___x_1842_);
v___x_1848_ = lean_unsigned_to_nat(3u);
v___x_1849_ = lean_nat_mul(v___x_1843_, v___x_1848_);
v___x_1850_ = lean_nat_dec_le(v___x_1847_, v___x_1849_);
lean_dec(v___x_1849_);
lean_dec(v___x_1847_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
lean_inc_ref(v_x_1769_);
lean_inc_ref(v_x_1768_);
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1768_, v_x_1769_, v_____s_1771_);
v___y_1783_ = v___x_1851_;
goto v___jp_1782_;
}
else
{
v___y_1783_ = v_____s_1771_;
goto v___jp_1782_;
}
}
}
}
v___jp_1774_:
{
lean_object* v_size_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_size_1777_ = lean_ctor_get(v___y_1775_, 0);
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_size_1777_, v___x_1778_);
v___x_1780_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1775_, v___x_1779_, v_i_1776_, v_fst_1772_, v_snd_1773_);
lean_dec(v_i_1776_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
v___jp_1782_:
{
lean_object* v___x_1784_; 
lean_inc(v_fst_1772_);
v___x_1784_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1768_, v_x_1769_, v___y_1783_, v_fst_1772_);
switch(lean_obj_tag(v___x_1784_))
{
case 0:
{
lean_object* v_index_1785_; lean_object* v_size_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_index_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_index_1785_);
lean_dec_ref_known(v___x_1784_, 3);
v_size_1786_ = lean_ctor_get(v___y_1783_, 0);
lean_inc(v_size_1786_);
v___x_1787_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1783_, v_size_1786_, v_index_1785_, v_fst_1772_, v_snd_1773_);
lean_dec(v_index_1785_);
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
case 1:
{
lean_object* v_index_1789_; 
v_index_1789_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_index_1789_);
lean_dec_ref_known(v___x_1784_, 1);
v___y_1775_ = v___y_1783_;
v_i_1776_ = v_index_1789_;
goto v___jp_1774_;
}
default: 
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1783_, v___x_1790_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_index_1792_; 
v_index_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_index_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___y_1775_ = v___y_1783_;
v_i_1776_ = v_index_1792_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1793_; 
lean_dec(v_snd_1773_);
lean_dec(v_fst_1772_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___y_1783_);
return v___x_1793_;
}
}
}
}
v___jp_1794_:
{
lean_object* v_size_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_size_1797_ = lean_ctor_get(v___y_1795_, 0);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_add(v_size_1797_, v___x_1798_);
v___x_1800_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1795_, v___x_1799_, v_i_1796_, v_fst_1772_, v_snd_1773_);
lean_dec(v_i_1796_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
v___jp_1802_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_inc_ref(v_x_1769_);
lean_inc_ref(v_x_1768_);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1768_, v_x_1769_, v_____s_1771_);
lean_inc(v_fst_1772_);
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1768_, v_x_1769_, v___x_1803_, v_fst_1772_);
switch(lean_obj_tag(v___x_1804_))
{
case 0:
{
lean_object* v_index_1805_; lean_object* v_size_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_index_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_index_1805_);
lean_dec_ref_known(v___x_1804_, 3);
v_size_1806_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_size_1806_);
v___x_1807_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1803_, v_size_1806_, v_index_1805_, v_fst_1772_, v_snd_1773_);
lean_dec(v_index_1805_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
case 1:
{
lean_object* v_index_1809_; 
v_index_1809_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_index_1809_);
lean_dec_ref_known(v___x_1804_, 1);
v___y_1795_ = v___x_1803_;
v_i_1796_ = v_index_1809_;
goto v___jp_1794_;
}
default: 
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1803_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_index_1812_; 
v_index_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_index_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___y_1795_ = v___x_1803_;
v_i_1796_ = v_index_1812_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1813_; 
lean_dec(v_snd_1773_);
lean_dec(v_fst_1772_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1803_);
return v___x_1813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany___redArg(lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_inst_1854_, lean_object* v_m_1855_, lean_object* v_l_1856_){
_start:
{
lean_object* v___f_1857_; lean_object* v___x_1858_; 
v___f_1857_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1857_, 0, v_x_1852_);
lean_closure_set(v___f_1857_, 1, v_x_1853_);
v___x_1858_ = lean_apply_4(v_inst_1854_, lean_box(0), v_l_1856_, v_m_1855_, v___f_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertMany(lean_object* v_00_u03b1_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_00_u03c1_1865_, lean_object* v_inst_1866_, lean_object* v_m_1867_, lean_object* v_l_1868_){
_start:
{
lean_object* v___f_1869_; lean_object* v___x_1870_; 
v___f_1869_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1869_, 0, v_x_1861_);
lean_closure_set(v___f_1869_, 1, v_x_1862_);
v___x_1870_ = lean_apply_4(v_inst_1866_, lean_box(0), v_l_1868_, v_m_1867_, v___f_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_a_1873_, lean_object* v_____s_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___y_1877_; lean_object* v_i_1878_; lean_object* v___y_1885_; lean_object* v___y_1897_; lean_object* v_i_1898_; lean_object* v___x_1916_; 
v___x_1875_ = lean_box(0);
lean_inc(v_a_1873_);
lean_inc_ref(v_x_1872_);
lean_inc_ref(v_x_1871_);
v___x_1916_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1871_, v_x_1872_, v_____s_1874_, v_a_1873_);
switch(lean_obj_tag(v___x_1916_))
{
case 0:
{
lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1916_, 3);
lean_dec(v_a_1873_);
lean_dec_ref(v_x_1872_);
lean_dec_ref(v_x_1871_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_____s_1874_);
return v___x_1917_;
}
case 1:
{
lean_object* v_index_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1937_; 
v_index_1918_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1937_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_index_1918_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1937_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_size_1922_; lean_object* v_keyArray_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_size_1922_ = lean_ctor_get(v_____s_1874_, 0);
v_keyArray_1923_ = lean_ctor_get(v_____s_1874_, 1);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_add(v_size_1922_, v___x_1924_);
v___x_1926_ = lean_array_get_size(v_keyArray_1923_);
v___x_1927_ = lean_nat_dec_lt(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_dec(v___x_1925_);
lean_del_object(v___x_1920_);
lean_dec(v_index_1918_);
goto v___jp_1904_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1928_ = lean_unsigned_to_nat(4u);
v___x_1929_ = lean_nat_mul(v___x_1925_, v___x_1928_);
v___x_1930_ = lean_unsigned_to_nat(3u);
v___x_1931_ = lean_nat_mul(v___x_1926_, v___x_1930_);
v___x_1932_ = lean_nat_dec_le(v___x_1929_, v___x_1931_);
lean_dec(v___x_1931_);
lean_dec(v___x_1929_);
if (v___x_1932_ == 0)
{
lean_dec(v___x_1925_);
lean_del_object(v___x_1920_);
lean_dec(v_index_1918_);
goto v___jp_1904_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v_x_1872_);
lean_dec_ref(v_x_1871_);
v___x_1933_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_1874_, v___x_1925_, v_index_1918_, v_a_1873_, v___x_1875_);
lean_dec(v_index_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1933_);
v___x_1935_ = v___x_1920_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
default: 
{
lean_object* v_size_1938_; lean_object* v_keyArray_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_size_1938_ = lean_ctor_get(v_____s_1874_, 0);
v_keyArray_1939_ = lean_ctor_get(v_____s_1874_, 1);
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_add(v_size_1938_, v___x_1940_);
v___x_1942_ = lean_array_get_size(v_keyArray_1939_);
v___x_1943_ = lean_nat_dec_lt(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v___x_1941_);
lean_inc_ref(v_x_1872_);
lean_inc_ref(v_x_1871_);
v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1871_, v_x_1872_, v_____s_1874_);
v___y_1885_ = v___x_1944_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1945_ = lean_unsigned_to_nat(4u);
v___x_1946_ = lean_nat_mul(v___x_1941_, v___x_1945_);
lean_dec(v___x_1941_);
v___x_1947_ = lean_unsigned_to_nat(3u);
v___x_1948_ = lean_nat_mul(v___x_1942_, v___x_1947_);
v___x_1949_ = lean_nat_dec_le(v___x_1946_, v___x_1948_);
lean_dec(v___x_1948_);
lean_dec(v___x_1946_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_inc_ref(v_x_1872_);
lean_inc_ref(v_x_1871_);
v___x_1950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1871_, v_x_1872_, v_____s_1874_);
v___y_1885_ = v___x_1950_;
goto v___jp_1884_;
}
else
{
v___y_1885_ = v_____s_1874_;
goto v___jp_1884_;
}
}
}
}
v___jp_1876_:
{
lean_object* v_size_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_size_1879_ = lean_ctor_get(v___y_1877_, 0);
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_add(v_size_1879_, v___x_1880_);
v___x_1882_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1877_, v___x_1881_, v_i_1878_, v_a_1873_, v___x_1875_);
lean_dec(v_i_1878_);
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
v___jp_1884_:
{
lean_object* v___x_1886_; 
lean_inc(v_a_1873_);
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1871_, v_x_1872_, v___y_1885_, v_a_1873_);
switch(lean_obj_tag(v___x_1886_))
{
case 0:
{
lean_object* v_index_1887_; lean_object* v_size_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_index_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_index_1887_);
lean_dec_ref_known(v___x_1886_, 3);
v_size_1888_ = lean_ctor_get(v___y_1885_, 0);
lean_inc(v_size_1888_);
v___x_1889_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1885_, v_size_1888_, v_index_1887_, v_a_1873_, v___x_1875_);
lean_dec(v_index_1887_);
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
case 1:
{
lean_object* v_index_1891_; 
v_index_1891_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_index_1891_);
lean_dec_ref_known(v___x_1886_, 1);
v___y_1877_ = v___y_1885_;
v_i_1878_ = v_index_1891_;
goto v___jp_1876_;
}
default: 
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1885_, v___x_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_index_1894_; 
v_index_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_index_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___y_1877_ = v___y_1885_;
v_i_1878_ = v_index_1894_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1895_; 
lean_dec(v_a_1873_);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___y_1885_);
return v___x_1895_;
}
}
}
}
v___jp_1896_:
{
lean_object* v_size_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_size_1899_ = lean_ctor_get(v___y_1897_, 0);
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = lean_nat_add(v_size_1899_, v___x_1900_);
v___x_1902_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1897_, v___x_1901_, v_i_1898_, v_a_1873_, v___x_1875_);
lean_dec(v_i_1898_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
v___jp_1904_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_inc_ref(v_x_1872_);
lean_inc_ref(v_x_1871_);
v___x_1905_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1871_, v_x_1872_, v_____s_1874_);
lean_inc(v_a_1873_);
v___x_1906_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1871_, v_x_1872_, v___x_1905_, v_a_1873_);
switch(lean_obj_tag(v___x_1906_))
{
case 0:
{
lean_object* v_index_1907_; lean_object* v_size_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_index_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_index_1907_);
lean_dec_ref_known(v___x_1906_, 3);
v_size_1908_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_size_1908_);
v___x_1909_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1905_, v_size_1908_, v_index_1907_, v_a_1873_, v___x_1875_);
lean_dec(v_index_1907_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
case 1:
{
lean_object* v_index_1911_; 
v_index_1911_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_index_1911_);
lean_dec_ref_known(v___x_1906_, 1);
v___y_1897_ = v___x_1905_;
v_i_1898_ = v_index_1911_;
goto v___jp_1896_;
}
default: 
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1905_, v___x_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_index_1914_; 
v_index_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_index_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___y_1897_ = v___x_1905_;
v_i_1898_ = v_index_1914_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1915_; 
lean_dec(v_a_1873_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1905_);
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_inst_1953_, lean_object* v_m_1954_, lean_object* v_l_1955_){
_start:
{
lean_object* v___f_1956_; lean_object* v___x_1957_; 
v___f_1956_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1956_, 0, v_x_1951_);
lean_closure_set(v___f_1956_, 1, v_x_1952_);
v___x_1957_ = lean_apply_4(v_inst_1953_, lean_box(0), v_l_1955_, v_m_1954_, v___f_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_00_u03c1_1963_, lean_object* v_inst_1964_, lean_object* v_m_1965_, lean_object* v_l_1966_){
_start:
{
lean_object* v___f_1967_; lean_object* v___x_1968_; 
v___f_1967_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1967_, 0, v_x_1959_);
lean_closure_set(v___f_1967_, 1, v_x_1960_);
v___x_1968_ = lean_apply_4(v_inst_1964_, lean_box(0), v_l_1966_, v_m_1965_, v___f_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg___lam__0(lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_a_1971_, lean_object* v_b_1972_, lean_object* v_acc_1973_){
_start:
{
lean_object* v___y_1975_; lean_object* v_i_1976_; lean_object* v___y_1995_; lean_object* v_i_1996_; lean_object* v___y_2003_; lean_object* v___x_2014_; 
lean_inc(v_a_1971_);
lean_inc_ref(v_x_1970_);
lean_inc_ref(v_x_1969_);
v___x_2014_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1969_, v_x_1970_, v_acc_1973_, v_a_1971_);
switch(lean_obj_tag(v___x_2014_))
{
case 0:
{
lean_object* v___x_2015_; 
lean_dec_ref_known(v___x_2014_, 3);
lean_dec(v_b_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_x_1970_);
lean_dec_ref(v_x_1969_);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_acc_1973_);
return v___x_2015_;
}
case 1:
{
lean_object* v_index_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2035_; 
v_index_2016_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2018_ = v___x_2014_;
v_isShared_2019_ = v_isSharedCheck_2035_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_index_2016_);
lean_dec(v___x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2035_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_size_2020_; lean_object* v_keyArray_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_size_2020_ = lean_ctor_get(v_acc_1973_, 0);
v_keyArray_2021_ = lean_ctor_get(v_acc_1973_, 1);
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = lean_nat_add(v_size_2020_, v___x_2022_);
v___x_2024_ = lean_array_get_size(v_keyArray_2021_);
v___x_2025_ = lean_nat_dec_lt(v___x_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_dec(v___x_2023_);
lean_del_object(v___x_2018_);
lean_dec(v_index_2016_);
goto v___jp_1982_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2026_ = lean_unsigned_to_nat(4u);
v___x_2027_ = lean_nat_mul(v___x_2023_, v___x_2026_);
v___x_2028_ = lean_unsigned_to_nat(3u);
v___x_2029_ = lean_nat_mul(v___x_2024_, v___x_2028_);
v___x_2030_ = lean_nat_dec_le(v___x_2027_, v___x_2029_);
lean_dec(v___x_2029_);
lean_dec(v___x_2027_);
if (v___x_2030_ == 0)
{
lean_dec(v___x_2023_);
lean_del_object(v___x_2018_);
lean_dec(v_index_2016_);
goto v___jp_1982_;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
lean_dec_ref(v_x_1970_);
lean_dec_ref(v_x_1969_);
v___x_2031_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1973_, v___x_2023_, v_index_2016_, v_a_1971_, v_b_1972_);
lean_dec(v_index_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2031_);
v___x_2033_ = v___x_2018_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
default: 
{
lean_object* v_size_2036_; lean_object* v_keyArray_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v_size_2036_ = lean_ctor_get(v_acc_1973_, 0);
v_keyArray_2037_ = lean_ctor_get(v_acc_1973_, 1);
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_size_2036_, v___x_2038_);
v___x_2040_ = lean_array_get_size(v_keyArray_2037_);
v___x_2041_ = lean_nat_dec_lt(v___x_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec(v___x_2039_);
lean_inc_ref(v_x_1970_);
lean_inc_ref(v_x_1969_);
v___x_2042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1969_, v_x_1970_, v_acc_1973_);
v___y_2003_ = v___x_2042_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2043_ = lean_unsigned_to_nat(4u);
v___x_2044_ = lean_nat_mul(v___x_2039_, v___x_2043_);
lean_dec(v___x_2039_);
v___x_2045_ = lean_unsigned_to_nat(3u);
v___x_2046_ = lean_nat_mul(v___x_2040_, v___x_2045_);
v___x_2047_ = lean_nat_dec_le(v___x_2044_, v___x_2046_);
lean_dec(v___x_2046_);
lean_dec(v___x_2044_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_inc_ref(v_x_1970_);
lean_inc_ref(v_x_1969_);
v___x_2048_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1969_, v_x_1970_, v_acc_1973_);
v___y_2003_ = v___x_2048_;
goto v___jp_2002_;
}
else
{
v___y_2003_ = v_acc_1973_;
goto v___jp_2002_;
}
}
}
}
v___jp_1974_:
{
lean_object* v_size_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_size_1977_ = lean_ctor_get(v___y_1975_, 0);
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_size_1977_, v___x_1978_);
v___x_1980_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1975_, v___x_1979_, v_i_1976_, v_a_1971_, v_b_1972_);
lean_dec(v_i_1976_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
v___jp_1982_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_inc_ref(v_x_1970_);
lean_inc_ref(v_x_1969_);
v___x_1983_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1969_, v_x_1970_, v_acc_1973_);
lean_inc(v_a_1971_);
v___x_1984_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1969_, v_x_1970_, v___x_1983_, v_a_1971_);
switch(lean_obj_tag(v___x_1984_))
{
case 0:
{
lean_object* v_index_1985_; lean_object* v_size_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_index_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_index_1985_);
lean_dec_ref_known(v___x_1984_, 3);
v_size_1986_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_size_1986_);
v___x_1987_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1983_, v_size_1986_, v_index_1985_, v_a_1971_, v_b_1972_);
lean_dec(v_index_1985_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
case 1:
{
lean_object* v_index_1989_; 
v_index_1989_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_index_1989_);
lean_dec_ref_known(v___x_1984_, 1);
v___y_1975_ = v___x_1983_;
v_i_1976_ = v_index_1989_;
goto v___jp_1974_;
}
default: 
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1983_, v___x_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_index_1992_; 
v_index_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_index_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1975_ = v___x_1983_;
v_i_1976_ = v_index_1992_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_b_1972_);
lean_dec(v_a_1971_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1983_);
return v___x_1993_;
}
}
}
}
v___jp_1994_:
{
lean_object* v_size_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_size_1997_ = lean_ctor_get(v___y_1995_, 0);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_add(v_size_1997_, v___x_1998_);
v___x_2000_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1995_, v___x_1999_, v_i_1996_, v_a_1971_, v_b_1972_);
lean_dec(v_i_1996_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
v___jp_2002_:
{
lean_object* v___x_2004_; 
lean_inc(v_a_1971_);
v___x_2004_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1969_, v_x_1970_, v___y_2003_, v_a_1971_);
switch(lean_obj_tag(v___x_2004_))
{
case 0:
{
lean_object* v_index_2005_; lean_object* v_size_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_index_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_index_2005_);
lean_dec_ref_known(v___x_2004_, 3);
v_size_2006_ = lean_ctor_get(v___y_2003_, 0);
lean_inc(v_size_2006_);
v___x_2007_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2003_, v_size_2006_, v_index_2005_, v_a_1971_, v_b_1972_);
lean_dec(v_index_2005_);
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
case 1:
{
lean_object* v_index_2009_; 
v_index_2009_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_index_2009_);
lean_dec_ref_known(v___x_2004_, 1);
v___y_1995_ = v___y_2003_;
v_i_1996_ = v_index_2009_;
goto v___jp_1994_;
}
default: 
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2003_, v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_index_2012_; 
v_index_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_index_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1995_ = v___y_2003_;
v_i_1996_ = v_index_2012_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_b_1972_);
lean_dec(v_a_1971_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___y_2003_);
return v___x_2013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union___redArg(lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v_m_u2081_2053_, lean_object* v_m_u2082_2054_){
_start:
{
lean_object* v_size_2055_; lean_object* v_size_2056_; uint8_t v___x_2057_; 
v_size_2055_ = lean_ctor_get(v_m_u2081_2053_, 0);
v_size_2056_ = lean_ctor_get(v_m_u2082_2054_, 0);
v___x_2057_ = lean_nat_dec_le(v_size_2055_, v_size_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___f_2058_; lean_object* v___x_2059_; 
v___f_2058_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2058_, v_x_2051_, v_x_2052_, v_m_u2081_2053_, v_m_u2082_2054_);
return v___x_2059_;
}
else
{
lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___f_2060_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2060_, 0, v_x_2051_);
lean_closure_set(v___f_2060_, 1, v_x_2052_);
v___x_2061_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v___x_2062_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2061_, v___f_2060_, v_m_u2082_2054_, v_m_u2081_2053_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_union(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_m_u2081_2069_, lean_object* v_m_u2082_2070_){
_start:
{
lean_object* v_size_2071_; lean_object* v_size_2072_; uint8_t v___x_2073_; 
v_size_2071_ = lean_ctor_get(v_m_u2081_2069_, 0);
v_size_2072_ = lean_ctor_get(v_m_u2082_2070_, 0);
v___x_2073_ = lean_nat_dec_le(v_size_2071_, v_size_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___f_2074_; lean_object* v___x_2075_; 
v___f_2074_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2074_, v_x_2065_, v_x_2066_, v_m_u2081_2069_, v_m_u2082_2070_);
return v___x_2075_;
}
else
{
lean_object* v___f_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___f_2076_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2076_, 0, v_x_2065_);
lean_closure_set(v___f_2076_, 1, v_x_2066_);
v___x_2077_ = ((lean_object*)(l_Std_ExtHashMap_ofList___redArg___closed__9));
v___x_2078_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2077_, v___f_2076_, v_m_u2082_2070_, v_m_u2081_2069_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_2081_, 0, lean_box(0));
lean_closure_set(v___x_2081_, 1, lean_box(0));
lean_closure_set(v___x_2081_, 2, v_x_2079_);
lean_closure_set(v___x_2081_, 3, v_x_2080_);
lean_closure_set(v___x_2081_, 4, lean_box(0));
lean_closure_set(v___x_2081_, 5, lean_box(0));
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_union), 8, 6);
lean_closure_set(v___x_2088_, 0, lean_box(0));
lean_closure_set(v___x_2088_, 1, lean_box(0));
lean_closure_set(v___x_2088_, 2, v_x_2084_);
lean_closure_set(v___x_2088_, 3, v_x_2085_);
lean_closure_set(v___x_2088_, 4, lean_box(0));
lean_closure_set(v___x_2088_, 5, lean_box(0));
return v___x_2088_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_inst_2091_, lean_object* v_m_u2081_2092_, lean_object* v_m_u2082_2093_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_2089_, v_x_2090_, v_inst_2091_, v_m_u2081_2092_, v_m_u2082_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_inst_2097_, lean_object* v_m_u2081_2098_, lean_object* v_m_u2082_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_2095_, v_x_2096_, v_inst_2097_, v_m_u2081_2098_, v_m_u2082_2099_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_inst_2104_){
_start:
{
lean_object* v___f_2105_; 
v___f_2105_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2105_, 0, v_x_2102_);
lean_closure_set(v___f_2105_, 1, v_x_2103_);
lean_closure_set(v___f_2105_, 2, v_inst_2104_);
return v___f_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_x_2108_, lean_object* v_x_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_){
_start:
{
lean_object* v___f_2113_; 
v___f_2113_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2113_, 0, v_x_2108_);
lean_closure_set(v___f_2113_, 1, v_x_2109_);
lean_closure_set(v___f_2113_, 2, v_inst_2112_);
return v___f_2113_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
uint8_t v___x_2119_; 
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2114_, v_inst_2115_, v_inst_2116_, v_x_2117_, v_x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
uint8_t v_res_2125_; lean_object* v_r_2126_; 
v_res_2125_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_2120_, v_inst_2121_, v_inst_2122_, v_x_2123_, v_x_2124_);
v_r_2126_ = lean_box(v_res_2125_);
return v_r_2126_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2127_, lean_object* v_00_u03b2_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2129_, v_inst_2131_, v_inst_2132_, v_x_2134_, v_x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2137_, lean_object* v_00_u03b2_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_Std_ExtHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_2137_, v_00_u03b2_2138_, v_inst_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_, v_x_2144_, v_x_2145_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter___redArg(lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_m_u2081_2150_, lean_object* v_m_u2082_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_2148_, v_x_2149_, v_m_u2081_2150_, v_m_u2082_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_inter(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_m_u2081_2159_, lean_object* v_m_u2082_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_2155_, v_x_2156_, v_m_u2081_2159_, v_m_u2082_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_2164_, 0, lean_box(0));
lean_closure_set(v___x_2164_, 1, lean_box(0));
lean_closure_set(v___x_2164_, 2, v_x_2162_);
lean_closure_set(v___x_2164_, 3, v_x_2163_);
lean_closure_set(v___x_2164_, 4, lean_box(0));
lean_closure_set(v___x_2164_, 5, lean_box(0));
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_inter), 8, 6);
lean_closure_set(v___x_2171_, 0, lean_box(0));
lean_closure_set(v___x_2171_, 1, lean_box(0));
lean_closure_set(v___x_2171_, 2, v_x_2167_);
lean_closure_set(v___x_2171_, 3, v_x_2168_);
lean_closure_set(v___x_2171_, 4, lean_box(0));
lean_closure_set(v___x_2171_, 5, lean_box(0));
return v___x_2171_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashMap_diff___redArg___lam__0(lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_m_u2082_2174_, uint8_t v___x_2175_, lean_object* v_k_2176_, lean_object* v_x_2177_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_2172_, v_x_2173_, v_m_u2082_2174_, v_k_2176_);
if (v___x_2178_ == 0)
{
return v___x_2175_;
}
else
{
uint8_t v___x_2179_; 
v___x_2179_ = 0;
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_2180_, lean_object* v_x_2181_, lean_object* v_m_u2082_2182_, lean_object* v___x_2183_, lean_object* v_k_2184_, lean_object* v_x_2185_){
_start:
{
uint8_t v___x_106__boxed_2186_; uint8_t v_res_2187_; lean_object* v_r_2188_; 
v___x_106__boxed_2186_ = lean_unbox(v___x_2183_);
v_res_2187_ = l_Std_ExtHashMap_diff___redArg___lam__0(v_x_2180_, v_x_2181_, v_m_u2082_2182_, v___x_106__boxed_2186_, v_k_2184_, v_x_2185_);
lean_dec(v_x_2185_);
lean_dec(v_m_u2082_2182_);
v_r_2188_ = lean_box(v_res_2187_);
return v_r_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff___redArg(lean_object* v_x_2189_, lean_object* v_x_2190_, lean_object* v_m_u2081_2191_, lean_object* v_m_u2082_2192_){
_start:
{
lean_object* v_size_2193_; lean_object* v_size_2194_; uint8_t v___x_2195_; 
v_size_2193_ = lean_ctor_get(v_m_u2081_2191_, 0);
v_size_2194_ = lean_ctor_get(v_m_u2082_2192_, 0);
v___x_2195_ = lean_nat_dec_le(v_size_2193_, v_size_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___f_2196_; lean_object* v___x_2197_; 
v___f_2196_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_2197_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2196_, v_x_2189_, v_x_2190_, v_m_u2081_2191_, v_m_u2082_2192_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(v___x_2195_);
v___f_2199_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2199_, 0, v_x_2189_);
lean_closure_set(v___f_2199_, 1, v_x_2190_);
lean_closure_set(v___f_2199_, 2, v_m_u2082_2192_);
lean_closure_set(v___f_2199_, 3, v___x_2198_);
v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2199_, v_m_u2081_2191_);
lean_dec(v_m_u2081_2191_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_diff(lean_object* v_00_u03b1_2201_, lean_object* v_00_u03b2_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_m_u2081_2207_, lean_object* v_m_u2082_2208_){
_start:
{
lean_object* v_size_2209_; lean_object* v_size_2210_; uint8_t v___x_2211_; 
v_size_2209_ = lean_ctor_get(v_m_u2081_2207_, 0);
v_size_2210_ = lean_ctor_get(v_m_u2082_2208_, 0);
v___x_2211_ = lean_nat_dec_le(v_size_2209_, v_size_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___f_2212_; lean_object* v___x_2213_; 
v___f_2212_ = ((lean_object*)(l_Std_ExtHashMap_union___redArg___closed__0));
v___x_2213_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2212_, v_x_2203_, v_x_2204_, v_m_u2081_2207_, v_m_u2082_2208_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_box(v___x_2211_);
v___f_2215_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2215_, 0, v_x_2203_);
lean_closure_set(v___f_2215_, 1, v_x_2204_);
lean_closure_set(v___f_2215_, 2, v_m_u2082_2208_);
lean_closure_set(v___f_2215_, 3, v___x_2214_);
v___x_2216_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2215_, v_m_u2081_2207_);
lean_dec(v_m_u2081_2207_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_2219_, 0, lean_box(0));
lean_closure_set(v___x_2219_, 1, lean_box(0));
lean_closure_set(v___x_2219_, 2, v_x_2217_);
lean_closure_set(v___x_2219_, 3, v_x_2218_);
lean_closure_set(v___x_2219_, 4, lean_box(0));
lean_closure_set(v___x_2219_, 5, lean_box(0));
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2220_, lean_object* v_00_u03b2_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_closure((void*)(l_Std_ExtHashMap_diff), 8, 6);
lean_closure_set(v___x_2226_, 0, lean_box(0));
lean_closure_set(v___x_2226_, 1, lean_box(0));
lean_closure_set(v___x_2226_, 2, v_x_2222_);
lean_closure_set(v___x_2226_, 3, v_x_2223_);
lean_closure_set(v___x_2226_, 4, lean_box(0));
lean_closure_set(v___x_2226_, 5, lean_box(0));
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray___redArg(lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_l_2233_){
_start:
{
lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___f_2234_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_2235_ = lean_obj_once(&l_Std_ExtHashMap_unitOfList___redArg___closed__1, &l_Std_ExtHashMap_unitOfList___redArg___closed__1_once, _init_l_Std_ExtHashMap_unitOfList___redArg___closed__1);
v___x_2236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2234_, v_inst_2231_, v_inst_2232_, v___x_2235_, v_l_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashMap_unitOfArray(lean_object* v_00_u03b1_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_l_2240_){
_start:
{
lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___f_2241_ = ((lean_object*)(l_Std_ExtHashMap_unitOfArray___redArg___closed__1));
v___x_2242_ = lean_obj_once(&l_Std_ExtHashMap_unitOfList___redArg___closed__1, &l_Std_ExtHashMap_unitOfList___redArg___closed__1_once, _init_l_Std_ExtHashMap_unitOfList___redArg___closed__1);
v___x_2243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2241_, v_inst_2238_, v_inst_2239_, v___x_2242_, v_l_2240_);
return v___x_2243_;
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
