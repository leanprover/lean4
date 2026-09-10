// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Assignment
// Imports: public import Std.Data.HashMap public import Init.Data.Hashable public import Std.Sat.CNF.Unit import Std.Sat.CNF.SpecLemmas import Std.Tactic.Do public import Std.Sat.CNF.Entails public import Std.Sat.CNF.Negation public import Std.Sat.CNF.Redundancy
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Sat_CNF_Clause_unit___redArg(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool___boxed(lean_object*);
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___boxed(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0 = (const lean_object*)&l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(lean_object* v_unassigned_23_){
_start:
{
lean_inc(v_unassigned_23_);
return v_unassigned_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg___boxed(lean_object* v_unassigned_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(v_unassigned_24_);
lean_dec(v_unassigned_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_unassigned_29_){
_start:
{
lean_inc(v_unassigned_29_);
return v_unassigned_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_unassigned_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_unassigned_33_);
lean_dec(v_unassigned_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(lean_object* v_true_36_){
_start:
{
lean_inc(v_true_36_);
return v_true_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg___boxed(lean_object* v_true_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(v_true_37_);
lean_dec(v_true_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_true_42_){
_start:
{
lean_inc(v_true_42_);
return v_true_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_true_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_true_46_);
lean_dec(v_true_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(lean_object* v_false_49_){
_start:
{
lean_inc(v_false_49_);
return v_false_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg___boxed(lean_object* v_false_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(v_false_50_);
lean_dec(v_false_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_false_55_){
_start:
{
lean_inc(v_false_55_);
return v_false_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_false_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_false_59_);
lean_dec(v_false_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(uint8_t v_x_62_){
_start:
{
if (v_x_62_ == 0)
{
uint8_t v___x_63_; 
v___x_63_ = 2;
return v___x_63_;
}
else
{
uint8_t v___x_64_; 
v___x_64_ = 1;
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool___boxed(lean_object* v_x_65_){
_start:
{
uint8_t v_x_18__boxed_66_; uint8_t v_res_67_; lean_object* v_r_68_; 
v_x_18__boxed_66_ = lean_unbox(v_x_65_);
v_res_67_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(v_x_18__boxed_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(uint8_t v_x_75_){
_start:
{
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
case 1:
{
lean_object* v___x_77_; 
v___x_77_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0));
return v___x_77_;
}
default: 
{
lean_object* v___x_78_; 
v___x_78_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1));
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___boxed(lean_object* v_x_79_){
_start:
{
uint8_t v_x_37__boxed_80_; lean_object* v_res_81_; 
v_x_37__boxed_80_ = lean_unbox(v_x_79_);
v_res_81_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(v_x_37__boxed_80_);
return v_res_81_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_unsigned_to_nat(16u);
v___x_84_ = lean_mk_array(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1);
return v___x_88_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1(void){
_start:
{
lean_object* v___x_90_; lean_object* v___f_91_; 
v___x_90_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_91_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_91_, 0, v___x_90_);
return v___f_91_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(lean_object* v_a_92_, lean_object* v_atom_93_){
_start:
{
lean_object* v___f_94_; lean_object* v___f_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___f_94_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_95_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_96_ = 0;
v___x_97_ = lean_box(v___x_96_);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_95_, v___f_94_, v_a_92_, v_atom_93_, v___x_97_);
lean_dec(v___x_97_);
v___x_99_ = lean_unbox(v___x_98_);
lean_dec(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___boxed(lean_object* v_a_100_, lean_object* v_atom_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(v_a_100_, v_atom_101_);
lean_dec_ref(v_a_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(lean_object* v_a_104_, lean_object* v_atom_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___f_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___f_106_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_107_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_108_ = 0;
v___x_109_ = lean_box(v___x_108_);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_107_, v___f_106_, v_a_104_, v_atom_105_, v___x_109_);
lean_dec(v___x_109_);
v___x_111_ = lean_unbox(v___x_110_);
lean_dec(v___x_110_);
switch(v___x_111_)
{
case 0:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
case 1:
{
lean_object* v___x_113_; 
v___x_113_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0));
return v___x_113_;
}
default: 
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1));
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f___boxed(lean_object* v_a_115_, lean_object* v_atom_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(v_a_115_, v_atom_116_);
lean_dec_ref(v_a_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(lean_object* v_a_118_, lean_object* v_atom_119_, uint8_t v_b_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___f_122_; 
v___f_121_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_122_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
if (v_b_120_ == 0)
{
uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = 2;
v___x_124_ = lean_box(v___x_123_);
v___x_125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_122_, v___f_121_, v_a_118_, v_atom_119_, v___x_124_);
return v___x_125_;
}
else
{
uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = 1;
v___x_127_ = lean_box(v___x_126_);
v___x_128_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_122_, v___f_121_, v_a_118_, v_atom_119_, v___x_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert___boxed(lean_object* v_a_129_, lean_object* v_atom_130_, lean_object* v_b_131_){
_start:
{
uint8_t v_b_boxed_132_; lean_object* v_res_133_; 
v_b_boxed_132_ = lean_unbox(v_b_131_);
v_res_133_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(v_a_129_, v_atom_130_, v_b_boxed_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(uint8_t v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_, lean_object* v_h__3_137_){
_start:
{
switch(v_x_134_)
{
case 0:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__3_137_);
lean_dec(v_h__2_136_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__1_135_, v___x_138_);
return v___x_139_;
}
case 1:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_h__3_137_);
lean_dec(v_h__1_135_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_apply_1(v_h__2_136_, v___x_140_);
return v___x_141_;
}
default: 
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_136_);
lean_dec(v_h__1_135_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_h__3_137_, v___x_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg___boxed(lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_, lean_object* v_h__3_147_){
_start:
{
uint8_t v_x_33__boxed_148_; lean_object* v_res_149_; 
v_x_33__boxed_148_ = lean_unbox(v_x_144_);
v_res_149_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(v_x_33__boxed_148_, v_h__1_145_, v_h__2_146_, v_h__3_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(lean_object* v_motive_150_, uint8_t v_x_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_, lean_object* v_h__3_154_){
_start:
{
switch(v_x_151_)
{
case 0:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__3_154_);
lean_dec(v_h__2_153_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__1_152_, v___x_155_);
return v___x_156_;
}
case 1:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__3_154_);
lean_dec(v_h__1_152_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__2_153_, v___x_157_);
return v___x_158_;
}
default: 
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_153_);
lean_dec(v_h__1_152_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_1(v_h__3_154_, v___x_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___boxed(lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_, lean_object* v_h__3_165_){
_start:
{
uint8_t v_x_48__boxed_166_; lean_object* v_res_167_; 
v_x_48__boxed_166_ = lean_unbox(v_x_162_);
v_res_167_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(v_motive_161_, v_x_48__boxed_166_, v_h__1_163_, v_h__2_164_, v_h__3_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_erase(lean_object* v_a_168_, lean_object* v_atom_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_172_; 
v___f_170_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_171_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___f_171_, v___f_170_, v_a_168_, v_atom_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_inc(v_x_173_);
return v_x_173_;
}
else
{
lean_object* v_key_175_; lean_object* v_value_176_; lean_object* v_tail_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_key_175_ = lean_ctor_get(v_x_174_, 0);
v_value_176_ = lean_ctor_get(v_x_174_, 1);
v_tail_177_ = lean_ctor_get(v_x_174_, 2);
v___x_178_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_x_173_, v_tail_177_);
lean_inc(v_value_176_);
lean_inc(v_key_175_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_key_175_);
lean_ctor_set(v___x_179_, 1, v_value_176_);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0___boxed(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_x_181_, v_x_182_);
lean_dec(v_x_182_);
lean_dec(v_x_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(lean_object* v_as_184_, size_t v_i_185_, size_t v_stop_186_, lean_object* v_b_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_eq(v_i_185_, v_stop_186_);
if (v___x_188_ == 0)
{
size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_sub(v_i_185_, v___x_189_);
v___x_191_ = lean_array_uget_borrowed(v_as_184_, v___x_190_);
v___x_192_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_b_187_, v___x_191_);
lean_dec(v_b_187_);
v_i_185_ = v___x_190_;
v_b_187_ = v___x_192_;
goto _start;
}
else
{
return v_b_187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2___boxed(lean_object* v_as_194_, lean_object* v_i_195_, lean_object* v_stop_196_, lean_object* v_b_197_){
_start:
{
size_t v_i_boxed_198_; size_t v_stop_boxed_199_; lean_object* v_res_200_; 
v_i_boxed_198_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_stop_boxed_199_ = lean_unbox_usize(v_stop_196_);
lean_dec(v_stop_196_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_as_194_, v_i_boxed_198_, v_stop_boxed_199_, v_b_197_);
lean_dec_ref(v_as_194_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
return v_x_201_;
}
else
{
lean_object* v_head_203_; lean_object* v_tail_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; uint8_t v_val_208_; uint8_t v___x_212_; 
v_head_203_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_head_203_);
v_tail_204_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_tail_204_);
lean_dec_ref_known(v_x_202_, 2);
v_fst_205_ = lean_ctor_get(v_head_203_, 0);
lean_inc(v_fst_205_);
v_snd_206_ = lean_ctor_get(v_head_203_, 1);
lean_inc(v_snd_206_);
lean_dec(v_head_203_);
v___x_212_ = lean_unbox(v_snd_206_);
lean_dec(v_snd_206_);
switch(v___x_212_)
{
case 0:
{
lean_dec(v_fst_205_);
v_x_202_ = v_tail_204_;
goto _start;
}
case 1:
{
uint8_t v___x_214_; 
v___x_214_ = 1;
v_val_208_ = v___x_214_;
goto v___jp_207_;
}
default: 
{
uint8_t v___x_215_; 
v___x_215_ = 0;
v_val_208_ = v___x_215_;
goto v___jp_207_;
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = l_Std_Sat_CNF_Clause_unit___redArg(v_fst_205_, v_val_208_);
v___x_210_ = lean_array_push(v_x_201_, v___x_209_);
v_x_201_ = v___x_210_;
v_x_202_ = v_tail_204_;
goto _start;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_box(0);
v___x_219_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0));
v___x_220_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(v___x_219_, v___x_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(lean_object* v_a_221_){
_start:
{
lean_object* v_buckets_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_buckets_222_ = lean_ctor_get(v_a_221_, 1);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0));
v___x_225_ = lean_box(0);
v___x_226_ = lean_array_get_size(v_buckets_222_);
v___x_227_ = lean_nat_dec_lt(v___x_223_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1);
return v___x_228_;
}
else
{
size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_usize_of_nat(v___x_226_);
v___x_230_ = ((size_t)0ULL);
v___x_231_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_buckets_222_, v___x_229_, v___x_230_, v___x_225_);
v___x_232_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(v___x_224_, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___boxed(lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(v_a_233_);
lean_dec_ref(v_a_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter___redArg(lean_object* v_x_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_h__1_236_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_apply_1(v_h__2_237_, v___x_238_);
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_237_);
v_val_240_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v_x_235_, 1);
v___x_241_ = lean_apply_1(v_h__1_236_, v_val_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter(lean_object* v_motive_242_, lean_object* v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__1_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__2_245_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v_val_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_245_);
v_val_248_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v_x_243_, 1);
v___x_249_ = lean_apply_1(v_h__1_244_, v_val_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(lean_object* v_a_250_, lean_object* v_fallback_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_inc(v_fallback_251_);
return v_fallback_251_;
}
else
{
lean_object* v_key_253_; lean_object* v_value_254_; lean_object* v_tail_255_; uint8_t v___x_256_; 
v_key_253_ = lean_ctor_get(v_x_252_, 0);
v_value_254_ = lean_ctor_get(v_x_252_, 1);
v_tail_255_ = lean_ctor_get(v_x_252_, 2);
v___x_256_ = lean_nat_dec_eq(v_key_253_, v_a_250_);
if (v___x_256_ == 0)
{
v_x_252_ = v_tail_255_;
goto _start;
}
else
{
lean_inc(v_value_254_);
return v_value_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg___boxed(lean_object* v_a_258_, lean_object* v_fallback_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_258_, v_fallback_259_, v_x_260_);
lean_dec(v_x_260_);
lean_dec(v_fallback_259_);
lean_dec(v_a_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(lean_object* v_m_262_, lean_object* v_a_263_, lean_object* v_fallback_264_){
_start:
{
lean_object* v_buckets_265_; lean_object* v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v_fold_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_buckets_265_ = lean_ctor_get(v_m_262_, 1);
v___x_266_ = lean_array_get_size(v_buckets_265_);
v___x_267_ = lean_uint64_of_nat(v_a_263_);
v___x_268_ = 32ULL;
v___x_269_ = lean_uint64_shift_right(v___x_267_, v___x_268_);
v_fold_270_ = lean_uint64_xor(v___x_267_, v___x_269_);
v___x_271_ = 16ULL;
v___x_272_ = lean_uint64_shift_right(v_fold_270_, v___x_271_);
v___x_273_ = lean_uint64_xor(v_fold_270_, v___x_272_);
v___x_274_ = lean_uint64_to_usize(v___x_273_);
v___x_275_ = lean_usize_of_nat(v___x_266_);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_sub(v___x_275_, v___x_276_);
v___x_278_ = lean_usize_land(v___x_274_, v___x_277_);
v___x_279_ = lean_array_uget_borrowed(v_buckets_265_, v___x_278_);
v___x_280_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_263_, v_fallback_264_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg___boxed(lean_object* v_m_281_, lean_object* v_a_282_, lean_object* v_fallback_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_281_, v_a_282_, v_fallback_283_);
lean_dec(v_fallback_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_m_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_dec(v_b_286_);
lean_dec(v_a_285_);
return v_x_287_;
}
else
{
lean_object* v_key_288_; lean_object* v_value_289_; lean_object* v_tail_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_302_; 
v_key_288_ = lean_ctor_get(v_x_287_, 0);
v_value_289_ = lean_ctor_get(v_x_287_, 1);
v_tail_290_ = lean_ctor_get(v_x_287_, 2);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_287_);
if (v_isSharedCheck_302_ == 0)
{
v___x_292_ = v_x_287_;
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_tail_290_);
lean_inc(v_value_289_);
lean_inc(v_key_288_);
lean_dec(v_x_287_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_eq(v_key_288_, v_a_285_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_285_, v_b_286_, v_tail_290_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 2, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_key_288_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_value_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v_value_289_);
lean_dec(v_key_288_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_b_286_);
lean_ctor_set(v___x_292_, 0, v_a_285_);
v___x_300_ = v___x_292_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_285_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_b_286_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v_tail_290_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
else
{
lean_object* v_key_306_; lean_object* v_tail_307_; uint8_t v___x_308_; 
v_key_306_ = lean_ctor_get(v_x_304_, 0);
v_tail_307_ = lean_ctor_get(v_x_304_, 2);
v___x_308_ = lean_nat_dec_eq(v_key_306_, v_a_303_);
if (v___x_308_ == 0)
{
v_x_304_ = v_tail_307_;
goto _start;
}
else
{
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg___boxed(lean_object* v_a_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_310_, v_x_311_);
lean_dec(v_x_311_);
lean_dec(v_a_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
return v_x_314_;
}
else
{
lean_object* v_key_316_; lean_object* v_value_317_; lean_object* v_tail_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_341_; 
v_key_316_ = lean_ctor_get(v_x_315_, 0);
v_value_317_ = lean_ctor_get(v_x_315_, 1);
v_tail_318_ = lean_ctor_get(v_x_315_, 2);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_341_ == 0)
{
v___x_320_ = v_x_315_;
v_isShared_321_ = v_isSharedCheck_341_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_tail_318_);
lean_inc(v_value_317_);
lean_inc(v_key_316_);
lean_dec(v_x_315_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_341_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v_fold_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_322_ = lean_array_get_size(v_x_314_);
v___x_323_ = lean_uint64_of_nat(v_key_316_);
v___x_324_ = 32ULL;
v___x_325_ = lean_uint64_shift_right(v___x_323_, v___x_324_);
v_fold_326_ = lean_uint64_xor(v___x_323_, v___x_325_);
v___x_327_ = 16ULL;
v___x_328_ = lean_uint64_shift_right(v_fold_326_, v___x_327_);
v___x_329_ = lean_uint64_xor(v_fold_326_, v___x_328_);
v___x_330_ = lean_uint64_to_usize(v___x_329_);
v___x_331_ = lean_usize_of_nat(v___x_322_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_sub(v___x_331_, v___x_332_);
v___x_334_ = lean_usize_land(v___x_330_, v___x_333_);
v___x_335_ = lean_array_uget_borrowed(v_x_314_, v___x_334_);
lean_inc(v___x_335_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 2, v___x_335_);
v___x_337_ = v___x_320_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_key_316_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_value_317_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v___x_335_);
v___x_337_ = v_reuseFailAlloc_340_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; 
v___x_338_ = lean_array_uset(v_x_314_, v___x_334_, v___x_337_);
v_x_314_ = v___x_338_;
v_x_315_ = v_tail_318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(lean_object* v_i_342_, lean_object* v_source_343_, lean_object* v_target_344_){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_array_get_size(v_source_343_);
v___x_346_ = lean_nat_dec_lt(v_i_342_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v_source_343_);
lean_dec(v_i_342_);
return v_target_344_;
}
else
{
lean_object* v_es_347_; lean_object* v___x_348_; lean_object* v_source_349_; lean_object* v_target_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_es_347_ = lean_array_fget(v_source_343_, v_i_342_);
v___x_348_ = lean_box(0);
v_source_349_ = lean_array_fset(v_source_343_, v_i_342_, v___x_348_);
v_target_350_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_target_344_, v_es_347_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_i_342_, v___x_351_);
lean_dec(v_i_342_);
v_i_342_ = v___x_352_;
v_source_343_ = v_source_349_;
v_target_344_ = v_target_350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(lean_object* v_data_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_nbuckets_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_355_ = lean_array_get_size(v_data_354_);
v___x_356_ = lean_unsigned_to_nat(2u);
v_nbuckets_357_ = lean_nat_mul(v___x_355_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_box(0);
v___x_360_ = lean_mk_array(v_nbuckets_357_, v___x_359_);
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v___x_358_, v_data_354_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(lean_object* v_m_362_, lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
lean_object* v_size_365_; lean_object* v_buckets_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_409_; 
v_size_365_ = lean_ctor_get(v_m_362_, 0);
v_buckets_366_ = lean_ctor_get(v_m_362_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_m_362_);
if (v_isSharedCheck_409_ == 0)
{
v___x_368_ = v_m_362_;
v_isShared_369_ = v_isSharedCheck_409_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_buckets_366_);
lean_inc(v_size_365_);
lean_dec(v_m_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_409_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v_fold_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_bkt_383_; uint8_t v___x_384_; 
v___x_370_ = lean_array_get_size(v_buckets_366_);
v___x_371_ = lean_uint64_of_nat(v_a_363_);
v___x_372_ = 32ULL;
v___x_373_ = lean_uint64_shift_right(v___x_371_, v___x_372_);
v_fold_374_ = lean_uint64_xor(v___x_371_, v___x_373_);
v___x_375_ = 16ULL;
v___x_376_ = lean_uint64_shift_right(v_fold_374_, v___x_375_);
v___x_377_ = lean_uint64_xor(v_fold_374_, v___x_376_);
v___x_378_ = lean_uint64_to_usize(v___x_377_);
v___x_379_ = lean_usize_of_nat(v___x_370_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v___x_379_, v___x_380_);
v___x_382_ = lean_usize_land(v___x_378_, v___x_381_);
v_bkt_383_ = lean_array_uget_borrowed(v_buckets_366_, v___x_382_);
v___x_384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_363_, v_bkt_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v_size_x27_386_; lean_object* v___x_387_; lean_object* v_buckets_x27_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v_size_x27_386_ = lean_nat_add(v_size_365_, v___x_385_);
lean_dec(v_size_365_);
lean_inc(v_bkt_383_);
v___x_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_387_, 0, v_a_363_);
lean_ctor_set(v___x_387_, 1, v_b_364_);
lean_ctor_set(v___x_387_, 2, v_bkt_383_);
v_buckets_x27_388_ = lean_array_uset(v_buckets_366_, v___x_382_, v___x_387_);
v___x_389_ = lean_unsigned_to_nat(4u);
v___x_390_ = lean_nat_mul(v_size_x27_386_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_nat_div(v___x_390_, v___x_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_array_get_size(v_buckets_x27_388_);
v___x_394_ = lean_nat_dec_le(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v_val_395_; lean_object* v___x_397_; 
v_val_395_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_buckets_x27_388_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_val_395_);
lean_ctor_set(v___x_368_, 0, v_size_x27_386_);
v___x_397_ = v___x_368_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_val_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_object* v___x_400_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_buckets_x27_388_);
lean_ctor_set(v___x_368_, 0, v_size_x27_386_);
v___x_400_ = v___x_368_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_size_x27_386_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_buckets_x27_388_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v___x_402_; lean_object* v_buckets_x27_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
lean_inc(v_bkt_383_);
v___x_402_ = lean_box(0);
v_buckets_x27_403_ = lean_array_uset(v_buckets_366_, v___x_382_, v___x_402_);
v___x_404_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_363_, v_b_364_, v_bkt_383_);
v___x_405_ = lean_array_uset(v_buckets_x27_403_, v___x_382_, v___x_404_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_405_);
v___x_407_ = v___x_368_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_size_365_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(lean_object* v_c_412_, size_t v_sz_413_, size_t v_i_414_, lean_object* v_b_415_){
_start:
{
lean_object* v_a_417_; uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_421_ == 0)
{
return v_b_415_;
}
else
{
lean_object* v_atoms_422_; lean_object* v_polarities_423_; lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_457_; 
v_atoms_422_ = lean_ctor_get(v_c_412_, 0);
v_polarities_423_ = lean_ctor_get(v_c_412_, 1);
v_snd_424_ = lean_ctor_get(v_b_415_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_b_415_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v_b_415_, 0);
lean_dec(v_unused_458_);
v___x_426_ = v_b_415_;
v_isShared_427_ = v_isSharedCheck_457_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_dec(v_b_415_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_457_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___y_431_; uint8_t v___y_440_; uint8_t v___x_446_; uint8_t v___x_447_; uint8_t v___x_448_; uint8_t v_val_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_428_ = lean_array_uget_borrowed(v_atoms_422_, v_i_414_);
v___x_429_ = lean_box(0);
v___x_446_ = lean_byte_array_uget(v_polarities_423_, v_i_414_);
v___x_447_ = 1;
v___x_448_ = lean_uint8_dec_eq(v___x_446_, v___x_447_);
v___x_451_ = 0;
v___x_452_ = lean_box(v___x_451_);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_424_, v___x_428_, v___x_452_);
lean_dec(v___x_452_);
v___x_454_ = lean_unbox(v___x_453_);
lean_dec(v___x_453_);
switch(v___x_454_)
{
case 0:
{
lean_del_object(v___x_426_);
if (v___x_448_ == 0)
{
if (v___x_421_ == 0)
{
goto v___jp_444_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = 1;
v___y_440_ = v___x_455_;
goto v___jp_439_;
}
}
else
{
goto v___jp_444_;
}
}
case 1:
{
v_val_450_ = v___x_421_;
goto v___jp_449_;
}
default: 
{
uint8_t v___x_456_; 
v___x_456_ = 0;
v_val_450_ = v___x_456_;
goto v___jp_449_;
}
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
lean_object* v___x_433_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_433_ = v___x_426_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_snd_424_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v_a_417_ = v___x_433_;
goto v___jp_416_;
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_435_);
v___x_437_ = v___x_426_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_424_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_box(v___y_440_);
lean_inc(v___x_428_);
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_424_, v___x_428_, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_429_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v_a_417_ = v___x_443_;
goto v___jp_416_;
}
v___jp_444_:
{
uint8_t v___x_445_; 
v___x_445_ = 2;
v___y_440_ = v___x_445_;
goto v___jp_439_;
}
v___jp_449_:
{
if (v___x_448_ == 0)
{
if (v_val_450_ == 0)
{
v___y_431_ = v___x_421_;
goto v___jp_430_;
}
else
{
v___y_431_ = v___x_448_;
goto v___jp_430_;
}
}
else
{
v___y_431_ = v_val_450_;
goto v___jp_430_;
}
}
}
}
v___jp_416_:
{
size_t v___x_418_; size_t v___x_419_; 
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_add(v_i_414_, v___x_418_);
v_i_414_ = v___x_419_;
v_b_415_ = v_a_417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___boxed(lean_object* v_c_459_, lean_object* v_sz_460_, lean_object* v_i_461_, lean_object* v_b_462_){
_start:
{
size_t v_sz_boxed_463_; size_t v_i_boxed_464_; lean_object* v_res_465_; 
v_sz_boxed_463_ = lean_unbox_usize(v_sz_460_);
lean_dec(v_sz_460_);
v_i_boxed_464_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_res_465_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_c_459_, v_sz_boxed_463_, v_i_boxed_464_, v_b_462_);
lean_dec_ref(v_c_459_);
return v_res_465_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0(void){
_start:
{
lean_object* v_assign_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_assign_466_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty;
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_assign_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object* v_clause_469_){
_start:
{
lean_object* v_atoms_470_; lean_object* v___x_471_; size_t v_sz_472_; size_t v___x_473_; lean_object* v___x_474_; lean_object* v_fst_475_; 
v_atoms_470_ = lean_ctor_get(v_clause_469_, 0);
v___x_471_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0);
v_sz_472_ = lean_array_size(v_atoms_470_);
v___x_473_ = ((size_t)0ULL);
v___x_474_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_clause_469_, v_sz_472_, v___x_473_, v___x_471_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_fst_475_);
if (lean_obj_tag(v_fst_475_) == 0)
{
lean_object* v_snd_476_; lean_object* v___x_477_; 
v_snd_476_ = lean_ctor_get(v___x_474_, 1);
lean_inc(v_snd_476_);
lean_dec_ref(v___x_474_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_snd_476_);
return v___x_477_;
}
else
{
lean_object* v_val_478_; 
lean_dec_ref(v___x_474_);
v_val_478_ = lean_ctor_get(v_fst_475_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v_fst_475_, 1);
return v_val_478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___boxed(lean_object* v_clause_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_479_);
lean_dec_ref(v_clause_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(lean_object* v_00_u03b2_481_, lean_object* v_m_482_, lean_object* v_a_483_, lean_object* v_fallback_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_482_, v_a_483_, v_fallback_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___boxed(lean_object* v_00_u03b2_486_, lean_object* v_m_487_, lean_object* v_a_488_, lean_object* v_fallback_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(v_00_u03b2_486_, v_m_487_, v_a_488_, v_fallback_489_);
lean_dec(v_fallback_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_m_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1(lean_object* v_00_u03b2_491_, lean_object* v_m_492_, lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_m_492_, v_a_493_, v_b_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(lean_object* v_00_u03b2_496_, lean_object* v_a_497_, lean_object* v_fallback_498_, lean_object* v_x_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_497_, v_fallback_498_, v_x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___boxed(lean_object* v_00_u03b2_501_, lean_object* v_a_502_, lean_object* v_fallback_503_, lean_object* v_x_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(v_00_u03b2_501_, v_a_502_, v_fallback_503_, v_x_504_);
lean_dec(v_x_504_);
lean_dec(v_fallback_503_);
lean_dec(v_a_502_);
return v_res_505_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(lean_object* v_00_u03b2_506_, lean_object* v_a_507_, lean_object* v_x_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_507_, v_x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___boxed(lean_object* v_00_u03b2_510_, lean_object* v_a_511_, lean_object* v_x_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(v_00_u03b2_510_, v_a_511_, v_x_512_);
lean_dec(v_x_512_);
lean_dec(v_a_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3(lean_object* v_00_u03b2_515_, lean_object* v_data_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_data_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4(lean_object* v_00_u03b2_518_, lean_object* v_a_519_, lean_object* v_b_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_519_, v_b_520_, v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_523_, lean_object* v_i_524_, lean_object* v_source_525_, lean_object* v_target_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v_i_524_, v_source_525_, v_target_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_x_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter___redArg(lean_object* v_x_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
if (lean_obj_tag(v_x_532_) == 1)
{
lean_object* v_val_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_534_);
v_val_535_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v_x_532_, 1);
v___x_536_ = lean_apply_1(v_h__1_533_, v_val_535_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
lean_dec(v_h__1_533_);
v___x_537_ = lean_apply_2(v_h__2_534_, v_x_532_, lean_box(0));
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter(lean_object* v_motive_538_, lean_object* v_x_539_, lean_object* v_h__1_540_, lean_object* v_h__2_541_){
_start:
{
if (lean_obj_tag(v_x_539_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_543_; 
lean_dec(v_h__2_541_);
v_val_542_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_x_539_, 1);
v___x_543_ = lean_apply_1(v_h__1_540_, v_val_542_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; 
lean_dec(v_h__1_540_);
v___x_544_ = lean_apply_2(v_h__2_541_, v_x_539_, lean_box(0));
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_h__1_546_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_apply_1(v_h__2_547_, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v_val_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_547_);
v_val_550_ = lean_ctor_get(v_x_545_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_x_545_, 1);
v___x_551_ = lean_apply_1(v_h__1_546_, v_val_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_552_, lean_object* v_motive_553_, lean_object* v_x_554_, lean_object* v_h__1_555_, lean_object* v_h__2_556_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_h__1_555_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v_h__2_556_, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_560_; 
lean_dec(v_h__2_556_);
v_val_559_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_x_554_, 1);
v___x_560_ = lean_apply_1(v_h__1_555_, v_val_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter___redArg(lean_object* v_x_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_h__2_563_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_apply_1(v_h__1_562_, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_567_; 
lean_dec(v_h__1_562_);
v_val_566_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v_x_561_, 1);
v___x_567_ = lean_apply_1(v_h__2_563_, v_val_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter(lean_object* v_motive_568_, lean_object* v_x_569_, lean_object* v_h__1_570_, lean_object* v_h__2_571_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_h__2_571_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_apply_1(v_h__1_570_, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_575_; 
lean_dec(v_h__1_570_);
v_val_574_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_x_569_, 1);
v___x_575_ = lean_apply_1(v_h__2_571_, v_val_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(lean_object* v_lit_576_, lean_object* v_c_577_, size_t v_sz_578_, size_t v_i_579_, lean_object* v_b_580_){
_start:
{
lean_object* v_a_582_; uint8_t v___x_586_; 
v___x_586_ = lean_usize_dec_lt(v_i_579_, v_sz_578_);
if (v___x_586_ == 0)
{
return v_b_580_;
}
else
{
lean_object* v_atoms_587_; lean_object* v_polarities_588_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_632_; 
v_atoms_587_ = lean_ctor_get(v_c_577_, 0);
v_polarities_588_ = lean_ctor_get(v_c_577_, 1);
v_fst_589_ = lean_ctor_get(v_lit_576_, 0);
v_snd_590_ = lean_ctor_get(v_lit_576_, 1);
v_snd_591_ = lean_ctor_get(v_b_580_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_b_580_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_b_580_, 0);
lean_dec(v_unused_633_);
v___x_593_ = v_b_580_;
v_isShared_594_ = v_isSharedCheck_632_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_dec(v_b_580_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_632_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___y_598_; uint8_t v___y_607_; uint8_t v___y_612_; uint8_t v___x_615_; uint8_t v___x_616_; uint8_t v___x_617_; uint8_t v_val_619_; uint8_t v___y_621_; uint8_t v___y_627_; uint8_t v___x_629_; 
v___x_595_ = lean_array_uget_borrowed(v_atoms_587_, v_i_579_);
v___x_596_ = lean_box(0);
v___x_615_ = lean_byte_array_uget(v_polarities_588_, v_i_579_);
v___x_616_ = 1;
v___x_617_ = lean_uint8_dec_eq(v___x_615_, v___x_616_);
v___x_629_ = lean_nat_dec_eq(v___x_595_, v_fst_589_);
if (v___x_629_ == 0)
{
v___y_621_ = v___x_629_;
goto v___jp_620_;
}
else
{
uint8_t v___x_630_; 
v___x_630_ = lean_unbox(v_snd_590_);
if (v___x_630_ == 0)
{
if (v___x_617_ == 0)
{
v___y_627_ = v___x_629_;
goto v___jp_626_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = lean_unbox(v_snd_590_);
v___y_621_ = v___x_631_;
goto v___jp_620_;
}
}
else
{
v___y_627_ = v___x_617_;
goto v___jp_626_;
}
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v___x_600_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_600_ = v___x_593_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_snd_591_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_a_582_ = v___x_600_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_602_);
v___x_604_ = v___x_593_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_snd_591_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
v___jp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_box(v___y_607_);
lean_inc(v___x_595_);
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_591_, v___x_595_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_596_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v_a_582_ = v___x_610_;
goto v___jp_581_;
}
v___jp_611_:
{
if (v___y_612_ == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 2;
v___y_607_ = v___x_613_;
goto v___jp_606_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = 1;
v___y_607_ = v___x_614_;
goto v___jp_606_;
}
}
v___jp_618_:
{
if (v___x_617_ == 0)
{
if (v_val_619_ == 0)
{
v___y_598_ = v___x_586_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_617_;
goto v___jp_597_;
}
}
else
{
v___y_598_ = v_val_619_;
goto v___jp_597_;
}
}
v___jp_620_:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_622_ = 0;
v___x_623_ = lean_box(v___x_622_);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_591_, v___x_595_, v___x_623_);
lean_dec(v___x_623_);
v___x_625_ = lean_unbox(v___x_624_);
lean_dec(v___x_624_);
switch(v___x_625_)
{
case 0:
{
lean_del_object(v___x_593_);
if (v___x_617_ == 0)
{
v___y_612_ = v___x_586_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___y_621_;
goto v___jp_611_;
}
}
case 1:
{
v_val_619_ = v___x_586_;
goto v___jp_618_;
}
default: 
{
v_val_619_ = v___y_621_;
goto v___jp_618_;
}
}
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
v___y_621_ = v___y_627_;
goto v___jp_620_;
}
else
{
lean_object* v___x_628_; 
lean_del_object(v___x_593_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_596_);
lean_ctor_set(v___x_628_, 1, v_snd_591_);
v_a_582_ = v___x_628_;
goto v___jp_581_;
}
}
}
}
v___jp_581_:
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_579_, v___x_583_);
v_i_579_ = v___x_584_;
v_b_580_ = v_a_582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0___boxed(lean_object* v_lit_634_, lean_object* v_c_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_b_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_640_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_641_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_634_, v_c_635_, v_sz_boxed_639_, v_i_boxed_640_, v_b_638_);
lean_dec_ref(v_c_635_);
lean_dec_ref(v_lit_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object* v_assign_642_, lean_object* v_c_643_, lean_object* v_lit_644_){
_start:
{
lean_object* v_atoms_645_; lean_object* v___x_646_; lean_object* v___x_647_; size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; lean_object* v_fst_651_; 
v_atoms_645_ = lean_ctor_get(v_c_643_, 0);
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_assign_642_);
v_sz_648_ = lean_array_size(v_atoms_645_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_644_, v_c_643_, v_sz_648_, v___x_649_, v___x_647_);
v_fst_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_fst_651_);
if (lean_obj_tag(v_fst_651_) == 0)
{
lean_object* v_snd_652_; lean_object* v___x_653_; 
v_snd_652_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_snd_652_);
lean_dec_ref(v___x_650_);
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_snd_652_);
return v___x_653_;
}
else
{
lean_object* v_val_654_; 
lean_dec_ref(v___x_650_);
v_val_654_ = lean_ctor_get(v_fst_651_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_fst_651_, 1);
return v_val_654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout___boxed(lean_object* v_assign_655_, lean_object* v_c_656_, lean_object* v_lit_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_655_, v_c_656_, v_lit_657_);
lean_dec_ref(v_lit_657_);
lean_dec_ref(v_c_656_);
return v_res_658_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Unit(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_SpecLemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Negation(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Redundancy(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Unit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Negation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Redundancy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty = _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Unit(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_SpecLemmas(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Negation(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Redundancy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Unit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Negation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Redundancy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
}
#ifdef __cplusplus
}
#endif
