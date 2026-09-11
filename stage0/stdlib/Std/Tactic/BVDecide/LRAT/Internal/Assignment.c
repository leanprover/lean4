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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_nbuckets_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_355_ = lean_array_get_size(v_data_354_);
v___x_356_ = lean_unsigned_to_nat(2u);
v_nbuckets_357_ = lean_nat_mul(v___x_355_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_box(0);
v___x_360_ = lean_mk_array(v_nbuckets_357_, v___x_359_);
v___x_361_ = lean_array_propagate_mark(v_data_354_, v___x_360_);
v___x_362_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v___x_358_, v_data_354_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(lean_object* v_m_363_, lean_object* v_a_364_, lean_object* v_b_365_){
_start:
{
lean_object* v_size_366_; lean_object* v_buckets_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_410_; 
v_size_366_ = lean_ctor_get(v_m_363_, 0);
v_buckets_367_ = lean_ctor_get(v_m_363_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_m_363_);
if (v_isSharedCheck_410_ == 0)
{
v___x_369_ = v_m_363_;
v_isShared_370_ = v_isSharedCheck_410_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_buckets_367_);
lean_inc(v_size_366_);
lean_dec(v_m_363_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_410_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v_fold_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v_bkt_384_; uint8_t v___x_385_; 
v___x_371_ = lean_array_get_size(v_buckets_367_);
v___x_372_ = lean_uint64_of_nat(v_a_364_);
v___x_373_ = 32ULL;
v___x_374_ = lean_uint64_shift_right(v___x_372_, v___x_373_);
v_fold_375_ = lean_uint64_xor(v___x_372_, v___x_374_);
v___x_376_ = 16ULL;
v___x_377_ = lean_uint64_shift_right(v_fold_375_, v___x_376_);
v___x_378_ = lean_uint64_xor(v_fold_375_, v___x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = lean_usize_of_nat(v___x_371_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_sub(v___x_380_, v___x_381_);
v___x_383_ = lean_usize_land(v___x_379_, v___x_382_);
v_bkt_384_ = lean_array_uget_borrowed(v_buckets_367_, v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_364_, v_bkt_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v_size_x27_387_; lean_object* v___x_388_; lean_object* v_buckets_x27_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v_size_x27_387_ = lean_nat_add(v_size_366_, v___x_386_);
lean_dec(v_size_366_);
lean_inc(v_bkt_384_);
v___x_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_388_, 0, v_a_364_);
lean_ctor_set(v___x_388_, 1, v_b_365_);
lean_ctor_set(v___x_388_, 2, v_bkt_384_);
v_buckets_x27_389_ = lean_array_uset(v_buckets_367_, v___x_383_, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(4u);
v___x_391_ = lean_nat_mul(v_size_x27_387_, v___x_390_);
v___x_392_ = lean_unsigned_to_nat(3u);
v___x_393_ = lean_nat_div(v___x_391_, v___x_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_array_get_size(v_buckets_x27_389_);
v___x_395_ = lean_nat_dec_le(v___x_393_, v___x_394_);
lean_dec(v___x_393_);
if (v___x_395_ == 0)
{
lean_object* v_val_396_; lean_object* v___x_398_; 
v_val_396_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_buckets_x27_389_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_val_396_);
lean_ctor_set(v___x_369_, 0, v_size_x27_387_);
v___x_398_ = v___x_369_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_size_x27_387_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_val_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v___x_401_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_buckets_x27_389_);
lean_ctor_set(v___x_369_, 0, v_size_x27_387_);
v___x_401_ = v___x_369_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_size_x27_387_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_buckets_x27_389_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v___x_403_; lean_object* v_buckets_x27_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
lean_inc(v_bkt_384_);
v___x_403_ = lean_box(0);
v_buckets_x27_404_ = lean_array_uset(v_buckets_367_, v___x_383_, v___x_403_);
v___x_405_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_364_, v_b_365_, v_bkt_384_);
v___x_406_ = lean_array_uset(v_buckets_x27_404_, v___x_383_, v___x_405_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_406_);
v___x_408_ = v___x_369_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_size_366_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(lean_object* v_c_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_b_416_){
_start:
{
lean_object* v_a_418_; uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_422_ == 0)
{
return v_b_416_;
}
else
{
lean_object* v_atoms_423_; lean_object* v_polarities_424_; lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_458_; 
v_atoms_423_ = lean_ctor_get(v_c_413_, 0);
v_polarities_424_ = lean_ctor_get(v_c_413_, 1);
v_snd_425_ = lean_ctor_get(v_b_416_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_b_416_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v_b_416_, 0);
lean_dec(v_unused_459_);
v___x_427_ = v_b_416_;
v_isShared_428_ = v_isSharedCheck_458_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_dec(v_b_416_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_458_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___y_432_; uint8_t v___y_441_; uint8_t v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; uint8_t v_val_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_429_ = lean_array_uget_borrowed(v_atoms_423_, v_i_415_);
v___x_430_ = lean_box(0);
v___x_447_ = lean_byte_array_uget(v_polarities_424_, v_i_415_);
v___x_448_ = 1;
v___x_449_ = lean_uint8_dec_eq(v___x_447_, v___x_448_);
v___x_452_ = 0;
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_425_, v___x_429_, v___x_453_);
lean_dec(v___x_453_);
v___x_455_ = lean_unbox(v___x_454_);
lean_dec(v___x_454_);
switch(v___x_455_)
{
case 0:
{
lean_del_object(v___x_427_);
if (v___x_449_ == 0)
{
if (v___x_422_ == 0)
{
goto v___jp_445_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 1;
v___y_441_ = v___x_456_;
goto v___jp_440_;
}
}
else
{
goto v___jp_445_;
}
}
case 1:
{
v_val_451_ = v___x_422_;
goto v___jp_450_;
}
default: 
{
uint8_t v___x_457_; 
v___x_457_ = 0;
v_val_451_ = v___x_457_;
goto v___jp_450_;
}
}
v___jp_431_:
{
if (v___y_432_ == 0)
{
lean_object* v___x_434_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_430_);
v___x_434_ = v___x_427_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_snd_425_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_a_418_ = v___x_434_;
goto v___jp_417_;
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_436_);
v___x_438_ = v___x_427_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_snd_425_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(v___y_441_);
lean_inc(v___x_429_);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_425_, v___x_429_, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_430_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v_a_418_ = v___x_444_;
goto v___jp_417_;
}
v___jp_445_:
{
uint8_t v___x_446_; 
v___x_446_ = 2;
v___y_441_ = v___x_446_;
goto v___jp_440_;
}
v___jp_450_:
{
if (v___x_449_ == 0)
{
if (v_val_451_ == 0)
{
v___y_432_ = v___x_422_;
goto v___jp_431_;
}
else
{
v___y_432_ = v___x_449_;
goto v___jp_431_;
}
}
else
{
v___y_432_ = v_val_451_;
goto v___jp_431_;
}
}
}
}
v___jp_417_:
{
size_t v___x_419_; size_t v___x_420_; 
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_415_, v___x_419_);
v_i_415_ = v___x_420_;
v_b_416_ = v_a_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___boxed(lean_object* v_c_460_, lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_b_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_465_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_466_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_c_460_, v_sz_boxed_464_, v_i_boxed_465_, v_b_463_);
lean_dec_ref(v_c_460_);
return v_res_466_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0(void){
_start:
{
lean_object* v_assign_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_assign_467_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty;
v___x_468_ = lean_box(0);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_assign_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object* v_clause_470_){
_start:
{
lean_object* v_atoms_471_; lean_object* v___x_472_; size_t v_sz_473_; size_t v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; 
v_atoms_471_ = lean_ctor_get(v_clause_470_, 0);
v___x_472_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0);
v_sz_473_ = lean_array_size(v_atoms_471_);
v___x_474_ = ((size_t)0ULL);
v___x_475_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_clause_470_, v_sz_473_, v___x_474_, v___x_472_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
if (lean_obj_tag(v_fst_476_) == 0)
{
lean_object* v_snd_477_; lean_object* v___x_478_; 
v_snd_477_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_snd_477_);
lean_dec_ref(v___x_475_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_snd_477_);
return v___x_478_;
}
else
{
lean_object* v_val_479_; 
lean_dec_ref(v___x_475_);
v_val_479_ = lean_ctor_get(v_fst_476_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v_fst_476_, 1);
return v_val_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___boxed(lean_object* v_clause_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_480_);
lean_dec_ref(v_clause_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(lean_object* v_00_u03b2_482_, lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_fallback_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_483_, v_a_484_, v_fallback_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_m_488_, lean_object* v_a_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(v_00_u03b2_487_, v_m_488_, v_a_489_, v_fallback_490_);
lean_dec(v_fallback_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_m_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1(lean_object* v_00_u03b2_492_, lean_object* v_m_493_, lean_object* v_a_494_, lean_object* v_b_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_m_493_, v_a_494_, v_b_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(lean_object* v_00_u03b2_497_, lean_object* v_a_498_, lean_object* v_fallback_499_, lean_object* v_x_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_498_, v_fallback_499_, v_x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___boxed(lean_object* v_00_u03b2_502_, lean_object* v_a_503_, lean_object* v_fallback_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(v_00_u03b2_502_, v_a_503_, v_fallback_504_, v_x_505_);
lean_dec(v_x_505_);
lean_dec(v_fallback_504_);
lean_dec(v_a_503_);
return v_res_506_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(lean_object* v_00_u03b2_507_, lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_508_, v_x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___boxed(lean_object* v_00_u03b2_511_, lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(v_00_u03b2_511_, v_a_512_, v_x_513_);
lean_dec(v_x_513_);
lean_dec(v_a_512_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3(lean_object* v_00_u03b2_516_, lean_object* v_data_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_data_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4(lean_object* v_00_u03b2_519_, lean_object* v_a_520_, lean_object* v_b_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_520_, v_b_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_524_, lean_object* v_i_525_, lean_object* v_source_526_, lean_object* v_target_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v_i_525_, v_source_526_, v_target_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_x_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter___redArg(lean_object* v_x_533_, lean_object* v_h__1_534_, lean_object* v_h__2_535_){
_start:
{
if (lean_obj_tag(v_x_533_) == 1)
{
lean_object* v_val_536_; lean_object* v___x_537_; 
lean_dec(v_h__2_535_);
v_val_536_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_x_533_, 1);
v___x_537_ = lean_apply_1(v_h__1_534_, v_val_536_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; 
lean_dec(v_h__1_534_);
v___x_538_ = lean_apply_2(v_h__2_535_, v_x_533_, lean_box(0));
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter(lean_object* v_motive_539_, lean_object* v_x_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_){
_start:
{
if (lean_obj_tag(v_x_540_) == 1)
{
lean_object* v_val_543_; lean_object* v___x_544_; 
lean_dec(v_h__2_542_);
v_val_543_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_x_540_, 1);
v___x_544_ = lean_apply_1(v_h__1_541_, v_val_543_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; 
lean_dec(v_h__1_541_);
v___x_545_ = lean_apply_2(v_h__2_542_, v_x_540_, lean_box(0));
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_546_, lean_object* v_h__1_547_, lean_object* v_h__2_548_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_h__1_547_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_apply_1(v_h__2_548_, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v_val_551_; lean_object* v___x_552_; 
lean_dec(v_h__2_548_);
v_val_551_ = lean_ctor_get(v_x_546_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_x_546_, 1);
v___x_552_ = lean_apply_1(v_h__1_547_, v_val_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_553_, lean_object* v_motive_554_, lean_object* v_x_555_, lean_object* v_h__1_556_, lean_object* v_h__2_557_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_h__1_556_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_apply_1(v_h__2_557_, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v_val_560_; lean_object* v___x_561_; 
lean_dec(v_h__2_557_);
v_val_560_ = lean_ctor_get(v_x_555_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v_x_555_, 1);
v___x_561_ = lean_apply_1(v_h__1_556_, v_val_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter___redArg(lean_object* v_x_562_, lean_object* v_h__1_563_, lean_object* v_h__2_564_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_h__2_564_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_apply_1(v_h__1_563_, v___x_565_);
return v___x_566_;
}
else
{
lean_object* v_val_567_; lean_object* v___x_568_; 
lean_dec(v_h__1_563_);
v_val_567_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_x_562_, 1);
v___x_568_ = lean_apply_1(v_h__2_564_, v_val_567_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter(lean_object* v_motive_569_, lean_object* v_x_570_, lean_object* v_h__1_571_, lean_object* v_h__2_572_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_h__2_572_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_apply_1(v_h__1_571_, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v_val_575_; lean_object* v___x_576_; 
lean_dec(v_h__1_571_);
v_val_575_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_val_575_);
lean_dec_ref_known(v_x_570_, 1);
v___x_576_ = lean_apply_1(v_h__2_572_, v_val_575_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(lean_object* v_lit_577_, lean_object* v_c_578_, size_t v_sz_579_, size_t v_i_580_, lean_object* v_b_581_){
_start:
{
lean_object* v_a_583_; uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_lt(v_i_580_, v_sz_579_);
if (v___x_587_ == 0)
{
return v_b_581_;
}
else
{
lean_object* v_atoms_588_; lean_object* v_polarities_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v_snd_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_633_; 
v_atoms_588_ = lean_ctor_get(v_c_578_, 0);
v_polarities_589_ = lean_ctor_get(v_c_578_, 1);
v_fst_590_ = lean_ctor_get(v_lit_577_, 0);
v_snd_591_ = lean_ctor_get(v_lit_577_, 1);
v_snd_592_ = lean_ctor_get(v_b_581_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_b_581_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_b_581_, 0);
lean_dec(v_unused_634_);
v___x_594_ = v_b_581_;
v_isShared_595_ = v_isSharedCheck_633_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snd_592_);
lean_dec(v_b_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_633_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___y_599_; uint8_t v___y_608_; uint8_t v___y_613_; uint8_t v___x_616_; uint8_t v___x_617_; uint8_t v___x_618_; uint8_t v_val_620_; uint8_t v___y_622_; uint8_t v___y_628_; uint8_t v___x_630_; 
v___x_596_ = lean_array_uget_borrowed(v_atoms_588_, v_i_580_);
v___x_597_ = lean_box(0);
v___x_616_ = lean_byte_array_uget(v_polarities_589_, v_i_580_);
v___x_617_ = 1;
v___x_618_ = lean_uint8_dec_eq(v___x_616_, v___x_617_);
v___x_630_ = lean_nat_dec_eq(v___x_596_, v_fst_590_);
if (v___x_630_ == 0)
{
v___y_622_ = v___x_630_;
goto v___jp_621_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = lean_unbox(v_snd_591_);
if (v___x_631_ == 0)
{
if (v___x_618_ == 0)
{
v___y_628_ = v___x_630_;
goto v___jp_627_;
}
else
{
uint8_t v___x_632_; 
v___x_632_ = lean_unbox(v_snd_591_);
v___y_622_ = v___x_632_;
goto v___jp_621_;
}
}
else
{
v___y_628_ = v___x_618_;
goto v___jp_627_;
}
}
v___jp_598_:
{
if (v___y_599_ == 0)
{
lean_object* v___x_601_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_597_);
v___x_601_ = v___x_594_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_snd_592_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
v_a_583_ = v___x_601_;
goto v___jp_582_;
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_603_);
v___x_605_ = v___x_594_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_snd_592_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
v___jp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(v___y_608_);
lean_inc(v___x_596_);
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_592_, v___x_596_, v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_597_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v_a_583_ = v___x_611_;
goto v___jp_582_;
}
v___jp_612_:
{
if (v___y_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = 2;
v___y_608_ = v___x_614_;
goto v___jp_607_;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = 1;
v___y_608_ = v___x_615_;
goto v___jp_607_;
}
}
v___jp_619_:
{
if (v___x_618_ == 0)
{
if (v_val_620_ == 0)
{
v___y_599_ = v___x_587_;
goto v___jp_598_;
}
else
{
v___y_599_ = v___x_618_;
goto v___jp_598_;
}
}
else
{
v___y_599_ = v_val_620_;
goto v___jp_598_;
}
}
v___jp_621_:
{
uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_623_ = 0;
v___x_624_ = lean_box(v___x_623_);
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_592_, v___x_596_, v___x_624_);
lean_dec(v___x_624_);
v___x_626_ = lean_unbox(v___x_625_);
lean_dec(v___x_625_);
switch(v___x_626_)
{
case 0:
{
lean_del_object(v___x_594_);
if (v___x_618_ == 0)
{
v___y_613_ = v___x_587_;
goto v___jp_612_;
}
else
{
v___y_613_ = v___y_622_;
goto v___jp_612_;
}
}
case 1:
{
v_val_620_ = v___x_587_;
goto v___jp_619_;
}
default: 
{
v_val_620_ = v___y_622_;
goto v___jp_619_;
}
}
}
v___jp_627_:
{
if (v___y_628_ == 0)
{
v___y_622_ = v___y_628_;
goto v___jp_621_;
}
else
{
lean_object* v___x_629_; 
lean_del_object(v___x_594_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_597_);
lean_ctor_set(v___x_629_, 1, v_snd_592_);
v_a_583_ = v___x_629_;
goto v___jp_582_;
}
}
}
}
v___jp_582_:
{
size_t v___x_584_; size_t v___x_585_; 
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_580_, v___x_584_);
v_i_580_ = v___x_585_;
v_b_581_ = v_a_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0___boxed(lean_object* v_lit_635_, lean_object* v_c_636_, lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_b_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_641_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_642_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_635_, v_c_636_, v_sz_boxed_640_, v_i_boxed_641_, v_b_639_);
lean_dec_ref(v_c_636_);
lean_dec_ref(v_lit_635_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object* v_assign_643_, lean_object* v_c_644_, lean_object* v_lit_645_){
_start:
{
lean_object* v_atoms_646_; lean_object* v___x_647_; lean_object* v___x_648_; size_t v_sz_649_; size_t v___x_650_; lean_object* v___x_651_; lean_object* v_fst_652_; 
v_atoms_646_ = lean_ctor_get(v_c_644_, 0);
v___x_647_ = lean_box(0);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_assign_643_);
v_sz_649_ = lean_array_size(v_atoms_646_);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_645_, v_c_644_, v_sz_649_, v___x_650_, v___x_648_);
v_fst_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_fst_652_);
if (lean_obj_tag(v_fst_652_) == 0)
{
lean_object* v_snd_653_; lean_object* v___x_654_; 
v_snd_653_ = lean_ctor_get(v___x_651_, 1);
lean_inc(v_snd_653_);
lean_dec_ref(v___x_651_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v_snd_653_);
return v___x_654_;
}
else
{
lean_object* v_val_655_; 
lean_dec_ref(v___x_651_);
v_val_655_ = lean_ctor_get(v_fst_652_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v_fst_652_, 1);
return v_val_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout___boxed(lean_object* v_assign_656_, lean_object* v_c_657_, lean_object* v_lit_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_656_, v_c_657_, v_lit_658_);
lean_dec_ref(v_lit_658_);
lean_dec_ref(v_c_657_);
return v_res_659_;
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
