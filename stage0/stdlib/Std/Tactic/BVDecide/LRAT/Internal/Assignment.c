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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(lean_object* v_unassigned_24_){
_start:
{
lean_inc(v_unassigned_24_);
return v_unassigned_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg___boxed(lean_object* v_unassigned_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(v_unassigned_25_);
lean_dec(v_unassigned_25_);
return v_res_26_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_unassigned_30_){
_start:
{
lean_inc(v_unassigned_30_);
return v_unassigned_30_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_unassigned_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(lean_box(0), v_t_28_, lean_box(0), v_unassigned_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_unassigned_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_unassigned_35_);
lean_dec(v_unassigned_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(lean_object* v_true_38_){
_start:
{
lean_inc(v_true_38_);
return v_true_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg___boxed(lean_object* v_true_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(v_true_39_);
lean_dec(v_true_39_);
return v_res_40_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_true_44_){
_start:
{
lean_inc(v_true_44_);
return v_true_44_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_true_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(lean_box(0), v_t_42_, lean_box(0), v_true_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_true_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_true_49_);
lean_dec(v_true_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(lean_object* v_false_52_){
_start:
{
lean_inc(v_false_52_);
return v_false_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg___boxed(lean_object* v_false_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(v_false_53_);
lean_dec(v_false_53_);
return v_res_54_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_false_58_){
_start:
{
lean_inc(v_false_58_);
return v_false_58_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_false_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(lean_box(0), v_t_56_, lean_box(0), v_false_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_false_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_false_63_);
lean_dec(v_false_63_);
return v_res_65_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(uint8_t v_x_66_){
_start:
{
if (v_x_66_ == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 2;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_66_ = stack[0].m_num;
uint8_t v_res_69_;
v_res_69_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(v_x_66_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool___boxed(lean_object* v_x_70_){
_start:
{
uint8_t v_x_18__boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_18__boxed_71_ = lean_unbox(v_x_70_);
v_res_72_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(v_x_18__boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(uint8_t v_x_80_){
_start:
{
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
case 1:
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0));
return v___x_82_;
}
default: 
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1));
return v___x_83_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_80_ = stack[0].m_num;
lean_object* v_res_84_;
v_res_84_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(v_x_80_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___boxed(lean_object* v_x_85_){
_start:
{
uint8_t v_x_37__boxed_86_; lean_object* v_res_87_; 
v_x_37__boxed_86_ = lean_unbox(v_x_85_);
v_res_87_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(v_x_37__boxed_86_);
return v_res_87_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_unsigned_to_nat(16u);
v___x_90_ = lean_mk_array(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1);
return v___x_94_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; 
v___x_96_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_97_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
return v___f_97_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(lean_object* v_a_98_, lean_object* v_atom_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___f_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___f_100_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_101_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_102_ = 0;
v___x_103_ = lean_box(v___x_102_);
v___x_104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_101_, v___f_100_, v_a_98_, v_atom_99_, v___x_103_);
lean_dec(v___x_103_);
v___x_105_ = lean_unbox(v___x_104_);
lean_dec(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_98_ = stack[0].m_obj;
lean_object* v_atom_99_ = stack[1].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(v_a_98_, v_atom_99_);
stack->m_num = v_res_106_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___boxed(lean_object* v_a_107_, lean_object* v_atom_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(v_a_107_, v_atom_108_);
lean_dec_ref(v_a_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(lean_object* v_a_111_, lean_object* v_atom_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___f_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___f_113_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_114_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_115_ = 0;
v___x_116_ = lean_box(v___x_115_);
v___x_117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_114_, v___f_113_, v_a_111_, v_atom_112_, v___x_116_);
lean_dec(v___x_116_);
v___x_118_ = lean_unbox(v___x_117_);
lean_dec(v___x_117_);
switch(v___x_118_)
{
case 0:
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
return v___x_119_;
}
case 1:
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0));
return v___x_120_;
}
default: 
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1));
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f___boxed(lean_object* v_a_122_, lean_object* v_atom_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(v_a_122_, v_atom_123_);
lean_dec_ref(v_a_122_);
return v_res_124_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(lean_object* v_a_125_, lean_object* v_atom_126_, uint8_t v_b_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___f_129_; 
v___f_128_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_129_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
if (v_b_127_ == 0)
{
uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = 2;
v___x_131_ = lean_box(v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_129_, v___f_128_, v_a_125_, v_atom_126_, v___x_131_);
return v___x_132_;
}
else
{
uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = 1;
v___x_134_ = lean_box(v___x_133_);
v___x_135_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_129_, v___f_128_, v_a_125_, v_atom_126_, v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_125_ = stack[0].m_obj;
lean_object* v_atom_126_ = stack[1].m_obj;
uint8_t v_b_127_ = stack[2].m_num;
lean_object* v_res_136_;
v_res_136_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(v_a_125_, v_atom_126_, v_b_127_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert___boxed(lean_object* v_a_137_, lean_object* v_atom_138_, lean_object* v_b_139_){
_start:
{
uint8_t v_b_boxed_140_; lean_object* v_res_141_; 
v_b_boxed_140_ = lean_unbox(v_b_139_);
v_res_141_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(v_a_137_, v_atom_138_, v_b_boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_erase(lean_object* v_a_142_, lean_object* v_atom_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v___f_144_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_145_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___f_145_, v___f_144_, v_a_142_, v_atom_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_inc(v_x_147_);
return v_x_147_;
}
else
{
lean_object* v_key_149_; lean_object* v_value_150_; lean_object* v_tail_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_key_149_ = lean_ctor_get(v_x_148_, 0);
v_value_150_ = lean_ctor_get(v_x_148_, 1);
v_tail_151_ = lean_ctor_get(v_x_148_, 2);
v___x_152_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_x_147_, v_tail_151_);
lean_inc(v_value_150_);
lean_inc(v_key_149_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_key_149_);
lean_ctor_set(v___x_153_, 1, v_value_150_);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0___boxed(lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_x_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec(v_x_155_);
return v_res_157_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(lean_object* v_as_158_, size_t v_i_159_, size_t v_stop_160_, lean_object* v_b_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_eq(v_i_159_, v_stop_160_);
if (v___x_162_ == 0)
{
size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = ((size_t)1ULL);
v___x_164_ = lean_usize_sub(v_i_159_, v___x_163_);
v___x_165_ = lean_array_uget_borrowed(v_as_158_, v___x_164_);
v___x_166_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_b_161_, v___x_165_);
lean_dec(v_b_161_);
v_i_159_ = v___x_164_;
v_b_161_ = v___x_166_;
goto _start;
}
else
{
return v_b_161_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_158_ = stack[0].m_obj;
size_t v_i_159_ = stack[1].m_num;
size_t v_stop_160_ = stack[2].m_num;
lean_object* v_b_161_ = stack[3].m_obj;
lean_object* v_res_168_;
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_as_158_, v_i_159_, v_stop_160_, v_b_161_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2___boxed(lean_object* v_as_169_, lean_object* v_i_170_, lean_object* v_stop_171_, lean_object* v_b_172_){
_start:
{
size_t v_i_boxed_173_; size_t v_stop_boxed_174_; lean_object* v_res_175_; 
v_i_boxed_173_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_stop_boxed_174_ = lean_unbox_usize(v_stop_171_);
lean_dec(v_stop_171_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_as_169_, v_i_boxed_173_, v_stop_boxed_174_, v_b_172_);
lean_dec_ref(v_as_169_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
return v_x_176_;
}
else
{
lean_object* v_head_178_; lean_object* v_tail_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; uint8_t v_val_183_; uint8_t v___x_187_; 
v_head_178_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_head_178_);
v_tail_179_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_tail_179_);
lean_dec_ref_known(v_x_177_, 2);
v_fst_180_ = lean_ctor_get(v_head_178_, 0);
lean_inc(v_fst_180_);
v_snd_181_ = lean_ctor_get(v_head_178_, 1);
lean_inc(v_snd_181_);
lean_dec(v_head_178_);
v___x_187_ = lean_unbox(v_snd_181_);
lean_dec(v_snd_181_);
switch(v___x_187_)
{
case 0:
{
lean_dec(v_fst_180_);
v_x_177_ = v_tail_179_;
goto _start;
}
case 1:
{
uint8_t v___x_189_; 
v___x_189_ = 1;
v_val_183_ = v___x_189_;
goto v___jp_182_;
}
default: 
{
uint8_t v___x_190_; 
v___x_190_ = 0;
v_val_183_ = v___x_190_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = l_Std_Sat_CNF_Clause_unit___redArg(v_fst_180_, v_val_183_);
v___x_185_ = lean_array_push(v_x_176_, v___x_184_);
v_x_176_ = v___x_185_;
v_x_177_ = v_tail_179_;
goto _start;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0));
v___x_195_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(v___x_194_, v___x_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(lean_object* v_a_196_){
_start:
{
lean_object* v_buckets_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_buckets_197_ = lean_ctor_get(v_a_196_, 1);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0));
v___x_200_ = lean_box(0);
v___x_201_ = lean_array_get_size(v_buckets_197_);
v___x_202_ = lean_nat_dec_lt(v___x_198_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1);
return v___x_203_;
}
else
{
size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_usize_of_nat(v___x_201_);
v___x_205_ = ((size_t)0ULL);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_buckets_197_, v___x_204_, v___x_205_, v___x_200_);
v___x_207_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(v___x_199_, v___x_206_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(v_a_208_);
lean_dec_ref(v_a_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter___redArg(lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_211_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__2_212_, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
lean_dec(v_h__2_212_);
v_val_215_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v_x_210_, 1);
v___x_216_ = lean_apply_1(v_h__1_211_, v_val_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter(lean_object* v_motive_217_, lean_object* v_x_218_, lean_object* v_h__1_219_, lean_object* v_h__2_220_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_h__1_219_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v_h__2_220_, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; 
lean_dec(v_h__2_220_);
v_val_223_ = lean_ctor_get(v_x_218_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v_x_218_, 1);
v___x_224_ = lean_apply_1(v_h__1_219_, v_val_223_);
return v___x_224_;
}
}
}
lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(uint8_t v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_){
_start:
{
switch(v_x_225_)
{
case 0:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_h__3_228_);
lean_dec(v_h__2_227_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_apply_1(v_h__1_226_, v___x_229_);
return v___x_230_;
}
case 1:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__3_228_);
lean_dec(v_h__1_226_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_h__2_227_, v___x_231_);
return v___x_232_;
}
default: 
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_h__2_227_);
lean_dec(v_h__1_226_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_apply_1(v_h__3_228_, v___x_233_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_225_ = stack[0].m_num;
lean_object* v_h__1_226_ = stack[1].m_obj;
lean_object* v_h__2_227_ = stack[2].m_obj;
lean_object* v_h__3_228_ = stack[3].m_obj;
lean_object* v_res_235_;
v_res_235_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(v_x_225_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg___boxed(lean_object* v_x_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_, lean_object* v_h__3_239_){
_start:
{
uint8_t v_x_33__boxed_240_; lean_object* v_res_241_; 
v_x_33__boxed_240_ = lean_unbox(v_x_236_);
v_res_241_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(v_x_33__boxed_240_, v_h__1_237_, v_h__2_238_, v_h__3_239_);
return v_res_241_;
}
}
lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(lean_object* v_motive_242_, uint8_t v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_, lean_object* v_h__3_246_){
_start:
{
switch(v_x_243_)
{
case 0:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_h__3_246_);
lean_dec(v_h__2_245_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_h__1_244_, v___x_247_);
return v___x_248_;
}
case 1:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_h__3_246_);
lean_dec(v_h__1_244_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_apply_1(v_h__2_245_, v___x_249_);
return v___x_250_;
}
default: 
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_h__2_245_);
lean_dec(v_h__1_244_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_apply_1(v_h__3_246_, v___x_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_243_ = stack[1].m_num;
lean_object* v_h__1_244_ = stack[2].m_obj;
lean_object* v_h__2_245_ = stack[3].m_obj;
lean_object* v_h__3_246_ = stack[4].m_obj;
lean_object* v_res_253_;
v_res_253_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(lean_box(0), v_x_243_, v_h__1_244_, v_h__2_245_, v_h__3_246_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___boxed(lean_object* v_motive_254_, lean_object* v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_, lean_object* v_h__3_258_){
_start:
{
uint8_t v_x_56__boxed_259_; lean_object* v_res_260_; 
v_x_56__boxed_259_ = lean_unbox(v_x_255_);
v_res_260_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(v_motive_254_, v_x_56__boxed_259_, v_h__1_256_, v_h__2_257_, v_h__3_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(lean_object* v_a_261_, lean_object* v_fallback_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_inc(v_fallback_262_);
return v_fallback_262_;
}
else
{
lean_object* v_key_264_; lean_object* v_value_265_; lean_object* v_tail_266_; uint8_t v___x_267_; 
v_key_264_ = lean_ctor_get(v_x_263_, 0);
v_value_265_ = lean_ctor_get(v_x_263_, 1);
v_tail_266_ = lean_ctor_get(v_x_263_, 2);
v___x_267_ = lean_nat_dec_eq(v_key_264_, v_a_261_);
if (v___x_267_ == 0)
{
v_x_263_ = v_tail_266_;
goto _start;
}
else
{
lean_inc(v_value_265_);
return v_value_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg___boxed(lean_object* v_a_269_, lean_object* v_fallback_270_, lean_object* v_x_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_269_, v_fallback_270_, v_x_271_);
lean_dec(v_x_271_);
lean_dec(v_fallback_270_);
lean_dec(v_a_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(lean_object* v_m_273_, lean_object* v_a_274_, lean_object* v_fallback_275_){
_start:
{
lean_object* v_buckets_276_; lean_object* v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v_fold_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_buckets_276_ = lean_ctor_get(v_m_273_, 1);
v___x_277_ = lean_array_get_size(v_buckets_276_);
v___x_278_ = lean_uint64_of_nat(v_a_274_);
v___x_279_ = 32ULL;
v___x_280_ = lean_uint64_shift_right(v___x_278_, v___x_279_);
v_fold_281_ = lean_uint64_xor(v___x_278_, v___x_280_);
v___x_282_ = 16ULL;
v___x_283_ = lean_uint64_shift_right(v_fold_281_, v___x_282_);
v___x_284_ = lean_uint64_xor(v_fold_281_, v___x_283_);
v___x_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = lean_usize_of_nat(v___x_277_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_sub(v___x_286_, v___x_287_);
v___x_289_ = lean_usize_land(v___x_285_, v___x_288_);
v___x_290_ = lean_array_uget_borrowed(v_buckets_276_, v___x_289_);
v___x_291_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_274_, v_fallback_275_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg___boxed(lean_object* v_m_292_, lean_object* v_a_293_, lean_object* v_fallback_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_292_, v_a_293_, v_fallback_294_);
lean_dec(v_fallback_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_m_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_dec(v_b_297_);
lean_dec(v_a_296_);
return v_x_298_;
}
else
{
lean_object* v_key_299_; lean_object* v_value_300_; lean_object* v_tail_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_313_; 
v_key_299_ = lean_ctor_get(v_x_298_, 0);
v_value_300_ = lean_ctor_get(v_x_298_, 1);
v_tail_301_ = lean_ctor_get(v_x_298_, 2);
v_isSharedCheck_313_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_313_ == 0)
{
v___x_303_ = v_x_298_;
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_tail_301_);
lean_inc(v_value_300_);
lean_inc(v_key_299_);
lean_dec(v_x_298_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
uint8_t v___x_305_; 
v___x_305_ = lean_nat_dec_eq(v_key_299_, v_a_296_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_296_, v_b_297_, v_tail_301_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 2, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_key_299_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_value_300_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
else
{
lean_object* v___x_311_; 
lean_dec(v_value_300_);
lean_dec(v_key_299_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_b_297_);
lean_ctor_set(v___x_303_, 0, v_a_296_);
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_296_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_b_297_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_tail_301_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(lean_object* v_a_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
else
{
lean_object* v_key_317_; lean_object* v_tail_318_; uint8_t v___x_319_; 
v_key_317_ = lean_ctor_get(v_x_315_, 0);
v_tail_318_ = lean_ctor_get(v_x_315_, 2);
v___x_319_ = lean_nat_dec_eq(v_key_317_, v_a_314_);
if (v___x_319_ == 0)
{
v_x_315_ = v_tail_318_;
goto _start;
}
else
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_314_ = stack[0].m_obj;
lean_object* v_x_315_ = stack[1].m_obj;
uint8_t v_res_321_;
v_res_321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_314_, v_x_315_);
stack->m_num = v_res_321_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg___boxed(lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec(v_a_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
return v_x_326_;
}
else
{
lean_object* v_key_328_; lean_object* v_value_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_353_; 
v_key_328_ = lean_ctor_get(v_x_327_, 0);
v_value_329_ = lean_ctor_get(v_x_327_, 1);
v_tail_330_ = lean_ctor_get(v_x_327_, 2);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_353_ == 0)
{
v___x_332_ = v_x_327_;
v_isShared_333_ = v_isSharedCheck_353_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_value_329_);
lean_inc(v_key_328_);
lean_dec(v_x_327_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_353_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_334_ = lean_array_get_size(v_x_326_);
v___x_335_ = lean_uint64_of_nat(v_key_328_);
v___x_336_ = 32ULL;
v___x_337_ = lean_uint64_shift_right(v___x_335_, v___x_336_);
v_fold_338_ = lean_uint64_xor(v___x_335_, v___x_337_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_334_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v___x_347_ = lean_array_uget_borrowed(v_x_326_, v___x_346_);
lean_inc(v___x_347_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 2, v___x_347_);
v___x_349_ = v___x_332_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_key_328_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_value_329_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v___x_347_);
v___x_349_ = v_reuseFailAlloc_352_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; 
v___x_350_ = lean_array_uset(v_x_326_, v___x_346_, v___x_349_);
v_x_326_ = v___x_350_;
v_x_327_ = v_tail_330_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(lean_object* v_i_354_, lean_object* v_source_355_, lean_object* v_target_356_){
_start:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_array_get_size(v_source_355_);
v___x_358_ = lean_nat_dec_lt(v_i_354_, v___x_357_);
if (v___x_358_ == 0)
{
lean_dec_ref(v_source_355_);
lean_dec(v_i_354_);
return v_target_356_;
}
else
{
lean_object* v_es_359_; lean_object* v___x_360_; lean_object* v_source_361_; lean_object* v_target_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_es_359_ = lean_array_fget(v_source_355_, v_i_354_);
v___x_360_ = lean_box(0);
v_source_361_ = lean_array_fset(v_source_355_, v_i_354_, v___x_360_);
v_target_362_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_target_356_, v_es_359_);
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_i_354_, v___x_363_);
lean_dec(v_i_354_);
v_i_354_ = v___x_364_;
v_source_355_ = v_source_361_;
v_target_356_ = v_target_362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(lean_object* v_data_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_nbuckets_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_367_ = lean_array_get_size(v_data_366_);
v___x_368_ = lean_unsigned_to_nat(2u);
v_nbuckets_369_ = lean_nat_mul(v___x_367_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_box(0);
v___x_372_ = lean_mk_array(v_nbuckets_369_, v___x_371_);
v___x_373_ = lean_array_propagate_mark(v_data_366_, v___x_372_);
v___x_374_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v___x_370_, v_data_366_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(lean_object* v_m_375_, lean_object* v_a_376_, lean_object* v_b_377_){
_start:
{
lean_object* v_size_378_; lean_object* v_buckets_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_422_; 
v_size_378_ = lean_ctor_get(v_m_375_, 0);
v_buckets_379_ = lean_ctor_get(v_m_375_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_m_375_);
if (v_isSharedCheck_422_ == 0)
{
v___x_381_ = v_m_375_;
v_isShared_382_ = v_isSharedCheck_422_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_buckets_379_);
lean_inc(v_size_378_);
lean_dec(v_m_375_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_422_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v_fold_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; lean_object* v_bkt_396_; uint8_t v___x_397_; 
v___x_383_ = lean_array_get_size(v_buckets_379_);
v___x_384_ = lean_uint64_of_nat(v_a_376_);
v___x_385_ = 32ULL;
v___x_386_ = lean_uint64_shift_right(v___x_384_, v___x_385_);
v_fold_387_ = lean_uint64_xor(v___x_384_, v___x_386_);
v___x_388_ = 16ULL;
v___x_389_ = lean_uint64_shift_right(v_fold_387_, v___x_388_);
v___x_390_ = lean_uint64_xor(v_fold_387_, v___x_389_);
v___x_391_ = lean_uint64_to_usize(v___x_390_);
v___x_392_ = lean_usize_of_nat(v___x_383_);
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_sub(v___x_392_, v___x_393_);
v___x_395_ = lean_usize_land(v___x_391_, v___x_394_);
v_bkt_396_ = lean_array_uget_borrowed(v_buckets_379_, v___x_395_);
v___x_397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_376_, v_bkt_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v_size_x27_399_; lean_object* v___x_400_; lean_object* v_buckets_x27_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v_size_x27_399_ = lean_nat_add(v_size_378_, v___x_398_);
lean_dec(v_size_378_);
lean_inc(v_bkt_396_);
v___x_400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_400_, 0, v_a_376_);
lean_ctor_set(v___x_400_, 1, v_b_377_);
lean_ctor_set(v___x_400_, 2, v_bkt_396_);
v_buckets_x27_401_ = lean_array_uset(v_buckets_379_, v___x_395_, v___x_400_);
v___x_402_ = lean_unsigned_to_nat(4u);
v___x_403_ = lean_nat_mul(v_size_x27_399_, v___x_402_);
v___x_404_ = lean_unsigned_to_nat(3u);
v___x_405_ = lean_nat_div(v___x_403_, v___x_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_array_get_size(v_buckets_x27_401_);
v___x_407_ = lean_nat_dec_le(v___x_405_, v___x_406_);
lean_dec(v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v_val_408_; lean_object* v___x_410_; 
v_val_408_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_buckets_x27_401_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v_val_408_);
lean_ctor_set(v___x_381_, 0, v_size_x27_399_);
v___x_410_ = v___x_381_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_size_x27_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_val_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v___x_413_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v_buckets_x27_401_);
lean_ctor_set(v___x_381_, 0, v_size_x27_399_);
v___x_413_ = v___x_381_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_size_x27_399_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_buckets_x27_401_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v___x_415_; lean_object* v_buckets_x27_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_inc(v_bkt_396_);
v___x_415_ = lean_box(0);
v_buckets_x27_416_ = lean_array_uset(v_buckets_379_, v___x_395_, v___x_415_);
v___x_417_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_376_, v_b_377_, v_bkt_396_);
v___x_418_ = lean_array_uset(v_buckets_x27_416_, v___x_395_, v___x_417_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_418_);
v___x_420_ = v___x_381_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_size_378_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(lean_object* v_c_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_b_428_){
_start:
{
lean_object* v_a_430_; uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_434_ == 0)
{
return v_b_428_;
}
else
{
lean_object* v_atoms_435_; lean_object* v_polarities_436_; lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_470_; 
v_atoms_435_ = lean_ctor_get(v_c_425_, 0);
v_polarities_436_ = lean_ctor_get(v_c_425_, 1);
v_snd_437_ = lean_ctor_get(v_b_428_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_b_428_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_b_428_, 0);
lean_dec(v_unused_471_);
v___x_439_ = v_b_428_;
v_isShared_440_ = v_isSharedCheck_470_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v_b_428_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_470_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___y_444_; uint8_t v___y_453_; uint8_t v___x_459_; uint8_t v___x_460_; uint8_t v___x_461_; uint8_t v_val_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_441_ = lean_array_uget_borrowed(v_atoms_435_, v_i_427_);
v___x_442_ = lean_box(0);
v___x_459_ = lean_byte_array_uget(v_polarities_436_, v_i_427_);
v___x_460_ = 1;
v___x_461_ = lean_uint8_dec_eq(v___x_459_, v___x_460_);
v___x_464_ = 0;
v___x_465_ = lean_box(v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_437_, v___x_441_, v___x_465_);
lean_dec(v___x_465_);
v___x_467_ = lean_unbox(v___x_466_);
lean_dec(v___x_466_);
switch(v___x_467_)
{
case 0:
{
lean_del_object(v___x_439_);
if (v___x_461_ == 0)
{
if (v___x_434_ == 0)
{
goto v___jp_457_;
}
else
{
uint8_t v___x_468_; 
v___x_468_ = 1;
v___y_453_ = v___x_468_;
goto v___jp_452_;
}
}
else
{
goto v___jp_457_;
}
}
case 1:
{
v_val_463_ = v___x_434_;
goto v___jp_462_;
}
default: 
{
uint8_t v___x_469_; 
v___x_469_ = 0;
v_val_463_ = v___x_469_;
goto v___jp_462_;
}
}
v___jp_443_:
{
if (v___y_444_ == 0)
{
lean_object* v___x_446_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_446_ = v___x_439_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_snd_437_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v_a_430_ = v___x_446_;
goto v___jp_429_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_448_);
v___x_450_ = v___x_439_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_437_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
v___jp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_box(v___y_453_);
lean_inc(v___x_441_);
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_437_, v___x_441_, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_442_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v_a_430_ = v___x_456_;
goto v___jp_429_;
}
v___jp_457_:
{
uint8_t v___x_458_; 
v___x_458_ = 2;
v___y_453_ = v___x_458_;
goto v___jp_452_;
}
v___jp_462_:
{
if (v___x_461_ == 0)
{
if (v_val_463_ == 0)
{
v___y_444_ = v___x_434_;
goto v___jp_443_;
}
else
{
v___y_444_ = v___x_461_;
goto v___jp_443_;
}
}
else
{
v___y_444_ = v_val_463_;
goto v___jp_443_;
}
}
}
}
v___jp_429_:
{
size_t v___x_431_; size_t v___x_432_; 
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_427_, v___x_431_);
v_i_427_ = v___x_432_;
v_b_428_ = v_a_430_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_425_ = stack[0].m_obj;
size_t v_sz_426_ = stack[1].m_num;
size_t v_i_427_ = stack[2].m_num;
lean_object* v_b_428_ = stack[3].m_obj;
lean_object* v_res_472_;
v_res_472_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_c_425_, v_sz_426_, v_i_427_, v_b_428_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___boxed(lean_object* v_c_473_, lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_b_476_){
_start:
{
size_t v_sz_boxed_477_; size_t v_i_boxed_478_; lean_object* v_res_479_; 
v_sz_boxed_477_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_478_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_479_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_c_473_, v_sz_boxed_477_, v_i_boxed_478_, v_b_476_);
lean_dec_ref(v_c_473_);
return v_res_479_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0(void){
_start:
{
lean_object* v_assign_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_assign_480_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty;
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_assign_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object* v_clause_483_){
_start:
{
lean_object* v_atoms_484_; lean_object* v___x_485_; size_t v_sz_486_; size_t v___x_487_; lean_object* v___x_488_; lean_object* v_fst_489_; 
v_atoms_484_ = lean_ctor_get(v_clause_483_, 0);
v___x_485_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0);
v_sz_486_ = lean_array_size(v_atoms_484_);
v___x_487_ = ((size_t)0ULL);
v___x_488_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_clause_483_, v_sz_486_, v___x_487_, v___x_485_);
v_fst_489_ = lean_ctor_get(v___x_488_, 0);
if (lean_obj_tag(v_fst_489_) == 0)
{
lean_object* v_snd_490_; lean_object* v___x_491_; 
v_snd_490_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_snd_490_);
lean_dec_ref(v___x_488_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_snd_490_);
return v___x_491_;
}
else
{
lean_object* v_val_492_; 
lean_inc_ref(v_fst_489_);
lean_dec_ref(v___x_488_);
v_val_492_ = lean_ctor_get(v_fst_489_, 0);
lean_inc(v_val_492_);
lean_dec_ref_known(v_fst_489_, 1);
return v_val_492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___boxed(lean_object* v_clause_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_493_);
lean_dec_ref(v_clause_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(lean_object* v_00_u03b2_495_, lean_object* v_m_496_, lean_object* v_a_497_, lean_object* v_fallback_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_496_, v_a_497_, v_fallback_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___boxed(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_, lean_object* v_fallback_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(v_00_u03b2_500_, v_m_501_, v_a_502_, v_fallback_503_);
lean_dec(v_fallback_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_m_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1(lean_object* v_00_u03b2_505_, lean_object* v_m_506_, lean_object* v_a_507_, lean_object* v_b_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_m_506_, v_a_507_, v_b_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(lean_object* v_00_u03b2_510_, lean_object* v_a_511_, lean_object* v_fallback_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_511_, v_fallback_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___boxed(lean_object* v_00_u03b2_515_, lean_object* v_a_516_, lean_object* v_fallback_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(v_00_u03b2_515_, v_a_516_, v_fallback_517_, v_x_518_);
lean_dec(v_x_518_);
lean_dec(v_fallback_517_);
lean_dec(v_a_516_);
return v_res_519_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_521_ = stack[1].m_obj;
lean_object* v_x_522_ = stack[2].m_obj;
uint8_t v_res_524_;
v_res_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(lean_box(0), v_a_521_, v_x_522_);
stack->m_num = v_res_524_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___boxed(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v_res_528_; lean_object* v_r_529_; 
v_res_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(v_00_u03b2_525_, v_a_526_, v_x_527_);
lean_dec(v_x_527_);
lean_dec(v_a_526_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3(lean_object* v_00_u03b2_530_, lean_object* v_data_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_data_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_b_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_534_, v_b_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_538_, lean_object* v_i_539_, lean_object* v_source_540_, lean_object* v_target_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v_i_539_, v_source_540_, v_target_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_x_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter___redArg(lean_object* v_x_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_){
_start:
{
if (lean_obj_tag(v_x_547_) == 1)
{
lean_object* v_val_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_549_);
v_val_550_ = lean_ctor_get(v_x_547_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_x_547_, 1);
v___x_551_ = lean_apply_1(v_h__1_548_, v_val_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; 
lean_dec(v_h__1_548_);
v___x_552_ = lean_apply_2(v_h__2_549_, v_x_547_, lean_box(0));
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter(lean_object* v_motive_553_, lean_object* v_x_554_, lean_object* v_h__1_555_, lean_object* v_h__2_556_){
_start:
{
if (lean_obj_tag(v_x_554_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_558_; 
lean_dec(v_h__2_556_);
v_val_557_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v_x_554_, 1);
v___x_558_ = lean_apply_1(v_h__1_555_, v_val_557_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
lean_dec(v_h__1_555_);
v___x_559_ = lean_apply_2(v_h__2_556_, v_x_554_, lean_box(0));
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_560_, lean_object* v_h__1_561_, lean_object* v_h__2_562_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_h__1_561_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_apply_1(v_h__2_562_, v___x_563_);
return v___x_564_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_566_; 
lean_dec(v_h__2_562_);
v_val_565_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v_x_560_, 1);
v___x_566_ = lean_apply_1(v_h__1_561_, v_val_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_567_, lean_object* v_motive_568_, lean_object* v_x_569_, lean_object* v_h__1_570_, lean_object* v_h__2_571_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_h__1_570_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_apply_1(v_h__2_571_, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_575_; 
lean_dec(v_h__2_571_);
v_val_574_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_x_569_, 1);
v___x_575_ = lean_apply_1(v_h__1_570_, v_val_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter___redArg(lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_h__2_578_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_h__1_577_, v___x_579_);
return v___x_580_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_582_; 
lean_dec(v_h__1_577_);
v_val_581_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_x_576_, 1);
v___x_582_ = lean_apply_1(v_h__2_578_, v_val_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter(lean_object* v_motive_583_, lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__2_586_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_apply_1(v_h__1_585_, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v_val_589_; lean_object* v___x_590_; 
lean_dec(v_h__1_585_);
v_val_589_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_x_584_, 1);
v___x_590_ = lean_apply_1(v_h__2_586_, v_val_589_);
return v___x_590_;
}
}
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(lean_object* v_lit_591_, lean_object* v_c_592_, size_t v_sz_593_, size_t v_i_594_, lean_object* v_b_595_){
_start:
{
lean_object* v_a_597_; uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_lt(v_i_594_, v_sz_593_);
if (v___x_601_ == 0)
{
return v_b_595_;
}
else
{
lean_object* v_atoms_602_; lean_object* v_polarities_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_647_; 
v_atoms_602_ = lean_ctor_get(v_c_592_, 0);
v_polarities_603_ = lean_ctor_get(v_c_592_, 1);
v_fst_604_ = lean_ctor_get(v_lit_591_, 0);
v_snd_605_ = lean_ctor_get(v_lit_591_, 1);
v_snd_606_ = lean_ctor_get(v_b_595_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_b_595_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v_b_595_, 0);
lean_dec(v_unused_648_);
v___x_608_ = v_b_595_;
v_isShared_609_ = v_isSharedCheck_647_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_dec(v_b_595_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_647_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___y_613_; uint8_t v___y_622_; uint8_t v___y_627_; uint8_t v___x_630_; uint8_t v___x_631_; uint8_t v___x_632_; uint8_t v_val_634_; uint8_t v___y_636_; uint8_t v___y_642_; uint8_t v___x_644_; 
v___x_610_ = lean_array_uget_borrowed(v_atoms_602_, v_i_594_);
v___x_611_ = lean_box(0);
v___x_630_ = lean_byte_array_uget(v_polarities_603_, v_i_594_);
v___x_631_ = 1;
v___x_632_ = lean_uint8_dec_eq(v___x_630_, v___x_631_);
v___x_644_ = lean_nat_dec_eq(v___x_610_, v_fst_604_);
if (v___x_644_ == 0)
{
v___y_636_ = v___x_644_;
goto v___jp_635_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = lean_unbox(v_snd_605_);
if (v___x_645_ == 0)
{
if (v___x_632_ == 0)
{
v___y_642_ = v___x_644_;
goto v___jp_641_;
}
else
{
uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_snd_605_);
v___y_636_ = v___x_646_;
goto v___jp_635_;
}
}
else
{
v___y_642_ = v___x_632_;
goto v___jp_641_;
}
}
v___jp_612_:
{
if (v___y_613_ == 0)
{
lean_object* v___x_615_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_snd_606_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v_a_597_ = v___x_615_;
goto v___jp_596_;
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_617_);
v___x_619_ = v___x_608_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_snd_606_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_box(v___y_622_);
lean_inc(v___x_610_);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_606_, v___x_610_, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_611_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v_a_597_ = v___x_625_;
goto v___jp_596_;
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
uint8_t v___x_628_; 
v___x_628_ = 2;
v___y_622_ = v___x_628_;
goto v___jp_621_;
}
else
{
uint8_t v___x_629_; 
v___x_629_ = 1;
v___y_622_ = v___x_629_;
goto v___jp_621_;
}
}
v___jp_633_:
{
if (v___x_632_ == 0)
{
if (v_val_634_ == 0)
{
v___y_613_ = v___x_601_;
goto v___jp_612_;
}
else
{
v___y_613_ = v___x_632_;
goto v___jp_612_;
}
}
else
{
v___y_613_ = v_val_634_;
goto v___jp_612_;
}
}
v___jp_635_:
{
uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_637_ = 0;
v___x_638_ = lean_box(v___x_637_);
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_606_, v___x_610_, v___x_638_);
lean_dec(v___x_638_);
v___x_640_ = lean_unbox(v___x_639_);
lean_dec(v___x_639_);
switch(v___x_640_)
{
case 0:
{
lean_del_object(v___x_608_);
if (v___x_632_ == 0)
{
v___y_627_ = v___x_601_;
goto v___jp_626_;
}
else
{
v___y_627_ = v___y_636_;
goto v___jp_626_;
}
}
case 1:
{
v_val_634_ = v___x_601_;
goto v___jp_633_;
}
default: 
{
v_val_634_ = v___y_636_;
goto v___jp_633_;
}
}
}
v___jp_641_:
{
if (v___y_642_ == 0)
{
v___y_636_ = v___y_642_;
goto v___jp_635_;
}
else
{
lean_object* v___x_643_; 
lean_del_object(v___x_608_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_611_);
lean_ctor_set(v___x_643_, 1, v_snd_606_);
v_a_597_ = v___x_643_;
goto v___jp_596_;
}
}
}
}
v___jp_596_:
{
size_t v___x_598_; size_t v___x_599_; 
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_add(v_i_594_, v___x_598_);
v_i_594_ = v___x_599_;
v_b_595_ = v_a_597_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lit_591_ = stack[0].m_obj;
lean_object* v_c_592_ = stack[1].m_obj;
size_t v_sz_593_ = stack[2].m_num;
size_t v_i_594_ = stack[3].m_num;
lean_object* v_b_595_ = stack[4].m_obj;
lean_object* v_res_649_;
v_res_649_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_591_, v_c_592_, v_sz_593_, v_i_594_, v_b_595_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0___boxed(lean_object* v_lit_650_, lean_object* v_c_651_, lean_object* v_sz_652_, lean_object* v_i_653_, lean_object* v_b_654_){
_start:
{
size_t v_sz_boxed_655_; size_t v_i_boxed_656_; lean_object* v_res_657_; 
v_sz_boxed_655_ = lean_unbox_usize(v_sz_652_);
lean_dec(v_sz_652_);
v_i_boxed_656_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_res_657_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_650_, v_c_651_, v_sz_boxed_655_, v_i_boxed_656_, v_b_654_);
lean_dec_ref(v_c_651_);
lean_dec_ref(v_lit_650_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object* v_assign_658_, lean_object* v_c_659_, lean_object* v_lit_660_){
_start:
{
lean_object* v_atoms_661_; lean_object* v___x_662_; lean_object* v___x_663_; size_t v_sz_664_; size_t v___x_665_; lean_object* v___x_666_; lean_object* v_fst_667_; 
v_atoms_661_ = lean_ctor_get(v_c_659_, 0);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_assign_658_);
v_sz_664_ = lean_array_size(v_atoms_661_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_660_, v_c_659_, v_sz_664_, v___x_665_, v___x_663_);
v_fst_667_ = lean_ctor_get(v___x_666_, 0);
if (lean_obj_tag(v_fst_667_) == 0)
{
lean_object* v_snd_668_; lean_object* v___x_669_; 
v_snd_668_ = lean_ctor_get(v___x_666_, 1);
lean_inc(v_snd_668_);
lean_dec_ref(v___x_666_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_snd_668_);
return v___x_669_;
}
else
{
lean_object* v_val_670_; 
lean_inc_ref(v_fst_667_);
lean_dec_ref(v___x_666_);
v_val_670_ = lean_ctor_get(v_fst_667_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_fst_667_, 1);
return v_val_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout___boxed(lean_object* v_assign_671_, lean_object* v_c_672_, lean_object* v_lit_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_671_, v_c_672_, v_lit_673_);
lean_dec_ref(v_lit_673_);
lean_dec_ref(v_c_672_);
return v_res_674_;
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
