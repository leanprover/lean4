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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(lean_object* v_unassigned_22_){
_start:
{
lean_inc(v_unassigned_22_);
return v_unassigned_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg___boxed(lean_object* v_unassigned_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___redArg(v_unassigned_23_);
lean_dec(v_unassigned_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_unassigned_28_){
_start:
{
lean_inc(v_unassigned_28_);
return v_unassigned_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_unassigned_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_unassigned_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_unassigned_32_);
lean_dec(v_unassigned_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(lean_object* v_true_35_){
_start:
{
lean_inc(v_true_35_);
return v_true_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg___boxed(lean_object* v_true_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___redArg(v_true_36_);
lean_dec(v_true_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_true_41_){
_start:
{
lean_inc(v_true_41_);
return v_true_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_true_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_true_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_true_45_);
lean_dec(v_true_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(lean_object* v_false_48_){
_start:
{
lean_inc(v_false_48_);
return v_false_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg___boxed(lean_object* v_false_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___redArg(v_false_49_);
lean_dec(v_false_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_false_54_){
_start:
{
lean_inc(v_false_54_);
return v_false_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_false_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_false_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_false_58_);
lean_dec(v_false_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(uint8_t v_x_61_){
_start:
{
if (v_x_61_ == 0)
{
uint8_t v___x_62_; 
v___x_62_ = 2;
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 1;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool___boxed(lean_object* v_x_64_){
_start:
{
uint8_t v_x_18__boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_x_18__boxed_65_ = lean_unbox(v_x_64_);
v_res_66_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_ofBool(v_x_18__boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(uint8_t v_x_74_){
_start:
{
switch(v_x_74_)
{
case 0:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
case 1:
{
lean_object* v___x_76_; 
v___x_76_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0));
return v___x_76_;
}
default: 
{
lean_object* v___x_77_; 
v___x_77_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1));
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___boxed(lean_object* v_x_78_){
_start:
{
uint8_t v_x_37__boxed_79_; lean_object* v_res_80_; 
v_x_37__boxed_79_ = lean_unbox(v_x_78_);
v_res_80_ = l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption(v_x_37__boxed_79_);
return v_res_80_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_unsigned_to_nat(16u);
v___x_83_ = lean_mk_array(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__0);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty___closed__1);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1(void){
_start:
{
lean_object* v___x_89_; lean_object* v___f_90_; 
v___x_89_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_90_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_90_, 0, v___x_89_);
return v___f_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(lean_object* v_a_91_, lean_object* v_atom_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___f_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___f_93_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_94_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_95_ = 0;
v___x_96_ = lean_box(v___x_95_);
v___x_97_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_94_, v___f_93_, v_a_91_, v_atom_92_, v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = lean_unbox(v___x_97_);
lean_dec(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___boxed(lean_object* v_a_99_, lean_object* v_atom_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get(v_a_99_, v_atom_100_);
lean_dec_ref(v_a_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(lean_object* v_a_103_, lean_object* v_atom_104_){
_start:
{
lean_object* v___f_105_; lean_object* v___f_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___f_105_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_106_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_107_ = 0;
v___x_108_ = lean_box(v___x_107_);
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_106_, v___f_105_, v_a_103_, v_atom_104_, v___x_108_);
lean_dec(v___x_108_);
v___x_110_ = lean_unbox(v___x_109_);
lean_dec(v___x_109_);
switch(v___x_110_)
{
case 0:
{
lean_object* v___x_111_; 
v___x_111_ = lean_box(0);
return v___x_111_;
}
case 1:
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__0));
return v___x_112_;
}
default: 
{
lean_object* v___x_113_; 
v___x_113_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption___closed__1));
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f___boxed(lean_object* v_a_114_, lean_object* v_atom_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get_x3f(v_a_114_, v_atom_115_);
lean_dec_ref(v_a_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(lean_object* v_a_117_, lean_object* v_atom_118_, uint8_t v_b_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___f_121_; 
v___f_120_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_121_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
if (v_b_119_ == 0)
{
uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = 2;
v___x_123_ = lean_box(v___x_122_);
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_121_, v___f_120_, v_a_117_, v_atom_118_, v___x_123_);
return v___x_124_;
}
else
{
uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = 1;
v___x_126_ = lean_box(v___x_125_);
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_121_, v___f_120_, v_a_117_, v_atom_118_, v___x_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert___boxed(lean_object* v_a_128_, lean_object* v_atom_129_, lean_object* v_b_130_){
_start:
{
uint8_t v_b_boxed_131_; lean_object* v_res_132_; 
v_b_boxed_131_ = lean_unbox(v_b_130_);
v_res_132_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_insert(v_a_128_, v_atom_129_, v_b_boxed_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_erase(lean_object* v_a_133_, lean_object* v_atom_134_){
_start:
{
lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___x_137_; 
v___f_135_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__0));
v___f_136_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_get___closed__1);
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___f_136_, v___f_135_, v_a_133_, v_atom_134_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_inc(v_x_138_);
return v_x_138_;
}
else
{
lean_object* v_key_140_; lean_object* v_value_141_; lean_object* v_tail_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_key_140_ = lean_ctor_get(v_x_139_, 0);
v_value_141_ = lean_ctor_get(v_x_139_, 1);
v_tail_142_ = lean_ctor_get(v_x_139_, 2);
v___x_143_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_x_138_, v_tail_142_);
lean_inc(v_value_141_);
lean_inc(v_key_140_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v_key_140_);
lean_ctor_set(v___x_144_, 1, v_value_141_);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0___boxed(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_x_146_, v_x_147_);
lean_dec(v_x_147_);
lean_dec(v_x_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(lean_object* v_as_149_, size_t v_i_150_, size_t v_stop_151_, lean_object* v_b_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = lean_usize_dec_eq(v_i_150_, v_stop_151_);
if (v___x_153_ == 0)
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_sub(v_i_150_, v___x_154_);
v___x_156_ = lean_array_uget_borrowed(v_as_149_, v___x_155_);
v___x_157_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__0(v_b_152_, v___x_156_);
lean_dec(v_b_152_);
v_i_150_ = v___x_155_;
v_b_152_ = v___x_157_;
goto _start;
}
else
{
return v_b_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2___boxed(lean_object* v_as_159_, lean_object* v_i_160_, lean_object* v_stop_161_, lean_object* v_b_162_){
_start:
{
size_t v_i_boxed_163_; size_t v_stop_boxed_164_; lean_object* v_res_165_; 
v_i_boxed_163_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_stop_boxed_164_ = lean_unbox_usize(v_stop_161_);
lean_dec(v_stop_161_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_as_159_, v_i_boxed_163_, v_stop_boxed_164_, v_b_162_);
lean_dec_ref(v_as_159_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
return v_x_166_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v_fst_170_; lean_object* v_snd_171_; uint8_t v_val_173_; uint8_t v___x_177_; 
v_head_168_ = lean_ctor_get(v_x_167_, 0);
lean_inc(v_head_168_);
v_tail_169_ = lean_ctor_get(v_x_167_, 1);
lean_inc(v_tail_169_);
lean_dec_ref_known(v_x_167_, 2);
v_fst_170_ = lean_ctor_get(v_head_168_, 0);
lean_inc(v_fst_170_);
v_snd_171_ = lean_ctor_get(v_head_168_, 1);
lean_inc(v_snd_171_);
lean_dec(v_head_168_);
v___x_177_ = lean_unbox(v_snd_171_);
lean_dec(v_snd_171_);
switch(v___x_177_)
{
case 0:
{
lean_dec(v_fst_170_);
v_x_167_ = v_tail_169_;
goto _start;
}
case 1:
{
uint8_t v___x_179_; 
v___x_179_ = 1;
v_val_173_ = v___x_179_;
goto v___jp_172_;
}
default: 
{
uint8_t v___x_180_; 
v___x_180_ = 0;
v_val_173_ = v___x_180_;
goto v___jp_172_;
}
}
v___jp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Std_Sat_CNF_Clause_unit___redArg(v_fst_170_, v_val_173_);
v___x_175_ = lean_array_push(v_x_166_, v___x_174_);
v_x_166_ = v___x_175_;
v_x_167_ = v_tail_169_;
goto _start;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_box(0);
v___x_184_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0));
v___x_185_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(v___x_184_, v___x_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(lean_object* v_a_186_){
_start:
{
lean_object* v_buckets_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_buckets_187_ = lean_ctor_get(v_a_186_, 1);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__0));
v___x_190_ = lean_box(0);
v___x_191_ = lean_array_get_size(v_buckets_187_);
v___x_192_ = lean_nat_dec_lt(v___x_188_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___closed__1);
return v___x_193_;
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_usize_of_nat(v___x_191_);
v___x_195_ = ((size_t)0ULL);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__2(v_buckets_187_, v___x_194_, v___x_195_, v___x_190_);
v___x_197_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_spec__1(v___x_189_, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF___boxed(lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF(v_a_198_);
lean_dec_ref(v_a_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter___redArg(lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__1_201_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__2_202_, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
lean_dec(v_h__2_202_);
v_val_205_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v_x_200_, 1);
v___x_206_ = lean_apply_1(v_h__1_201_, v_val_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCNF_match__1_splitter(lean_object* v_motive_207_, lean_object* v_x_208_, lean_object* v_h__1_209_, lean_object* v_h__2_210_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__1_209_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__2_210_, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v_val_213_; lean_object* v___x_214_; 
lean_dec(v_h__2_210_);
v_val_213_ = lean_ctor_get(v_x_208_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_x_208_, 1);
v___x_214_ = lean_apply_1(v_h__1_209_, v_val_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(uint8_t v_x_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_, lean_object* v_h__3_218_){
_start:
{
switch(v_x_215_)
{
case 0:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_h__3_218_);
lean_dec(v_h__2_217_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_apply_1(v_h__1_216_, v___x_219_);
return v___x_220_;
}
case 1:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_h__3_218_);
lean_dec(v_h__1_216_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v_h__2_217_, v___x_221_);
return v___x_222_;
}
default: 
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__2_217_);
lean_dec(v_h__1_216_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__3_218_, v___x_223_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg___boxed(lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_){
_start:
{
uint8_t v_x_33__boxed_229_; lean_object* v_res_230_; 
v_x_33__boxed_229_ = lean_unbox(v_x_225_);
v_res_230_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___redArg(v_x_33__boxed_229_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(lean_object* v_motive_231_, uint8_t v_x_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_, lean_object* v_h__3_235_){
_start:
{
switch(v_x_232_)
{
case 0:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__3_235_);
lean_dec(v_h__2_234_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__1_233_, v___x_236_);
return v___x_237_;
}
case 1:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_h__3_235_);
lean_dec(v_h__1_233_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_apply_1(v_h__2_234_, v___x_238_);
return v___x_239_;
}
default: 
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_234_);
lean_dec(v_h__1_233_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_1(v_h__3_235_, v___x_240_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter___boxed(lean_object* v_motive_242_, lean_object* v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_, lean_object* v_h__3_246_){
_start:
{
uint8_t v_x_48__boxed_247_; lean_object* v_res_248_; 
v_x_48__boxed_247_ = lean_unbox(v_x_243_);
v_res_248_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_AssignValue_toOption_match__1_splitter(v_motive_242_, v_x_48__boxed_247_, v_h__1_244_, v_h__2_245_, v_h__3_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(lean_object* v_a_249_, lean_object* v_fallback_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_inc(v_fallback_250_);
return v_fallback_250_;
}
else
{
lean_object* v_key_252_; lean_object* v_value_253_; lean_object* v_tail_254_; uint8_t v___x_255_; 
v_key_252_ = lean_ctor_get(v_x_251_, 0);
v_value_253_ = lean_ctor_get(v_x_251_, 1);
v_tail_254_ = lean_ctor_get(v_x_251_, 2);
v___x_255_ = lean_nat_dec_eq(v_key_252_, v_a_249_);
if (v___x_255_ == 0)
{
v_x_251_ = v_tail_254_;
goto _start;
}
else
{
lean_inc(v_value_253_);
return v_value_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg___boxed(lean_object* v_a_257_, lean_object* v_fallback_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_257_, v_fallback_258_, v_x_259_);
lean_dec(v_x_259_);
lean_dec(v_fallback_258_);
lean_dec(v_a_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(lean_object* v_m_261_, lean_object* v_a_262_, lean_object* v_fallback_263_){
_start:
{
lean_object* v_buckets_264_; lean_object* v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v_fold_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_buckets_264_ = lean_ctor_get(v_m_261_, 1);
v___x_265_ = lean_array_get_size(v_buckets_264_);
v___x_266_ = lean_uint64_of_nat(v_a_262_);
v___x_267_ = 32ULL;
v___x_268_ = lean_uint64_shift_right(v___x_266_, v___x_267_);
v_fold_269_ = lean_uint64_xor(v___x_266_, v___x_268_);
v___x_270_ = 16ULL;
v___x_271_ = lean_uint64_shift_right(v_fold_269_, v___x_270_);
v___x_272_ = lean_uint64_xor(v_fold_269_, v___x_271_);
v___x_273_ = lean_uint64_to_usize(v___x_272_);
v___x_274_ = lean_usize_of_nat(v___x_265_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_sub(v___x_274_, v___x_275_);
v___x_277_ = lean_usize_land(v___x_273_, v___x_276_);
v___x_278_ = lean_array_uget_borrowed(v_buckets_264_, v___x_277_);
v___x_279_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_262_, v_fallback_263_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg___boxed(lean_object* v_m_280_, lean_object* v_a_281_, lean_object* v_fallback_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_280_, v_a_281_, v_fallback_282_);
lean_dec(v_fallback_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_m_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(lean_object* v_a_284_, lean_object* v_b_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_dec(v_b_285_);
lean_dec(v_a_284_);
return v_x_286_;
}
else
{
lean_object* v_key_287_; lean_object* v_value_288_; lean_object* v_tail_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_301_; 
v_key_287_ = lean_ctor_get(v_x_286_, 0);
v_value_288_ = lean_ctor_get(v_x_286_, 1);
v_tail_289_ = lean_ctor_get(v_x_286_, 2);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_301_ == 0)
{
v___x_291_ = v_x_286_;
v_isShared_292_ = v_isSharedCheck_301_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_tail_289_);
lean_inc(v_value_288_);
lean_inc(v_key_287_);
lean_dec(v_x_286_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_301_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v___x_293_; 
v___x_293_ = lean_nat_dec_eq(v_key_287_, v_a_284_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_284_, v_b_285_, v_tail_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 2, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_key_287_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_value_288_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v_value_288_);
lean_dec(v_key_287_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_b_285_);
lean_ctor_set(v___x_291_, 0, v_a_284_);
v___x_299_ = v___x_291_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_284_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_b_285_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_tail_289_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(lean_object* v_a_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
else
{
lean_object* v_key_305_; lean_object* v_tail_306_; uint8_t v___x_307_; 
v_key_305_ = lean_ctor_get(v_x_303_, 0);
v_tail_306_ = lean_ctor_get(v_x_303_, 2);
v___x_307_ = lean_nat_dec_eq(v_key_305_, v_a_302_);
if (v___x_307_ == 0)
{
v_x_303_ = v_tail_306_;
goto _start;
}
else
{
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg___boxed(lean_object* v_a_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_309_, v_x_310_);
lean_dec(v_x_310_);
lean_dec(v_a_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
return v_x_313_;
}
else
{
lean_object* v_key_315_; lean_object* v_value_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_340_; 
v_key_315_ = lean_ctor_get(v_x_314_, 0);
v_value_316_ = lean_ctor_get(v_x_314_, 1);
v_tail_317_ = lean_ctor_get(v_x_314_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_340_ == 0)
{
v___x_319_ = v_x_314_;
v_isShared_320_ = v_isSharedCheck_340_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_value_316_);
lean_inc(v_key_315_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_340_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v_fold_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_321_ = lean_array_get_size(v_x_313_);
v___x_322_ = lean_uint64_of_nat(v_key_315_);
v___x_323_ = 32ULL;
v___x_324_ = lean_uint64_shift_right(v___x_322_, v___x_323_);
v_fold_325_ = lean_uint64_xor(v___x_322_, v___x_324_);
v___x_326_ = 16ULL;
v___x_327_ = lean_uint64_shift_right(v_fold_325_, v___x_326_);
v___x_328_ = lean_uint64_xor(v_fold_325_, v___x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = lean_usize_of_nat(v___x_321_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_land(v___x_329_, v___x_332_);
v___x_334_ = lean_array_uget_borrowed(v_x_313_, v___x_333_);
lean_inc(v___x_334_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 2, v___x_334_);
v___x_336_ = v___x_319_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_key_315_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_value_316_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v___x_334_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_array_uset(v_x_313_, v___x_333_, v___x_336_);
v_x_313_ = v___x_337_;
v_x_314_ = v_tail_317_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(lean_object* v_i_341_, lean_object* v_source_342_, lean_object* v_target_343_){
_start:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_array_get_size(v_source_342_);
v___x_345_ = lean_nat_dec_lt(v_i_341_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v_source_342_);
lean_dec(v_i_341_);
return v_target_343_;
}
else
{
lean_object* v_es_346_; lean_object* v___x_347_; lean_object* v_source_348_; lean_object* v_target_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_es_346_ = lean_array_fget(v_source_342_, v_i_341_);
v___x_347_ = lean_box(0);
v_source_348_ = lean_array_fset(v_source_342_, v_i_341_, v___x_347_);
v_target_349_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_target_343_, v_es_346_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_i_341_, v___x_350_);
lean_dec(v_i_341_);
v_i_341_ = v___x_351_;
v_source_342_ = v_source_348_;
v_target_343_ = v_target_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(lean_object* v_data_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_nbuckets_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_354_ = lean_array_get_size(v_data_353_);
v___x_355_ = lean_unsigned_to_nat(2u);
v_nbuckets_356_ = lean_nat_mul(v___x_354_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_box(0);
v___x_359_ = lean_mk_array(v_nbuckets_356_, v___x_358_);
v___x_360_ = lean_array_propagate_mark(v_data_353_, v___x_359_);
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v___x_357_, v_data_353_, v___x_360_);
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
lean_object* v_atoms_422_; lean_object* v_polarities_423_; lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_454_; 
v_atoms_422_ = lean_ctor_get(v_c_412_, 0);
v_polarities_423_ = lean_ctor_get(v_c_412_, 1);
v_snd_424_ = lean_ctor_get(v_b_415_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_b_415_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v_b_415_, 0);
lean_dec(v_unused_455_);
v___x_426_ = v_b_415_;
v_isShared_427_ = v_isSharedCheck_454_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_dec(v_b_415_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_454_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___y_438_; uint8_t v___x_442_; uint8_t v___x_443_; uint8_t v___x_444_; uint8_t v_val_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_433_ = lean_array_uget_borrowed(v_atoms_422_, v_i_414_);
v___x_434_ = lean_box(0);
v___x_442_ = lean_byte_array_uget(v_polarities_423_, v_i_414_);
v___x_443_ = 1;
v___x_444_ = lean_uint8_dec_eq(v___x_442_, v___x_443_);
v___x_447_ = 0;
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_424_, v___x_433_, v___x_448_);
lean_dec(v___x_448_);
v___x_450_ = lean_unbox(v___x_449_);
lean_dec(v___x_449_);
switch(v___x_450_)
{
case 0:
{
lean_del_object(v___x_426_);
if (v___x_444_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = 1;
v___y_438_ = v___x_451_;
goto v___jp_437_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 2;
v___y_438_ = v___x_452_;
goto v___jp_437_;
}
}
case 1:
{
v_val_446_ = v___x_421_;
goto v___jp_445_;
}
default: 
{
uint8_t v___x_453_; 
v___x_453_ = 0;
v_val_446_ = v___x_453_;
goto v___jp_445_;
}
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_snd_424_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
v___jp_435_:
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v_snd_424_);
v_a_417_ = v___x_436_;
goto v___jp_416_;
}
v___jp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_box(v___y_438_);
lean_inc(v___x_433_);
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_424_, v___x_433_, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_434_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v_a_417_ = v___x_441_;
goto v___jp_416_;
}
v___jp_445_:
{
if (v___x_444_ == 0)
{
if (v_val_446_ == 0)
{
goto v___jp_428_;
}
else
{
lean_del_object(v___x_426_);
goto v___jp_435_;
}
}
else
{
if (v_val_446_ == 0)
{
lean_del_object(v___x_426_);
goto v___jp_435_;
}
else
{
goto v___jp_428_;
}
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___boxed(lean_object* v_c_456_, lean_object* v_sz_457_, lean_object* v_i_458_, lean_object* v_b_459_){
_start:
{
size_t v_sz_boxed_460_; size_t v_i_boxed_461_; lean_object* v_res_462_; 
v_sz_boxed_460_ = lean_unbox_usize(v_sz_457_);
lean_dec(v_sz_457_);
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_res_462_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_c_456_, v_sz_boxed_460_, v_i_boxed_461_, v_b_459_);
lean_dec_ref(v_c_456_);
return v_res_462_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0(void){
_start:
{
lean_object* v_assign_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_assign_463_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_empty;
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_assign_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object* v_clause_466_){
_start:
{
lean_object* v_atoms_467_; lean_object* v___x_468_; size_t v_sz_469_; size_t v___x_470_; lean_object* v___x_471_; lean_object* v_fst_472_; 
v_atoms_467_ = lean_ctor_get(v_clause_466_, 0);
v___x_468_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___closed__0);
v_sz_469_ = lean_array_size(v_atoms_467_);
v___x_470_ = ((size_t)0ULL);
v___x_471_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2(v_clause_466_, v_sz_469_, v___x_470_, v___x_468_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
if (lean_obj_tag(v_fst_472_) == 0)
{
lean_object* v_snd_473_; lean_object* v___x_474_; 
v_snd_473_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_snd_473_);
lean_dec_ref(v___x_471_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v_snd_473_);
return v___x_474_;
}
else
{
lean_object* v_val_475_; 
lean_inc_ref(v_fst_472_);
lean_dec_ref(v___x_471_);
v_val_475_ = lean_ctor_get(v_fst_472_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v_fst_472_, 1);
return v_val_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause___boxed(lean_object* v_clause_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_476_);
lean_dec_ref(v_clause_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_fallback_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_m_479_, v_a_480_, v_fallback_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___boxed(lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_a_485_, lean_object* v_fallback_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0(v_00_u03b2_483_, v_m_484_, v_a_485_, v_fallback_486_);
lean_dec(v_fallback_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_m_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1(lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_m_489_, v_a_490_, v_b_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(lean_object* v_00_u03b2_493_, lean_object* v_a_494_, lean_object* v_fallback_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___redArg(v_a_494_, v_fallback_495_, v_x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0___boxed(lean_object* v_00_u03b2_498_, lean_object* v_a_499_, lean_object* v_fallback_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0_spec__0(v_00_u03b2_498_, v_a_499_, v_fallback_500_, v_x_501_);
lean_dec(v_x_501_);
lean_dec(v_fallback_500_);
lean_dec(v_a_499_);
return v_res_502_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(lean_object* v_00_u03b2_503_, lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___redArg(v_a_504_, v_x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2___boxed(lean_object* v_00_u03b2_507_, lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__2(v_00_u03b2_507_, v_a_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_a_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3(lean_object* v_00_u03b2_512_, lean_object* v_data_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3___redArg(v_data_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4(lean_object* v_00_u03b2_515_, lean_object* v_a_516_, lean_object* v_b_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__4___redArg(v_a_516_, v_b_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_520_, lean_object* v_i_521_, lean_object* v_source_522_, lean_object* v_target_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4___redArg(v_i_521_, v_source_522_, v_target_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1_spec__3_spec__4_spec__6___redArg(v_x_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter___redArg(lean_object* v_x_529_, lean_object* v_h__1_530_, lean_object* v_h__2_531_){
_start:
{
if (lean_obj_tag(v_x_529_) == 1)
{
lean_object* v_val_532_; lean_object* v___x_533_; 
lean_dec(v_h__2_531_);
v_val_532_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v_x_529_, 1);
v___x_533_ = lean_apply_1(v_h__1_530_, v_val_532_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
lean_dec(v_h__1_530_);
v___x_534_ = lean_apply_2(v_h__2_531_, v_x_529_, lean_box(0));
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_match__1_splitter(lean_object* v_motive_535_, lean_object* v_x_536_, lean_object* v_h__1_537_, lean_object* v_h__2_538_){
_start:
{
if (lean_obj_tag(v_x_536_) == 1)
{
lean_object* v_val_539_; lean_object* v___x_540_; 
lean_dec(v_h__2_538_);
v_val_539_ = lean_ctor_get(v_x_536_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_x_536_, 1);
v___x_540_ = lean_apply_1(v_h__1_537_, v_val_539_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; 
lean_dec(v_h__1_537_);
v___x_541_ = lean_apply_2(v_h__2_538_, v_x_536_, lean_box(0));
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_542_, lean_object* v_h__1_543_, lean_object* v_h__2_544_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_h__1_543_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_apply_1(v_h__2_544_, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_548_; 
lean_dec(v_h__2_544_);
v_val_547_ = lean_ctor_get(v_x_542_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_x_542_, 1);
v___x_548_ = lean_apply_1(v_h__1_543_, v_val_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_549_, lean_object* v_motive_550_, lean_object* v_x_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v_h__1_552_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_apply_1(v_h__2_553_, v___x_554_);
return v___x_555_;
}
else
{
lean_object* v_val_556_; lean_object* v___x_557_; 
lean_dec(v_h__2_553_);
v_val_556_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v_x_551_, 1);
v___x_557_ = lean_apply_1(v_h__1_552_, v_val_556_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter___redArg(lean_object* v_x_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_h__2_560_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_apply_1(v_h__1_559_, v___x_561_);
return v___x_562_;
}
else
{
lean_object* v_val_563_; lean_object* v___x_564_; 
lean_dec(v_h__1_559_);
v_val_563_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v_x_558_, 1);
v___x_564_ = lean_apply_1(v_h__2_560_, v_val_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause__spec_match__1_splitter(lean_object* v_motive_565_, lean_object* v_x_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_h__2_568_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_1(v_h__1_567_, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v_val_571_; lean_object* v___x_572_; 
lean_dec(v_h__1_567_);
v_val_571_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v_x_566_, 1);
v___x_572_ = lean_apply_1(v_h__2_568_, v_val_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(lean_object* v_lit_573_, lean_object* v_c_574_, size_t v_sz_575_, size_t v_i_576_, lean_object* v_b_577_){
_start:
{
lean_object* v_a_579_; uint8_t v___x_583_; 
v___x_583_ = lean_usize_dec_lt(v_i_576_, v_sz_575_);
if (v___x_583_ == 0)
{
return v_b_577_;
}
else
{
lean_object* v_atoms_584_; lean_object* v_polarities_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_625_; 
v_atoms_584_ = lean_ctor_get(v_c_574_, 0);
v_polarities_585_ = lean_ctor_get(v_c_574_, 1);
v_fst_586_ = lean_ctor_get(v_lit_573_, 0);
v_snd_587_ = lean_ctor_get(v_lit_573_, 1);
v_snd_588_ = lean_ctor_get(v_b_577_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_b_577_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_b_577_, 0);
lean_dec(v_unused_626_);
v___x_590_ = v_b_577_;
v_isShared_591_ = v_isSharedCheck_625_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_dec(v_b_577_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_625_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___y_600_; uint8_t v___x_610_; uint8_t v___x_611_; uint8_t v___x_612_; uint8_t v_val_614_; uint8_t v___y_616_; uint8_t v___x_622_; 
v___x_597_ = lean_array_uget_borrowed(v_atoms_584_, v_i_576_);
v___x_598_ = lean_box(0);
v___x_610_ = lean_byte_array_uget(v_polarities_585_, v_i_576_);
v___x_611_ = 1;
v___x_612_ = lean_uint8_dec_eq(v___x_610_, v___x_611_);
v___x_622_ = lean_nat_dec_eq(v___x_597_, v_fst_586_);
if (v___x_622_ == 0)
{
v___y_616_ = v___x_622_;
goto v___jp_615_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = lean_unbox(v_snd_587_);
if (v___x_623_ == 0)
{
if (v___x_612_ == 0)
{
lean_del_object(v___x_590_);
goto v___jp_608_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = lean_unbox(v_snd_587_);
v___y_616_ = v___x_624_;
goto v___jp_615_;
}
}
else
{
if (v___x_612_ == 0)
{
v___y_616_ = v___x_612_;
goto v___jp_615_;
}
else
{
lean_del_object(v___x_590_);
goto v___jp_608_;
}
}
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__2___closed__0));
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_snd_588_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
v___jp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(v___y_600_);
lean_inc(v___x_597_);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__1___redArg(v_snd_588_, v___x_597_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_598_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v_a_579_ = v___x_603_;
goto v___jp_578_;
}
v___jp_604_:
{
uint8_t v___x_605_; 
v___x_605_ = 1;
v___y_600_ = v___x_605_;
goto v___jp_599_;
}
v___jp_606_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_598_);
lean_ctor_set(v___x_607_, 1, v_snd_588_);
v_a_579_ = v___x_607_;
goto v___jp_578_;
}
v___jp_608_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_598_);
lean_ctor_set(v___x_609_, 1, v_snd_588_);
v_a_579_ = v___x_609_;
goto v___jp_578_;
}
v___jp_613_:
{
if (v___x_612_ == 0)
{
if (v_val_614_ == 0)
{
goto v___jp_592_;
}
else
{
lean_del_object(v___x_590_);
goto v___jp_606_;
}
}
else
{
if (v_val_614_ == 0)
{
lean_del_object(v___x_590_);
goto v___jp_606_;
}
else
{
goto v___jp_592_;
}
}
}
v___jp_615_:
{
uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_617_ = 0;
v___x_618_ = lean_box(v___x_617_);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause_spec__0___redArg(v_snd_588_, v___x_597_, v___x_618_);
lean_dec(v___x_618_);
v___x_620_ = lean_unbox(v___x_619_);
lean_dec(v___x_619_);
switch(v___x_620_)
{
case 0:
{
lean_del_object(v___x_590_);
if (v___x_612_ == 0)
{
goto v___jp_604_;
}
else
{
if (v___y_616_ == 0)
{
uint8_t v___x_621_; 
v___x_621_ = 2;
v___y_600_ = v___x_621_;
goto v___jp_599_;
}
else
{
goto v___jp_604_;
}
}
}
case 1:
{
v_val_614_ = v___x_583_;
goto v___jp_613_;
}
default: 
{
v_val_614_ = v___y_616_;
goto v___jp_613_;
}
}
}
}
}
v___jp_578_:
{
size_t v___x_580_; size_t v___x_581_; 
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_576_, v___x_580_);
v_i_576_ = v___x_581_;
v_b_577_ = v_a_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0___boxed(lean_object* v_lit_627_, lean_object* v_c_628_, lean_object* v_sz_629_, lean_object* v_i_630_, lean_object* v_b_631_){
_start:
{
size_t v_sz_boxed_632_; size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_sz_boxed_632_ = lean_unbox_usize(v_sz_629_);
lean_dec(v_sz_629_);
v_i_boxed_633_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_res_634_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_627_, v_c_628_, v_sz_boxed_632_, v_i_boxed_633_, v_b_631_);
lean_dec_ref(v_c_628_);
lean_dec_ref(v_lit_627_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object* v_assign_635_, lean_object* v_c_636_, lean_object* v_lit_637_){
_start:
{
lean_object* v_atoms_638_; lean_object* v___x_639_; lean_object* v___x_640_; size_t v_sz_641_; size_t v___x_642_; lean_object* v___x_643_; lean_object* v_fst_644_; 
v_atoms_638_ = lean_ctor_get(v_c_636_, 0);
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_assign_635_);
v_sz_641_ = lean_array_size(v_atoms_638_);
v___x_642_ = ((size_t)0ULL);
v___x_643_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout_spec__0(v_lit_637_, v_c_636_, v_sz_641_, v___x_642_, v___x_640_);
v_fst_644_ = lean_ctor_get(v___x_643_, 0);
if (lean_obj_tag(v_fst_644_) == 0)
{
lean_object* v_snd_645_; lean_object* v___x_646_; 
v_snd_645_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_snd_645_);
lean_dec_ref(v___x_643_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_snd_645_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; 
lean_inc_ref(v_fst_644_);
lean_dec_ref(v___x_643_);
v_val_647_ = lean_ctor_get(v_fst_644_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_fst_644_, 1);
return v_val_647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout___boxed(lean_object* v_assign_648_, lean_object* v_c_649_, lean_object* v_lit_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_648_, v_c_649_, v_lit_650_);
lean_dec_ref(v_lit_650_);
lean_dec_ref(v_c_649_);
return v_res_651_;
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
