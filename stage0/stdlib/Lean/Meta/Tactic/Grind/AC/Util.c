// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Util
// Imports: public import Lean.Meta.Tactic.Grind.AC.Types public import Lean.Meta.Tactic.Grind.ProveEq public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Simp
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
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`grind` internal error, invalid structure id"};
static const lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_AC_instMonadGetStructACM_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_ACM_getStruct___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructACM = (const lean_object*)&l_Lean_Meta_Grind_AC_instMonadGetStructACM_value;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value),LEAN_SCALAR_PTR_LITERAL(111, 233, 51, 226, 114, 128, 218, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value),LEAN_SCALAR_PTR_LITERAL(194, 164, 165, 74, 8, 252, 37, 122)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_expr_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1_value;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", neutral\?: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", idempotent: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ac"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(243, 114, 160, 105, 78, 163, 71, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", comm: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Associative"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(2, 251, 219, 24, 41, 141, 182, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Commutative"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(106, 96, 18, 51, 62, 235, 64, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "IdempotentOp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(245, 219, 239, 145, 216, 232, 46, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LawfulIdentity"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value),LEAN_SCALAR_PTR_LITERAL(50, 22, 200, 99, 71, 159, 239, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_Grind_AC_acExt;
x_5 = l_Lean_Meta_Grind_SolverExtension_getState___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_AC_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_Grind_AC_acExt;
x_5 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_AC_modify_x27___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Meta_Grind_AC_acExt;
x_14 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_13, x_1, x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_modify_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Meta_Grind_getConfig___redArg(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 6);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 3);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_nat_dec_le(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 6);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_nat_dec_le(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(x_1, x_3, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_AC_checkMaxSteps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 3, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0));
x_4 = l_Lean_Meta_Grind_AC_acExt;
x_5 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_4, x_3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_AC_incSteps___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_AC_incSteps___redArg(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_AC_incSteps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_12(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_ACM_run___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = lean_apply_12(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_AC_ACM_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_AC_getOpId___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_getOpId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_16);
lean_free_object(x_13);
x_19 = l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1;
x_20 = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(x_19, x_8, x_9, x_10, x_11);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_array_fget(x_16, x_1);
lean_dec_ref(x_16);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_23);
x_26 = l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1;
x_27 = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(x_26, x_8, x_9, x_10, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_array_fget(x_23, x_1);
lean_dec_ref(x_23);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_1, x_8);
if (x_9 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_10; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_3, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = lean_array_fget(x_4, x_1);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_4, x_1, x_16);
x_18 = lean_apply_1(x_2, x_15);
x_19 = lean_array_fset(x_17, x_1, x_18);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_20 = lean_array_fget(x_4, x_1);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_4, x_1, x_21);
x_23 = lean_apply_1(x_2, x_20);
x_24 = lean_array_fset(x_22, x_1, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Lean_Meta_Grind_AC_acExt;
x_7 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_6, x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_AC_modifyStruct___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_modifyStruct___redArg(x_1, x_2, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_modifyStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_getOp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(0);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(x_2, x_3, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38;
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36));
x_3 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_19; 
x_19 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*11 + 20);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_box(x_22);
lean_ctor_set(x_19, 0, x_54);
return x_19;
}
else
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_55; uint8_t x_56; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_19);
x_55 = lean_ctor_get(x_2, 0);
x_64 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11));
x_65 = lean_name_eq(x_55, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14));
x_67 = lean_name_eq(x_55, x_66);
x_56 = x_67;
goto block_63;
}
else
{
x_56 = x_65;
goto block_63;
}
block_63:
{
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2));
x_58 = lean_name_eq(x_55, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5));
x_60 = lean_name_eq(x_55, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8));
x_62 = lean_name_eq(x_55, x_61);
if (x_62 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
goto block_18;
}
else
{
goto block_53;
}
}
else
{
goto block_53;
}
}
else
{
goto block_53;
}
}
else
{
goto block_53;
}
}
}
else
{
uint8_t x_68; lean_object* x_69; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = 0;
x_69 = lean_box(x_68);
lean_ctor_set(x_19, 0, x_69);
return x_19;
}
}
block_36:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_free_object(x_26);
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_dec_ref(x_28);
if (x_23 == 0)
{
lean_free_object(x_26);
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_29; 
x_29 = lean_box(x_22);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_dec_ref(x_30);
if (x_23 == 0)
{
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_22);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
block_53:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_getAppNumArgs(x_1);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Expr_appFn_x21(x_1);
x_41 = l_Lean_Expr_appFn_x21(x_40);
lean_dec_ref(x_40);
x_42 = l_Lean_Expr_appArg_x21(x_41);
lean_dec_ref(x_41);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_42);
x_43 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
if (lean_obj_tag(x_45) == 0)
{
lean_free_object(x_43);
x_23 = x_39;
x_24 = lean_box(0);
x_25 = x_42;
goto block_36;
}
else
{
lean_dec_ref(x_45);
if (x_39 == 0)
{
lean_free_object(x_43);
x_23 = x_39;
x_24 = lean_box(0);
x_25 = x_42;
goto block_36;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_42);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_box(x_22);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
if (lean_obj_tag(x_47) == 0)
{
x_23 = x_39;
x_24 = lean_box(0);
x_25 = x_42;
goto block_36;
}
else
{
lean_dec_ref(x_47);
if (x_39 == 0)
{
x_23 = x_39;
x_24 = lean_box(0);
x_25 = x_42;
goto block_36;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_42);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_box(x_22);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_42);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
else
{
lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_19, 0);
lean_inc(x_70);
lean_dec(x_19);
x_71 = lean_ctor_get_uint8(x_70, sizeof(void*)*11 + 20);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_box(x_71);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
else
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_101; uint8_t x_102; lean_object* x_110; uint8_t x_111; 
x_101 = lean_ctor_get(x_2, 0);
x_110 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11));
x_111 = lean_name_eq(x_101, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14));
x_113 = lean_name_eq(x_101, x_112);
x_102 = x_113;
goto block_109;
}
else
{
x_102 = x_111;
goto block_109;
}
block_109:
{
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2));
x_104 = lean_name_eq(x_101, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5));
x_106 = lean_name_eq(x_101, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8));
x_108 = lean_name_eq(x_101, x_107);
if (x_108 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
goto block_18;
}
else
{
goto block_98;
}
}
else
{
goto block_98;
}
}
else
{
goto block_98;
}
}
else
{
goto block_98;
}
}
}
else
{
uint8_t x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = 0;
x_115 = lean_box(x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
block_83:
{
lean_object* x_75; 
x_75 = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_77);
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_dec_ref(x_76);
if (x_72 == 0)
{
lean_dec(x_77);
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(x_71);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
block_98:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = l_Lean_Expr_getAppNumArgs(x_1);
x_85 = lean_unsigned_to_nat(4u);
x_86 = lean_nat_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = l_Lean_Expr_appFn_x21(x_1);
x_88 = l_Lean_Expr_appFn_x21(x_87);
lean_dec_ref(x_87);
x_89 = l_Lean_Expr_appArg_x21(x_88);
lean_dec_ref(x_88);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_89);
x_90 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_obj_tag(x_91) == 0)
{
lean_dec(x_92);
x_72 = x_86;
x_73 = lean_box(0);
x_74 = x_89;
goto block_83;
}
else
{
lean_dec_ref(x_91);
if (x_86 == 0)
{
lean_dec(x_92);
x_72 = x_86;
x_73 = lean_box(0);
x_74 = x_89;
goto block_83;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_89);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_box(x_71);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_89);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_19);
if (x_117 == 0)
{
return x_19;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_19, 0);
lean_inc(x_118);
lean_dec(x_19);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
block_18:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_getTermOpIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_lt(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = lean_nat_dec_eq(x_1, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(x_1, x_5);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = lean_nat_dec_eq(x_1, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(x_1, x_5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(x_3, x_5);
x_7 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_1, x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(x_5, x_1, x_2);
lean_ctor_set(x_3, 2, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(x_9, x_1, x_2);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Meta_Grind_AC_acExt;
x_7 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_6, x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_AC_addTermOpId___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_addTermOpId___redArg(x_1, x_2, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_addTermOpId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 10);
x_6 = lean_ctor_get(x_3, 11);
lean_inc_ref(x_1);
x_7 = l_Lean_PersistentArray_push___redArg(x_5, x_1);
x_8 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_6, x_1, x_2);
lean_ctor_set(x_3, 11, x_8);
lean_ctor_set(x_3, 10, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get(x_3, 7);
x_17 = lean_ctor_get(x_3, 8);
x_18 = lean_ctor_get(x_3, 9);
x_19 = lean_ctor_get(x_3, 10);
x_20 = lean_ctor_get(x_3, 11);
x_21 = lean_ctor_get(x_3, 12);
x_22 = lean_ctor_get(x_3, 13);
x_23 = lean_ctor_get(x_3, 14);
x_24 = lean_ctor_get(x_3, 15);
x_25 = lean_ctor_get(x_3, 16);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc_ref(x_1);
x_27 = l_Lean_PersistentArray_push___redArg(x_19, x_1);
x_28 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_20, x_1, x_2);
x_29 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set(x_29, 2, x_11);
lean_ctor_set(x_29, 3, x_12);
lean_ctor_set(x_29, 4, x_13);
lean_ctor_set(x_29, 5, x_14);
lean_ctor_set(x_29, 6, x_15);
lean_ctor_set(x_29, 7, x_16);
lean_ctor_set(x_29, 8, x_17);
lean_ctor_set(x_29, 9, x_18);
lean_ctor_set(x_29, 10, x_27);
lean_ctor_set(x_29, 11, x_28);
lean_ctor_set(x_29, 12, x_21);
lean_ctor_set(x_29, 13, x_22);
lean_ctor_set(x_29, 14, x_23);
lean_ctor_set(x_29, 15, x_24);
lean_ctor_set(x_29, 16, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*17, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 10);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 11);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_18, x_1);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
lean_dec_ref(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_free_object(x_14);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
lean_dec_ref(x_17);
lean_inc(x_21);
lean_inc_ref(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_2);
x_23 = l_Lean_Meta_Grind_AC_modifyStruct___redArg(x_22, x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
lean_inc_ref(x_1);
x_24 = l_Lean_Meta_Grind_AC_addTermOpId___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_24);
x_25 = l_Lean_Meta_Grind_AC_acExt;
x_26 = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(x_25, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_ctor_get(x_39, 10);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_39, 11);
lean_inc_ref(x_41);
lean_dec(x_39);
x_42 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_41, x_1);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
x_45 = lean_ctor_get(x_40, 2);
lean_inc(x_45);
lean_dec_ref(x_40);
lean_inc(x_45);
lean_inc_ref(x_1);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_45);
lean_inc(x_2);
x_47 = l_Lean_Meta_Grind_AC_modifyStruct___redArg(x_46, x_2, x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec_ref(x_47);
lean_inc_ref(x_1);
x_48 = l_Lean_Meta_Grind_AC_addTermOpId___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = l_Lean_Meta_Grind_AC_acExt;
x_50 = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(x_49, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_51 = x_50;
} else {
 lean_dec_ref(x_50);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_45);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_60 = x_47;
} else {
 lean_dec_ref(x_47);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_14, 0);
lean_inc(x_63);
lean_dec(x_14);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_mkVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_instantiate_expr_mvars(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_st_ref_take(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_7);
x_12 = lean_st_ref_set(x_2, x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 2);
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2;
x_16 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4;
x_17 = lean_box(1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_4);
lean_ctor_set(x_19, 4, x_5);
lean_ctor_set(x_19, 5, x_6);
lean_ctor_set(x_19, 6, x_7);
lean_ctor_set(x_19, 7, x_8);
lean_ctor_set(x_19, 8, x_9);
lean_ctor_set(x_19, 9, x_14);
lean_ctor_set(x_19, 10, x_15);
lean_ctor_set(x_19, 11, x_16);
lean_ctor_set(x_19, 12, x_16);
lean_ctor_set(x_19, 13, x_15);
lean_ctor_set(x_19, 14, x_17);
lean_ctor_set(x_19, 15, x_18);
lean_ctor_set(x_19, 16, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*17, x_10);
x_20 = lean_array_push(x_13, x_19);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 2);
x_24 = lean_ctor_get(x_11, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2;
x_27 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4;
x_28 = lean_box(1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_4);
lean_ctor_set(x_30, 4, x_5);
lean_ctor_set(x_30, 5, x_6);
lean_ctor_set(x_30, 6, x_7);
lean_ctor_set(x_30, 7, x_8);
lean_ctor_set(x_30, 8, x_9);
lean_ctor_set(x_30, 9, x_25);
lean_ctor_set(x_30, 10, x_26);
lean_ctor_set(x_30, 11, x_27);
lean_ctor_set(x_30, 12, x_27);
lean_ctor_set(x_30, 13, x_26);
lean_ctor_set(x_30, 14, x_28);
lean_ctor_set(x_30, 15, x_29);
lean_ctor_set(x_30, 16, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*17, x_10);
x_31 = lean_array_push(x_21, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_24);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_10);
x_13 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_11);
return x_13;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_154 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_154) == 4)
{
lean_object* x_913; lean_object* x_914; uint8_t x_915; 
x_913 = lean_ctor_get(x_154, 0);
lean_inc(x_913);
x_914 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
x_915 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg(x_914, x_913);
lean_dec(x_913);
if (x_915 == 0)
{
x_155 = x_2;
x_156 = x_3;
x_157 = x_4;
x_158 = x_5;
x_159 = x_6;
x_160 = x_7;
x_161 = x_8;
x_162 = x_9;
x_163 = x_10;
x_164 = x_11;
x_165 = lean_box(0);
goto block_912;
}
else
{
lean_object* x_916; lean_object* x_917; 
lean_dec_ref(x_154);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_916 = lean_box(0);
x_917 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_917, 0, x_916);
return x_917;
}
}
else
{
x_155 = x_2;
x_156 = x_3;
x_157 = x_4;
x_158 = x_5;
x_159 = x_6;
x_160 = x_7;
x_161 = x_8;
x_162 = x_9;
x_163 = x_10;
x_164 = x_11;
x_165 = lean_box(0);
goto block_912;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_36:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec_ref(x_18);
lean_inc(x_19);
x_32 = l_Lean_Meta_Grind_AC_mkVar(x_31, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
x_13 = x_19;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_13 = x_19;
x_14 = lean_box(0);
goto block_17;
}
}
block_58:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(x_42, x_53, x_41, x_46, x_45, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_18 = x_47;
x_19 = x_39;
x_20 = x_50;
x_21 = x_51;
x_22 = x_38;
x_23 = x_37;
x_24 = x_44;
x_25 = x_40;
x_26 = x_41;
x_27 = x_46;
x_28 = x_45;
x_29 = x_48;
x_30 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_55; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
block_83:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_MessageData_ofFormat(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_80; 
x_80 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4;
x_37 = x_59;
x_38 = x_60;
x_39 = x_61;
x_40 = x_63;
x_41 = x_64;
x_42 = x_65;
x_43 = lean_box(0);
x_44 = x_67;
x_45 = x_68;
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_79;
x_50 = x_73;
x_51 = x_72;
x_52 = x_80;
goto block_58;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = l_Lean_MessageData_ofExpr(x_81);
x_37 = x_59;
x_38 = x_60;
x_39 = x_61;
x_40 = x_63;
x_41 = x_64;
x_42 = x_65;
x_43 = lean_box(0);
x_44 = x_67;
x_45 = x_68;
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_79;
x_50 = x_73;
x_51 = x_72;
x_52 = x_82;
goto block_58;
}
}
block_108:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_MessageData_ofFormat(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_106; 
x_106 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_105;
x_63 = x_87;
x_64 = x_88;
x_65 = x_89;
x_66 = lean_box(0);
x_67 = x_92;
x_68 = x_93;
x_69 = x_94;
x_70 = x_95;
x_71 = x_97;
x_72 = x_99;
x_73 = x_98;
x_74 = x_106;
goto block_83;
}
else
{
lean_object* x_107; 
lean_dec_ref(x_96);
x_107 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_105;
x_63 = x_87;
x_64 = x_88;
x_65 = x_89;
x_66 = lean_box(0);
x_67 = x_92;
x_68 = x_93;
x_69 = x_94;
x_70 = x_95;
x_71 = x_97;
x_72 = x_99;
x_73 = x_98;
x_74 = x_107;
goto block_83;
}
}
block_153:
{
lean_object* x_130; 
x_130 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_119, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_132);
lean_dec(x_131);
x_133 = lean_array_get_size(x_132);
lean_dec_ref(x_132);
x_134 = lean_box(x_113);
lean_inc(x_118);
lean_inc_ref(x_1);
x_135 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed), 11, 10);
lean_closure_set(x_135, 0, x_133);
lean_closure_set(x_135, 1, x_112);
lean_closure_set(x_135, 2, x_110);
lean_closure_set(x_135, 3, x_1);
lean_closure_set(x_135, 4, x_118);
lean_closure_set(x_135, 5, x_114);
lean_closure_set(x_135, 6, x_109);
lean_closure_set(x_135, 7, x_111);
lean_closure_set(x_135, 8, x_117);
lean_closure_set(x_135, 9, x_134);
x_136 = l_Lean_Meta_Grind_AC_acExt;
x_137 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_136, x_135, x_119);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec_ref(x_137);
x_138 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
x_139 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(x_138, x_127);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec_ref(x_1);
x_18 = x_118;
x_19 = x_133;
x_20 = x_119;
x_21 = x_120;
x_22 = x_121;
x_23 = x_122;
x_24 = x_123;
x_25 = x_124;
x_26 = x_125;
x_27 = x_126;
x_28 = x_127;
x_29 = x_128;
x_30 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = l_Lean_MessageData_ofExpr(x_1);
x_143 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_145; 
x_145 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
x_84 = x_122;
x_85 = x_121;
x_86 = x_133;
x_87 = x_124;
x_88 = x_125;
x_89 = x_138;
x_90 = x_144;
x_91 = lean_box(0);
x_92 = x_123;
x_93 = x_127;
x_94 = x_126;
x_95 = x_118;
x_96 = x_115;
x_97 = x_128;
x_98 = x_119;
x_99 = x_120;
x_100 = x_145;
goto block_108;
}
else
{
lean_object* x_146; 
lean_dec_ref(x_116);
x_146 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
x_84 = x_122;
x_85 = x_121;
x_86 = x_133;
x_87 = x_124;
x_88 = x_125;
x_89 = x_138;
x_90 = x_144;
x_91 = lean_box(0);
x_92 = x_123;
x_93 = x_127;
x_94 = x_126;
x_95 = x_118;
x_96 = x_115;
x_97 = x_128;
x_98 = x_119;
x_99 = x_120;
x_100 = x_146;
goto block_108;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec_ref(x_1);
x_147 = !lean_is_exclusive(x_137);
if (x_147 == 0)
{
return x_137;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_137, 0);
lean_inc(x_148);
lean_dec(x_137);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_150 = !lean_is_exclusive(x_130);
if (x_150 == 0)
{
return x_130;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_130, 0);
lean_inc(x_151);
lean_dec(x_130);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
block_912:
{
lean_object* x_166; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_1);
x_166 = lean_infer_type(x_1, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_168 = lean_whnf(x_167, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_168, 0);
if (lean_obj_tag(x_170) == 7)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_170, 2);
lean_inc_ref(x_172);
lean_dec_ref(x_170);
x_173 = l_Lean_Expr_hasLooseBVars(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_free_object(x_168);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_174 = lean_whnf(x_172, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_174, 0);
if (lean_obj_tag(x_176) == 7)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_176, 2);
lean_inc_ref(x_178);
lean_dec_ref(x_176);
x_179 = l_Lean_Expr_hasLooseBVars(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_free_object(x_174);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_180 = l_Lean_Meta_isExprDefEq(x_171, x_177, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec_ref(x_178);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_184 = lean_box(0);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; 
lean_free_object(x_180);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_185 = l_Lean_Meta_isExprDefEq(x_171, x_178, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_189 = lean_box(0);
lean_ctor_set(x_185, 0, x_189);
return x_185;
}
else
{
lean_object* x_190; 
lean_free_object(x_185);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_190 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
lean_dec_ref(x_154);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_unbox(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_free_object(x_190);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_194 = l_Lean_Meta_getLevel(x_171, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18));
x_197 = lean_box(0);
lean_inc(x_195);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
lean_inc_ref(x_198);
x_199 = l_Lean_mkConst(x_196, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_200 = l_Lean_mkAppB(x_199, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_201 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_200, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_201, 0);
if (lean_obj_tag(x_203) == 1)
{
uint8_t x_204; 
lean_free_object(x_201);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_198);
x_207 = l_Lean_mkConst(x_206, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_208 = l_Lean_mkAppB(x_207, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_209 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_208, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_198);
x_212 = l_Lean_mkConst(x_211, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_213 = l_Lean_mkAppB(x_212, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_214 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_213, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
lean_inc_ref(x_171);
lean_ctor_set(x_203, 0, x_171);
x_216 = 0;
x_217 = lean_box(0);
lean_inc_ref(x_161);
x_218 = l_Lean_Meta_mkFreshExprMVar(x_203, x_216, x_217, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_221 = l_Lean_mkConst(x_220, x_198);
lean_inc(x_219);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_222 = l_Lean_mkApp3(x_221, x_171, x_1, x_219);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_223 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_222, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
if (lean_obj_tag(x_224) == 1)
{
lean_object* x_225; uint8_t x_226; 
x_225 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_219, x_162);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_228 = l_Lean_Meta_Grind_preprocessLight(x_227, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
x_230 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_229);
x_233 = lean_grind_internalize(x_229, x_231, x_232, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
lean_dec_ref(x_233);
lean_ctor_set_tag(x_225, 1);
lean_ctor_set(x_225, 0, x_229);
x_234 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_210);
lean_inc(x_215);
x_109 = x_215;
x_110 = x_195;
x_111 = x_210;
x_112 = x_171;
x_113 = x_234;
x_114 = x_205;
x_115 = x_215;
x_116 = x_210;
x_117 = x_224;
x_118 = x_225;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
uint8_t x_235; 
lean_dec(x_229);
lean_free_object(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_235 = !lean_is_exclusive(x_233);
if (x_235 == 0)
{
return x_233;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_229);
lean_free_object(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_238 = !lean_is_exclusive(x_230);
if (x_238 == 0)
{
return x_230;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_230, 0);
lean_inc(x_239);
lean_dec(x_230);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_free_object(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_241 = !lean_is_exclusive(x_228);
if (x_241 == 0)
{
return x_228;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_228, 0);
lean_inc(x_242);
lean_dec(x_228);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_225, 0);
lean_inc(x_244);
lean_dec(x_225);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_245 = l_Lean_Meta_Grind_preprocessLight(x_244, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
x_249 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_246);
x_250 = lean_grind_internalize(x_246, x_248, x_249, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; uint8_t x_252; 
lean_dec_ref(x_250);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_246);
x_252 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_210);
lean_inc(x_215);
x_109 = x_215;
x_110 = x_195;
x_111 = x_210;
x_112 = x_171;
x_113 = x_252;
x_114 = x_205;
x_115 = x_215;
x_116 = x_210;
x_117 = x_224;
x_118 = x_251;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_246);
lean_dec_ref(x_224);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_253 = lean_ctor_get(x_250, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_254 = x_250;
} else {
 lean_dec_ref(x_250);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_246);
lean_dec_ref(x_224);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_256 = lean_ctor_get(x_247, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 x_257 = x_247;
} else {
 lean_dec_ref(x_247);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec_ref(x_224);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_259 = lean_ctor_get(x_245, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_260 = x_245;
} else {
 lean_dec_ref(x_245);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
return x_261;
}
}
}
else
{
lean_object* x_262; uint8_t x_263; 
lean_dec(x_224);
lean_dec(x_219);
x_262 = lean_box(0);
x_263 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_210);
lean_inc(x_215);
x_109 = x_215;
x_110 = x_195;
x_111 = x_210;
x_112 = x_171;
x_113 = x_263;
x_114 = x_205;
x_115 = x_215;
x_116 = x_210;
x_117 = x_262;
x_118 = x_262;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
uint8_t x_264; 
lean_dec(x_219);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_264 = !lean_is_exclusive(x_223);
if (x_264 == 0)
{
return x_223;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_223, 0);
lean_inc(x_265);
lean_dec(x_223);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_267 = !lean_is_exclusive(x_218);
if (x_267 == 0)
{
return x_218;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_218, 0);
lean_inc(x_268);
lean_dec(x_218);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_210);
lean_free_object(x_203);
lean_dec(x_205);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_270 = !lean_is_exclusive(x_214);
if (x_270 == 0)
{
return x_214;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_214, 0);
lean_inc(x_271);
lean_dec(x_214);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_free_object(x_203);
lean_dec(x_205);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_273 = !lean_is_exclusive(x_209);
if (x_273 == 0)
{
return x_209;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_209, 0);
lean_inc(x_274);
lean_dec(x_209);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_203, 0);
lean_inc(x_276);
lean_dec(x_203);
x_277 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_198);
x_278 = l_Lean_mkConst(x_277, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_279 = l_Lean_mkAppB(x_278, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_280 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_279, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_198);
x_283 = l_Lean_mkConst(x_282, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_284 = l_Lean_mkAppB(x_283, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_285 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_284, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
lean_dec_ref(x_285);
lean_inc_ref(x_171);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_171);
x_288 = 0;
x_289 = lean_box(0);
lean_inc_ref(x_161);
x_290 = l_Lean_Meta_mkFreshExprMVar(x_287, x_288, x_289, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
x_292 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_293 = l_Lean_mkConst(x_292, x_198);
lean_inc(x_291);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_294 = l_Lean_mkApp3(x_293, x_171, x_1, x_291);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_295 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_294, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
if (lean_obj_tag(x_296) == 1)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_291, x_162);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_300 = l_Lean_Meta_Grind_preprocessLight(x_298, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
lean_dec_ref(x_300);
x_302 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec_ref(x_302);
x_304 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_301);
x_305 = lean_grind_internalize(x_301, x_303, x_304, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; uint8_t x_307; 
lean_dec_ref(x_305);
if (lean_is_scalar(x_299)) {
 x_306 = lean_alloc_ctor(1, 1, 0);
} else {
 x_306 = x_299;
 lean_ctor_set_tag(x_306, 1);
}
lean_ctor_set(x_306, 0, x_301);
x_307 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_281);
lean_inc(x_286);
x_109 = x_286;
x_110 = x_195;
x_111 = x_281;
x_112 = x_171;
x_113 = x_307;
x_114 = x_276;
x_115 = x_286;
x_116 = x_281;
x_117 = x_296;
x_118 = x_306;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_301);
lean_dec(x_299);
lean_dec_ref(x_296);
lean_dec(x_286);
lean_dec(x_281);
lean_dec(x_276);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_308 = lean_ctor_get(x_305, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_309 = x_305;
} else {
 lean_dec_ref(x_305);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_301);
lean_dec(x_299);
lean_dec_ref(x_296);
lean_dec(x_286);
lean_dec(x_281);
lean_dec(x_276);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_302, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 x_312 = x_302;
} else {
 lean_dec_ref(x_302);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_299);
lean_dec_ref(x_296);
lean_dec(x_286);
lean_dec(x_281);
lean_dec(x_276);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_314 = lean_ctor_get(x_300, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 x_315 = x_300;
} else {
 lean_dec_ref(x_300);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_314);
return x_316;
}
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_296);
lean_dec(x_291);
x_317 = lean_box(0);
x_318 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_281);
lean_inc(x_286);
x_109 = x_286;
x_110 = x_195;
x_111 = x_281;
x_112 = x_171;
x_113 = x_318;
x_114 = x_276;
x_115 = x_286;
x_116 = x_281;
x_117 = x_317;
x_118 = x_317;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_291);
lean_dec(x_286);
lean_dec(x_281);
lean_dec(x_276);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_319 = lean_ctor_get(x_295, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_320 = x_295;
} else {
 lean_dec_ref(x_295);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_286);
lean_dec(x_281);
lean_dec(x_276);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_322 = lean_ctor_get(x_290, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 x_323 = x_290;
} else {
 lean_dec_ref(x_290);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 1, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_281);
lean_dec(x_276);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_325 = lean_ctor_get(x_285, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_326 = x_285;
} else {
 lean_dec_ref(x_285);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 1, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_276);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_328 = lean_ctor_get(x_280, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_329 = x_280;
} else {
 lean_dec_ref(x_280);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_328);
return x_330;
}
}
}
else
{
lean_object* x_331; 
lean_dec(x_203);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_331 = lean_box(0);
lean_ctor_set(x_201, 0, x_331);
return x_201;
}
}
else
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_201, 0);
lean_inc(x_332);
lean_dec(x_201);
if (lean_obj_tag(x_332) == 1)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_334 = x_332;
} else {
 lean_dec_ref(x_332);
 x_334 = lean_box(0);
}
x_335 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_198);
x_336 = l_Lean_mkConst(x_335, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_337 = l_Lean_mkAppB(x_336, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_338 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_337, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_198);
x_341 = l_Lean_mkConst(x_340, x_198);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_342 = l_Lean_mkAppB(x_341, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_343 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_342, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
lean_inc_ref(x_171);
if (lean_is_scalar(x_334)) {
 x_345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_345 = x_334;
}
lean_ctor_set(x_345, 0, x_171);
x_346 = 0;
x_347 = lean_box(0);
lean_inc_ref(x_161);
x_348 = l_Lean_Meta_mkFreshExprMVar(x_345, x_346, x_347, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_351 = l_Lean_mkConst(x_350, x_198);
lean_inc(x_349);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_352 = l_Lean_mkApp3(x_351, x_171, x_1, x_349);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_353 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_352, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
lean_dec_ref(x_353);
if (lean_obj_tag(x_354) == 1)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_349, x_162);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_358 = l_Lean_Meta_Grind_preprocessLight(x_356, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
lean_dec_ref(x_360);
x_362 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_359);
x_363 = lean_grind_internalize(x_359, x_361, x_362, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; uint8_t x_365; 
lean_dec_ref(x_363);
if (lean_is_scalar(x_357)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_357;
 lean_ctor_set_tag(x_364, 1);
}
lean_ctor_set(x_364, 0, x_359);
x_365 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_339);
lean_inc(x_344);
x_109 = x_344;
x_110 = x_195;
x_111 = x_339;
x_112 = x_171;
x_113 = x_365;
x_114 = x_333;
x_115 = x_344;
x_116 = x_339;
x_117 = x_354;
x_118 = x_364;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_354);
lean_dec(x_344);
lean_dec(x_339);
lean_dec(x_333);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_366 = lean_ctor_get(x_363, 0);
lean_inc(x_366);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_367 = x_363;
} else {
 lean_dec_ref(x_363);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 1, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_366);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_354);
lean_dec(x_344);
lean_dec(x_339);
lean_dec(x_333);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_369 = lean_ctor_get(x_360, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_370 = x_360;
} else {
 lean_dec_ref(x_360);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_369);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_357);
lean_dec_ref(x_354);
lean_dec(x_344);
lean_dec(x_339);
lean_dec(x_333);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_372 = lean_ctor_get(x_358, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_373 = x_358;
} else {
 lean_dec_ref(x_358);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 1, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_372);
return x_374;
}
}
else
{
lean_object* x_375; uint8_t x_376; 
lean_dec(x_354);
lean_dec(x_349);
x_375 = lean_box(0);
x_376 = lean_unbox(x_192);
lean_dec(x_192);
lean_inc(x_339);
lean_inc(x_344);
x_109 = x_344;
x_110 = x_195;
x_111 = x_339;
x_112 = x_171;
x_113 = x_376;
x_114 = x_333;
x_115 = x_344;
x_116 = x_339;
x_117 = x_375;
x_118 = x_375;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_349);
lean_dec(x_344);
lean_dec(x_339);
lean_dec(x_333);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_377 = lean_ctor_get(x_353, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_378 = x_353;
} else {
 lean_dec_ref(x_353);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_344);
lean_dec(x_339);
lean_dec(x_333);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_380 = lean_ctor_get(x_348, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 x_381 = x_348;
} else {
 lean_dec_ref(x_348);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 1, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_380);
return x_382;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_339);
lean_dec(x_334);
lean_dec(x_333);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_383 = lean_ctor_get(x_343, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_384 = x_343;
} else {
 lean_dec_ref(x_343);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_334);
lean_dec(x_333);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_386 = lean_ctor_get(x_338, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_387 = x_338;
} else {
 lean_dec_ref(x_338);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_332);
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_389 = lean_box(0);
x_390 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_390, 0, x_389);
return x_390;
}
}
}
else
{
uint8_t x_391; 
lean_dec_ref(x_198);
lean_dec(x_195);
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_391 = !lean_is_exclusive(x_201);
if (x_391 == 0)
{
return x_201;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_201, 0);
lean_inc(x_392);
lean_dec(x_201);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_392);
return x_393;
}
}
}
else
{
uint8_t x_394; 
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_394 = !lean_is_exclusive(x_194);
if (x_394 == 0)
{
return x_194;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_194, 0);
lean_inc(x_395);
lean_dec(x_194);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
return x_396;
}
}
}
else
{
lean_object* x_397; 
lean_dec(x_192);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_397 = lean_box(0);
lean_ctor_set(x_190, 0, x_397);
return x_190;
}
}
else
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_ctor_get(x_190, 0);
lean_inc(x_398);
lean_dec(x_190);
x_399 = lean_unbox(x_398);
if (x_399 == 0)
{
lean_object* x_400; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_400 = l_Lean_Meta_getLevel(x_171, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_402 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18));
x_403 = lean_box(0);
lean_inc(x_401);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_403);
lean_inc_ref(x_404);
x_405 = l_Lean_mkConst(x_402, x_404);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_406 = l_Lean_mkAppB(x_405, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_407 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_406, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_409 = x_407;
} else {
 lean_dec_ref(x_407);
 x_409 = lean_box(0);
}
if (lean_obj_tag(x_408) == 1)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_409);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_411 = x_408;
} else {
 lean_dec_ref(x_408);
 x_411 = lean_box(0);
}
x_412 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_404);
x_413 = l_Lean_mkConst(x_412, x_404);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_414 = l_Lean_mkAppB(x_413, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_415 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_414, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
lean_dec_ref(x_415);
x_417 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_404);
x_418 = l_Lean_mkConst(x_417, x_404);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_419 = l_Lean_mkAppB(x_418, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_420 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_419, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; lean_object* x_425; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec_ref(x_420);
lean_inc_ref(x_171);
if (lean_is_scalar(x_411)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_411;
}
lean_ctor_set(x_422, 0, x_171);
x_423 = 0;
x_424 = lean_box(0);
lean_inc_ref(x_161);
x_425 = l_Lean_Meta_mkFreshExprMVar(x_422, x_423, x_424, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec_ref(x_425);
x_427 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_428 = l_Lean_mkConst(x_427, x_404);
lean_inc(x_426);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_429 = l_Lean_mkApp3(x_428, x_171, x_1, x_426);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_430 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_429, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
if (lean_obj_tag(x_431) == 1)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_426, x_162);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 x_434 = x_432;
} else {
 lean_dec_ref(x_432);
 x_434 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_435 = l_Lean_Meta_Grind_preprocessLight(x_433, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec_ref(x_435);
x_437 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
lean_dec_ref(x_437);
x_439 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_436);
x_440 = lean_grind_internalize(x_436, x_438, x_439, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; uint8_t x_442; 
lean_dec_ref(x_440);
if (lean_is_scalar(x_434)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_434;
 lean_ctor_set_tag(x_441, 1);
}
lean_ctor_set(x_441, 0, x_436);
x_442 = lean_unbox(x_398);
lean_dec(x_398);
lean_inc(x_416);
lean_inc(x_421);
x_109 = x_421;
x_110 = x_401;
x_111 = x_416;
x_112 = x_171;
x_113 = x_442;
x_114 = x_410;
x_115 = x_421;
x_116 = x_416;
x_117 = x_431;
x_118 = x_441;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_436);
lean_dec(x_434);
lean_dec_ref(x_431);
lean_dec(x_421);
lean_dec(x_416);
lean_dec(x_410);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_444 = x_440;
} else {
 lean_dec_ref(x_440);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 1, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_436);
lean_dec(x_434);
lean_dec_ref(x_431);
lean_dec(x_421);
lean_dec(x_416);
lean_dec(x_410);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_446 = lean_ctor_get(x_437, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_447 = x_437;
} else {
 lean_dec_ref(x_437);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 1, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_446);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_434);
lean_dec_ref(x_431);
lean_dec(x_421);
lean_dec(x_416);
lean_dec(x_410);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_449 = lean_ctor_get(x_435, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_450 = x_435;
} else {
 lean_dec_ref(x_435);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
}
else
{
lean_object* x_452; uint8_t x_453; 
lean_dec(x_431);
lean_dec(x_426);
x_452 = lean_box(0);
x_453 = lean_unbox(x_398);
lean_dec(x_398);
lean_inc(x_416);
lean_inc(x_421);
x_109 = x_421;
x_110 = x_401;
x_111 = x_416;
x_112 = x_171;
x_113 = x_453;
x_114 = x_410;
x_115 = x_421;
x_116 = x_416;
x_117 = x_452;
x_118 = x_452;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_426);
lean_dec(x_421);
lean_dec(x_416);
lean_dec(x_410);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_454 = lean_ctor_get(x_430, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_455 = x_430;
} else {
 lean_dec_ref(x_430);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 1, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_454);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_421);
lean_dec(x_416);
lean_dec(x_410);
lean_dec_ref(x_404);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_425, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_458 = x_425;
} else {
 lean_dec_ref(x_425);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 1, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_457);
return x_459;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_416);
lean_dec(x_411);
lean_dec(x_410);
lean_dec_ref(x_404);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_460 = lean_ctor_get(x_420, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_461 = x_420;
} else {
 lean_dec_ref(x_420);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_460);
return x_462;
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_411);
lean_dec(x_410);
lean_dec_ref(x_404);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_463 = lean_ctor_get(x_415, 0);
lean_inc(x_463);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_464 = x_415;
} else {
 lean_dec_ref(x_415);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 1, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_463);
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_408);
lean_dec_ref(x_404);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_466 = lean_box(0);
if (lean_is_scalar(x_409)) {
 x_467 = lean_alloc_ctor(0, 1, 0);
} else {
 x_467 = x_409;
}
lean_ctor_set(x_467, 0, x_466);
return x_467;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec_ref(x_404);
lean_dec(x_401);
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_468 = lean_ctor_get(x_407, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_469 = x_407;
} else {
 lean_dec_ref(x_407);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 1, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_468);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_400, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_472 = x_400;
} else {
 lean_dec_ref(x_400);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_471);
return x_473;
}
}
else
{
lean_object* x_474; lean_object* x_475; 
lean_dec(x_398);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_474 = lean_box(0);
x_475 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_475, 0, x_474);
return x_475;
}
}
}
else
{
uint8_t x_476; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_476 = !lean_is_exclusive(x_190);
if (x_476 == 0)
{
return x_190;
}
else
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_190, 0);
lean_inc(x_477);
lean_dec(x_190);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
return x_478;
}
}
}
}
else
{
lean_object* x_479; uint8_t x_480; 
x_479 = lean_ctor_get(x_185, 0);
lean_inc(x_479);
lean_dec(x_185);
x_480 = lean_unbox(x_479);
lean_dec(x_479);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_481 = lean_box(0);
x_482 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_482, 0, x_481);
return x_482;
}
else
{
lean_object* x_483; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_483 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
lean_dec_ref(x_154);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 x_485 = x_483;
} else {
 lean_dec_ref(x_483);
 x_485 = lean_box(0);
}
x_486 = lean_unbox(x_484);
if (x_486 == 0)
{
lean_object* x_487; 
lean_dec(x_485);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_487 = l_Lean_Meta_getLevel(x_171, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
lean_dec_ref(x_487);
x_489 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18));
x_490 = lean_box(0);
lean_inc(x_488);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_490);
lean_inc_ref(x_491);
x_492 = l_Lean_mkConst(x_489, x_491);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_493 = l_Lean_mkAppB(x_492, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_494 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_493, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
if (lean_obj_tag(x_495) == 1)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_496);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
x_499 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_491);
x_500 = l_Lean_mkConst(x_499, x_491);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_501 = l_Lean_mkAppB(x_500, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_502 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_501, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
lean_dec_ref(x_502);
x_504 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_491);
x_505 = l_Lean_mkConst(x_504, x_491);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_506 = l_Lean_mkAppB(x_505, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_507 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_506, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; uint8_t x_510; lean_object* x_511; lean_object* x_512; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec_ref(x_507);
lean_inc_ref(x_171);
if (lean_is_scalar(x_498)) {
 x_509 = lean_alloc_ctor(1, 1, 0);
} else {
 x_509 = x_498;
}
lean_ctor_set(x_509, 0, x_171);
x_510 = 0;
x_511 = lean_box(0);
lean_inc_ref(x_161);
x_512 = l_Lean_Meta_mkFreshExprMVar(x_509, x_510, x_511, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec_ref(x_512);
x_514 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_515 = l_Lean_mkConst(x_514, x_491);
lean_inc(x_513);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_516 = l_Lean_mkApp3(x_515, x_171, x_1, x_513);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_517 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_516, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
lean_dec_ref(x_517);
if (lean_obj_tag(x_518) == 1)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_519 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_513, x_162);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_521 = x_519;
} else {
 lean_dec_ref(x_519);
 x_521 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_522 = l_Lean_Meta_Grind_preprocessLight(x_520, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
lean_dec_ref(x_522);
x_524 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
lean_dec_ref(x_524);
x_526 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_523);
x_527 = lean_grind_internalize(x_523, x_525, x_526, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; uint8_t x_529; 
lean_dec_ref(x_527);
if (lean_is_scalar(x_521)) {
 x_528 = lean_alloc_ctor(1, 1, 0);
} else {
 x_528 = x_521;
 lean_ctor_set_tag(x_528, 1);
}
lean_ctor_set(x_528, 0, x_523);
x_529 = lean_unbox(x_484);
lean_dec(x_484);
lean_inc(x_503);
lean_inc(x_508);
x_109 = x_508;
x_110 = x_488;
x_111 = x_503;
x_112 = x_171;
x_113 = x_529;
x_114 = x_497;
x_115 = x_508;
x_116 = x_503;
x_117 = x_518;
x_118 = x_528;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec_ref(x_518);
lean_dec(x_508);
lean_dec(x_503);
lean_dec(x_497);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_530 = lean_ctor_get(x_527, 0);
lean_inc(x_530);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 x_531 = x_527;
} else {
 lean_dec_ref(x_527);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 1, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_530);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec_ref(x_518);
lean_dec(x_508);
lean_dec(x_503);
lean_dec(x_497);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_533 = lean_ctor_get(x_524, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 x_534 = x_524;
} else {
 lean_dec_ref(x_524);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_521);
lean_dec_ref(x_518);
lean_dec(x_508);
lean_dec(x_503);
lean_dec(x_497);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_536 = lean_ctor_get(x_522, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 x_537 = x_522;
} else {
 lean_dec_ref(x_522);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 1, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_536);
return x_538;
}
}
else
{
lean_object* x_539; uint8_t x_540; 
lean_dec(x_518);
lean_dec(x_513);
x_539 = lean_box(0);
x_540 = lean_unbox(x_484);
lean_dec(x_484);
lean_inc(x_503);
lean_inc(x_508);
x_109 = x_508;
x_110 = x_488;
x_111 = x_503;
x_112 = x_171;
x_113 = x_540;
x_114 = x_497;
x_115 = x_508;
x_116 = x_503;
x_117 = x_539;
x_118 = x_539;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_513);
lean_dec(x_508);
lean_dec(x_503);
lean_dec(x_497);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_541 = lean_ctor_get(x_517, 0);
lean_inc(x_541);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 x_542 = x_517;
} else {
 lean_dec_ref(x_517);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 1, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_541);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_508);
lean_dec(x_503);
lean_dec(x_497);
lean_dec_ref(x_491);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_544 = lean_ctor_get(x_512, 0);
lean_inc(x_544);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 x_545 = x_512;
} else {
 lean_dec_ref(x_512);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(1, 1, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_544);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_503);
lean_dec(x_498);
lean_dec(x_497);
lean_dec_ref(x_491);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_547 = lean_ctor_get(x_507, 0);
lean_inc(x_547);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_548 = x_507;
} else {
 lean_dec_ref(x_507);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 1, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_547);
return x_549;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_498);
lean_dec(x_497);
lean_dec_ref(x_491);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_550 = lean_ctor_get(x_502, 0);
lean_inc(x_550);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 x_551 = x_502;
} else {
 lean_dec_ref(x_502);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 1, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_550);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; 
lean_dec(x_495);
lean_dec_ref(x_491);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_553 = lean_box(0);
if (lean_is_scalar(x_496)) {
 x_554 = lean_alloc_ctor(0, 1, 0);
} else {
 x_554 = x_496;
}
lean_ctor_set(x_554, 0, x_553);
return x_554;
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec_ref(x_491);
lean_dec(x_488);
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_555 = lean_ctor_get(x_494, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_556 = x_494;
} else {
 lean_dec_ref(x_494);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 1, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_555);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_558 = lean_ctor_get(x_487, 0);
lean_inc(x_558);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 x_559 = x_487;
} else {
 lean_dec_ref(x_487);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 1, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_558);
return x_560;
}
}
else
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_484);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_561 = lean_box(0);
if (lean_is_scalar(x_485)) {
 x_562 = lean_alloc_ctor(0, 1, 0);
} else {
 x_562 = x_485;
}
lean_ctor_set(x_562, 0, x_561);
return x_562;
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_563 = lean_ctor_get(x_483, 0);
lean_inc(x_563);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 x_564 = x_483;
} else {
 lean_dec_ref(x_483);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 1, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_563);
return x_565;
}
}
}
}
else
{
uint8_t x_566; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_566 = !lean_is_exclusive(x_185);
if (x_566 == 0)
{
return x_185;
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_185, 0);
lean_inc(x_567);
lean_dec(x_185);
x_568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_568, 0, x_567);
return x_568;
}
}
}
}
else
{
lean_object* x_569; uint8_t x_570; 
x_569 = lean_ctor_get(x_180, 0);
lean_inc(x_569);
lean_dec(x_180);
x_570 = lean_unbox(x_569);
lean_dec(x_569);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
lean_dec_ref(x_178);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_571 = lean_box(0);
x_572 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_572, 0, x_571);
return x_572;
}
else
{
lean_object* x_573; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_573 = l_Lean_Meta_isExprDefEq(x_171, x_178, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_575 = x_573;
} else {
 lean_dec_ref(x_573);
 x_575 = lean_box(0);
}
x_576 = lean_unbox(x_574);
lean_dec(x_574);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_577 = lean_box(0);
if (lean_is_scalar(x_575)) {
 x_578 = lean_alloc_ctor(0, 1, 0);
} else {
 x_578 = x_575;
}
lean_ctor_set(x_578, 0, x_577);
return x_578;
}
else
{
lean_object* x_579; 
lean_dec(x_575);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_579 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
lean_dec_ref(x_154);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; uint8_t x_582; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_581 = x_579;
} else {
 lean_dec_ref(x_579);
 x_581 = lean_box(0);
}
x_582 = lean_unbox(x_580);
if (x_582 == 0)
{
lean_object* x_583; 
lean_dec(x_581);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_583 = l_Lean_Meta_getLevel(x_171, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec_ref(x_583);
x_585 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18));
x_586 = lean_box(0);
lean_inc(x_584);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_584);
lean_ctor_set(x_587, 1, x_586);
lean_inc_ref(x_587);
x_588 = l_Lean_mkConst(x_585, x_587);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_589 = l_Lean_mkAppB(x_588, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_590 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_589, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_592 = x_590;
} else {
 lean_dec_ref(x_590);
 x_592 = lean_box(0);
}
if (lean_obj_tag(x_591) == 1)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_592);
x_593 = lean_ctor_get(x_591, 0);
lean_inc(x_593);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 x_594 = x_591;
} else {
 lean_dec_ref(x_591);
 x_594 = lean_box(0);
}
x_595 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_587);
x_596 = l_Lean_mkConst(x_595, x_587);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_597 = l_Lean_mkAppB(x_596, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_598 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_597, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
lean_dec_ref(x_598);
x_600 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_587);
x_601 = l_Lean_mkConst(x_600, x_587);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_602 = l_Lean_mkAppB(x_601, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_603 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_602, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
lean_dec_ref(x_603);
lean_inc_ref(x_171);
if (lean_is_scalar(x_594)) {
 x_605 = lean_alloc_ctor(1, 1, 0);
} else {
 x_605 = x_594;
}
lean_ctor_set(x_605, 0, x_171);
x_606 = 0;
x_607 = lean_box(0);
lean_inc_ref(x_161);
x_608 = l_Lean_Meta_mkFreshExprMVar(x_605, x_606, x_607, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
lean_dec_ref(x_608);
x_610 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_611 = l_Lean_mkConst(x_610, x_587);
lean_inc(x_609);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_612 = l_Lean_mkApp3(x_611, x_171, x_1, x_609);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_613 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_612, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
lean_dec_ref(x_613);
if (lean_obj_tag(x_614) == 1)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_615 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_609, x_162);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 x_617 = x_615;
} else {
 lean_dec_ref(x_615);
 x_617 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_618 = l_Lean_Meta_Grind_preprocessLight(x_616, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
lean_dec_ref(x_618);
x_620 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
lean_dec_ref(x_620);
x_622 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_619);
x_623 = lean_grind_internalize(x_619, x_621, x_622, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; uint8_t x_625; 
lean_dec_ref(x_623);
if (lean_is_scalar(x_617)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_617;
 lean_ctor_set_tag(x_624, 1);
}
lean_ctor_set(x_624, 0, x_619);
x_625 = lean_unbox(x_580);
lean_dec(x_580);
lean_inc(x_599);
lean_inc(x_604);
x_109 = x_604;
x_110 = x_584;
x_111 = x_599;
x_112 = x_171;
x_113 = x_625;
x_114 = x_593;
x_115 = x_604;
x_116 = x_599;
x_117 = x_614;
x_118 = x_624;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_619);
lean_dec(x_617);
lean_dec_ref(x_614);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_593);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_626 = lean_ctor_get(x_623, 0);
lean_inc(x_626);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 x_627 = x_623;
} else {
 lean_dec_ref(x_623);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_626);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_619);
lean_dec(x_617);
lean_dec_ref(x_614);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_593);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_629 = lean_ctor_get(x_620, 0);
lean_inc(x_629);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 x_630 = x_620;
} else {
 lean_dec_ref(x_620);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 1, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_629);
return x_631;
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_617);
lean_dec_ref(x_614);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_593);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_632 = lean_ctor_get(x_618, 0);
lean_inc(x_632);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 x_633 = x_618;
} else {
 lean_dec_ref(x_618);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 1, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_632);
return x_634;
}
}
else
{
lean_object* x_635; uint8_t x_636; 
lean_dec(x_614);
lean_dec(x_609);
x_635 = lean_box(0);
x_636 = lean_unbox(x_580);
lean_dec(x_580);
lean_inc(x_599);
lean_inc(x_604);
x_109 = x_604;
x_110 = x_584;
x_111 = x_599;
x_112 = x_171;
x_113 = x_636;
x_114 = x_593;
x_115 = x_604;
x_116 = x_599;
x_117 = x_635;
x_118 = x_635;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_609);
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_593);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_637 = lean_ctor_get(x_613, 0);
lean_inc(x_637);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 x_638 = x_613;
} else {
 lean_dec_ref(x_613);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_604);
lean_dec(x_599);
lean_dec(x_593);
lean_dec_ref(x_587);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_640 = lean_ctor_get(x_608, 0);
lean_inc(x_640);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 x_641 = x_608;
} else {
 lean_dec_ref(x_608);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 1, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_640);
return x_642;
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_599);
lean_dec(x_594);
lean_dec(x_593);
lean_dec_ref(x_587);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_643 = lean_ctor_get(x_603, 0);
lean_inc(x_643);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_644 = x_603;
} else {
 lean_dec_ref(x_603);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 1, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_643);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_594);
lean_dec(x_593);
lean_dec_ref(x_587);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_646 = lean_ctor_get(x_598, 0);
lean_inc(x_646);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 x_647 = x_598;
} else {
 lean_dec_ref(x_598);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 1, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_646);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_591);
lean_dec_ref(x_587);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_649 = lean_box(0);
if (lean_is_scalar(x_592)) {
 x_650 = lean_alloc_ctor(0, 1, 0);
} else {
 x_650 = x_592;
}
lean_ctor_set(x_650, 0, x_649);
return x_650;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec_ref(x_587);
lean_dec(x_584);
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_651 = lean_ctor_get(x_590, 0);
lean_inc(x_651);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_652 = x_590;
} else {
 lean_dec_ref(x_590);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 1, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_651);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_654 = lean_ctor_get(x_583, 0);
lean_inc(x_654);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 x_655 = x_583;
} else {
 lean_dec_ref(x_583);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 1, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_654);
return x_656;
}
}
else
{
lean_object* x_657; lean_object* x_658; 
lean_dec(x_580);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_657 = lean_box(0);
if (lean_is_scalar(x_581)) {
 x_658 = lean_alloc_ctor(0, 1, 0);
} else {
 x_658 = x_581;
}
lean_ctor_set(x_658, 0, x_657);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_659 = lean_ctor_get(x_579, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_660 = x_579;
} else {
 lean_dec_ref(x_579);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 1, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_659);
return x_661;
}
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_662 = lean_ctor_get(x_573, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_663 = x_573;
} else {
 lean_dec_ref(x_573);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_662);
return x_664;
}
}
}
}
else
{
uint8_t x_665; 
lean_dec_ref(x_178);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_665 = !lean_is_exclusive(x_180);
if (x_665 == 0)
{
return x_180;
}
else
{
lean_object* x_666; lean_object* x_667; 
x_666 = lean_ctor_get(x_180, 0);
lean_inc(x_666);
lean_dec(x_180);
x_667 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_667, 0, x_666);
return x_667;
}
}
}
else
{
lean_object* x_668; 
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_668 = lean_box(0);
lean_ctor_set(x_174, 0, x_668);
return x_174;
}
}
else
{
lean_object* x_669; 
lean_dec(x_176);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_669 = lean_box(0);
lean_ctor_set(x_174, 0, x_669);
return x_174;
}
}
else
{
lean_object* x_670; 
x_670 = lean_ctor_get(x_174, 0);
lean_inc(x_670);
lean_dec(x_174);
if (lean_obj_tag(x_670) == 7)
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_671 = lean_ctor_get(x_670, 1);
lean_inc_ref(x_671);
x_672 = lean_ctor_get(x_670, 2);
lean_inc_ref(x_672);
lean_dec_ref(x_670);
x_673 = l_Lean_Expr_hasLooseBVars(x_672);
if (x_673 == 0)
{
lean_object* x_674; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_674 = l_Lean_Meta_isExprDefEq(x_171, x_671, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; uint8_t x_677; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_676 = x_674;
} else {
 lean_dec_ref(x_674);
 x_676 = lean_box(0);
}
x_677 = lean_unbox(x_675);
lean_dec(x_675);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; 
lean_dec_ref(x_672);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_678 = lean_box(0);
if (lean_is_scalar(x_676)) {
 x_679 = lean_alloc_ctor(0, 1, 0);
} else {
 x_679 = x_676;
}
lean_ctor_set(x_679, 0, x_678);
return x_679;
}
else
{
lean_object* x_680; 
lean_dec(x_676);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_680 = l_Lean_Meta_isExprDefEq(x_171, x_672, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; uint8_t x_683; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 x_682 = x_680;
} else {
 lean_dec_ref(x_680);
 x_682 = lean_box(0);
}
x_683 = lean_unbox(x_681);
lean_dec(x_681);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_684 = lean_box(0);
if (lean_is_scalar(x_682)) {
 x_685 = lean_alloc_ctor(0, 1, 0);
} else {
 x_685 = x_682;
}
lean_ctor_set(x_685, 0, x_684);
return x_685;
}
else
{
lean_object* x_686; 
lean_dec(x_682);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_686 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
lean_dec_ref(x_154);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; uint8_t x_689; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 x_688 = x_686;
} else {
 lean_dec_ref(x_686);
 x_688 = lean_box(0);
}
x_689 = lean_unbox(x_687);
if (x_689 == 0)
{
lean_object* x_690; 
lean_dec(x_688);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_171);
x_690 = l_Lean_Meta_getLevel(x_171, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
lean_dec_ref(x_690);
x_692 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18));
x_693 = lean_box(0);
lean_inc(x_691);
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_693);
lean_inc_ref(x_694);
x_695 = l_Lean_mkConst(x_692, x_694);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_696 = l_Lean_mkAppB(x_695, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_697 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_696, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 x_699 = x_697;
} else {
 lean_dec_ref(x_697);
 x_699 = lean_box(0);
}
if (lean_obj_tag(x_698) == 1)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_699);
x_700 = lean_ctor_get(x_698, 0);
lean_inc(x_700);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 x_701 = x_698;
} else {
 lean_dec_ref(x_698);
 x_701 = lean_box(0);
}
x_702 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_694);
x_703 = l_Lean_mkConst(x_702, x_694);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_704 = l_Lean_mkAppB(x_703, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_705 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_704, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
lean_dec_ref(x_705);
x_707 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_694);
x_708 = l_Lean_mkConst(x_707, x_694);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_709 = l_Lean_mkAppB(x_708, x_171, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_710 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_709, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; 
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
lean_dec_ref(x_710);
lean_inc_ref(x_171);
if (lean_is_scalar(x_701)) {
 x_712 = lean_alloc_ctor(1, 1, 0);
} else {
 x_712 = x_701;
}
lean_ctor_set(x_712, 0, x_171);
x_713 = 0;
x_714 = lean_box(0);
lean_inc_ref(x_161);
x_715 = l_Lean_Meta_mkFreshExprMVar(x_712, x_713, x_714, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
lean_dec_ref(x_715);
x_717 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_718 = l_Lean_mkConst(x_717, x_694);
lean_inc(x_716);
lean_inc_ref(x_1);
lean_inc_ref(x_171);
x_719 = l_Lean_mkApp3(x_718, x_171, x_1, x_716);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_720 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_719, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
lean_dec_ref(x_720);
if (lean_obj_tag(x_721) == 1)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_722 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_716, x_162);
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 x_724 = x_722;
} else {
 lean_dec_ref(x_722);
 x_724 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_725 = l_Lean_Meta_Grind_preprocessLight(x_723, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
lean_dec_ref(x_725);
x_727 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
lean_dec_ref(x_727);
x_729 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_726);
x_730 = lean_grind_internalize(x_726, x_728, x_729, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; uint8_t x_732; 
lean_dec_ref(x_730);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(1, 1, 0);
} else {
 x_731 = x_724;
 lean_ctor_set_tag(x_731, 1);
}
lean_ctor_set(x_731, 0, x_726);
x_732 = lean_unbox(x_687);
lean_dec(x_687);
lean_inc(x_706);
lean_inc(x_711);
x_109 = x_711;
x_110 = x_691;
x_111 = x_706;
x_112 = x_171;
x_113 = x_732;
x_114 = x_700;
x_115 = x_711;
x_116 = x_706;
x_117 = x_721;
x_118 = x_731;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_726);
lean_dec(x_724);
lean_dec_ref(x_721);
lean_dec(x_711);
lean_dec(x_706);
lean_dec(x_700);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_733 = lean_ctor_get(x_730, 0);
lean_inc(x_733);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 x_734 = x_730;
} else {
 lean_dec_ref(x_730);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(1, 1, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_733);
return x_735;
}
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_726);
lean_dec(x_724);
lean_dec_ref(x_721);
lean_dec(x_711);
lean_dec(x_706);
lean_dec(x_700);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_736 = lean_ctor_get(x_727, 0);
lean_inc(x_736);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 x_737 = x_727;
} else {
 lean_dec_ref(x_727);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 1, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_736);
return x_738;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_724);
lean_dec_ref(x_721);
lean_dec(x_711);
lean_dec(x_706);
lean_dec(x_700);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_739 = lean_ctor_get(x_725, 0);
lean_inc(x_739);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 x_740 = x_725;
} else {
 lean_dec_ref(x_725);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 1, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_739);
return x_741;
}
}
else
{
lean_object* x_742; uint8_t x_743; 
lean_dec(x_721);
lean_dec(x_716);
x_742 = lean_box(0);
x_743 = lean_unbox(x_687);
lean_dec(x_687);
lean_inc(x_706);
lean_inc(x_711);
x_109 = x_711;
x_110 = x_691;
x_111 = x_706;
x_112 = x_171;
x_113 = x_743;
x_114 = x_700;
x_115 = x_711;
x_116 = x_706;
x_117 = x_742;
x_118 = x_742;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_716);
lean_dec(x_711);
lean_dec(x_706);
lean_dec(x_700);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_744 = lean_ctor_get(x_720, 0);
lean_inc(x_744);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_745 = x_720;
} else {
 lean_dec_ref(x_720);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 1, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_744);
return x_746;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_711);
lean_dec(x_706);
lean_dec(x_700);
lean_dec_ref(x_694);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_747 = lean_ctor_get(x_715, 0);
lean_inc(x_747);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 x_748 = x_715;
} else {
 lean_dec_ref(x_715);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(1, 1, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_747);
return x_749;
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_706);
lean_dec(x_701);
lean_dec(x_700);
lean_dec_ref(x_694);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_750 = lean_ctor_get(x_710, 0);
lean_inc(x_750);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 x_751 = x_710;
} else {
 lean_dec_ref(x_710);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(1, 1, 0);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_750);
return x_752;
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_701);
lean_dec(x_700);
lean_dec_ref(x_694);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_753 = lean_ctor_get(x_705, 0);
lean_inc(x_753);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 x_754 = x_705;
} else {
 lean_dec_ref(x_705);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(1, 1, 0);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_753);
return x_755;
}
}
else
{
lean_object* x_756; lean_object* x_757; 
lean_dec(x_698);
lean_dec_ref(x_694);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_756 = lean_box(0);
if (lean_is_scalar(x_699)) {
 x_757 = lean_alloc_ctor(0, 1, 0);
} else {
 x_757 = x_699;
}
lean_ctor_set(x_757, 0, x_756);
return x_757;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec_ref(x_694);
lean_dec(x_691);
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_758 = lean_ctor_get(x_697, 0);
lean_inc(x_758);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 x_759 = x_697;
} else {
 lean_dec_ref(x_697);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 1, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_758);
return x_760;
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_761 = lean_ctor_get(x_690, 0);
lean_inc(x_761);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 x_762 = x_690;
} else {
 lean_dec_ref(x_690);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 1, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_761);
return x_763;
}
}
else
{
lean_object* x_764; lean_object* x_765; 
lean_dec(x_687);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_764 = lean_box(0);
if (lean_is_scalar(x_688)) {
 x_765 = lean_alloc_ctor(0, 1, 0);
} else {
 x_765 = x_688;
}
lean_ctor_set(x_765, 0, x_764);
return x_765;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_766 = lean_ctor_get(x_686, 0);
lean_inc(x_766);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 x_767 = x_686;
} else {
 lean_dec_ref(x_686);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 1, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_766);
return x_768;
}
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_769 = lean_ctor_get(x_680, 0);
lean_inc(x_769);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 x_770 = x_680;
} else {
 lean_dec_ref(x_680);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 1, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_769);
return x_771;
}
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec_ref(x_672);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_772 = lean_ctor_get(x_674, 0);
lean_inc(x_772);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_773 = x_674;
} else {
 lean_dec_ref(x_674);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_772);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; 
lean_dec_ref(x_672);
lean_dec_ref(x_671);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_775 = lean_box(0);
x_776 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_776, 0, x_775);
return x_776;
}
}
else
{
lean_object* x_777; lean_object* x_778; 
lean_dec(x_670);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_777 = lean_box(0);
x_778 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_778, 0, x_777);
return x_778;
}
}
}
else
{
uint8_t x_779; 
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_779 = !lean_is_exclusive(x_174);
if (x_779 == 0)
{
return x_174;
}
else
{
lean_object* x_780; lean_object* x_781; 
x_780 = lean_ctor_get(x_174, 0);
lean_inc(x_780);
lean_dec(x_174);
x_781 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_781, 0, x_780);
return x_781;
}
}
}
else
{
lean_object* x_782; 
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_782 = lean_box(0);
lean_ctor_set(x_168, 0, x_782);
return x_168;
}
}
else
{
lean_object* x_783; 
lean_dec(x_170);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_783 = lean_box(0);
lean_ctor_set(x_168, 0, x_783);
return x_168;
}
}
else
{
lean_object* x_784; 
x_784 = lean_ctor_get(x_168, 0);
lean_inc(x_784);
lean_dec(x_168);
if (lean_obj_tag(x_784) == 7)
{
lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_785 = lean_ctor_get(x_784, 1);
lean_inc_ref(x_785);
x_786 = lean_ctor_get(x_784, 2);
lean_inc_ref(x_786);
lean_dec_ref(x_784);
x_787 = l_Lean_Expr_hasLooseBVars(x_786);
if (x_787 == 0)
{
lean_object* x_788; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_788 = lean_whnf(x_786, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 x_790 = x_788;
} else {
 lean_dec_ref(x_788);
 x_790 = lean_box(0);
}
if (lean_obj_tag(x_789) == 7)
{
lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_791 = lean_ctor_get(x_789, 1);
lean_inc_ref(x_791);
x_792 = lean_ctor_get(x_789, 2);
lean_inc_ref(x_792);
lean_dec_ref(x_789);
x_793 = l_Lean_Expr_hasLooseBVars(x_792);
if (x_793 == 0)
{
lean_object* x_794; 
lean_dec(x_790);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_785);
x_794 = l_Lean_Meta_isExprDefEq(x_785, x_791, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; uint8_t x_797; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 x_796 = x_794;
} else {
 lean_dec_ref(x_794);
 x_796 = lean_box(0);
}
x_797 = lean_unbox(x_795);
lean_dec(x_795);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; 
lean_dec_ref(x_792);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_798 = lean_box(0);
if (lean_is_scalar(x_796)) {
 x_799 = lean_alloc_ctor(0, 1, 0);
} else {
 x_799 = x_796;
}
lean_ctor_set(x_799, 0, x_798);
return x_799;
}
else
{
lean_object* x_800; 
lean_dec(x_796);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_785);
x_800 = l_Lean_Meta_isExprDefEq(x_785, x_792, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; lean_object* x_802; uint8_t x_803; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 x_802 = x_800;
} else {
 lean_dec_ref(x_800);
 x_802 = lean_box(0);
}
x_803 = lean_unbox(x_801);
lean_dec(x_801);
if (x_803 == 0)
{
lean_object* x_804; lean_object* x_805; 
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_804 = lean_box(0);
if (lean_is_scalar(x_802)) {
 x_805 = lean_alloc_ctor(0, 1, 0);
} else {
 x_805 = x_802;
}
lean_ctor_set(x_805, 0, x_804);
return x_805;
}
else
{
lean_object* x_806; 
lean_dec(x_802);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_806 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
lean_dec_ref(x_154);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; uint8_t x_809; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 x_808 = x_806;
} else {
 lean_dec_ref(x_806);
 x_808 = lean_box(0);
}
x_809 = lean_unbox(x_807);
if (x_809 == 0)
{
lean_object* x_810; 
lean_dec(x_808);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc_ref(x_785);
x_810 = l_Lean_Meta_getLevel(x_785, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
lean_dec_ref(x_810);
x_812 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18));
x_813 = lean_box(0);
lean_inc(x_811);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_813);
lean_inc_ref(x_814);
x_815 = l_Lean_mkConst(x_812, x_814);
lean_inc_ref(x_1);
lean_inc_ref(x_785);
x_816 = l_Lean_mkAppB(x_815, x_785, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_817 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_816, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 x_819 = x_817;
} else {
 lean_dec_ref(x_817);
 x_819 = lean_box(0);
}
if (lean_obj_tag(x_818) == 1)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_819);
x_820 = lean_ctor_get(x_818, 0);
lean_inc(x_820);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 x_821 = x_818;
} else {
 lean_dec_ref(x_818);
 x_821 = lean_box(0);
}
x_822 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20));
lean_inc_ref(x_814);
x_823 = l_Lean_mkConst(x_822, x_814);
lean_inc_ref(x_1);
lean_inc_ref(x_785);
x_824 = l_Lean_mkAppB(x_823, x_785, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_825 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_824, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
lean_dec_ref(x_825);
x_827 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22));
lean_inc_ref(x_814);
x_828 = l_Lean_mkConst(x_827, x_814);
lean_inc_ref(x_1);
lean_inc_ref(x_785);
x_829 = l_Lean_mkAppB(x_828, x_785, x_1);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_830 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_829, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; uint8_t x_833; lean_object* x_834; lean_object* x_835; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
lean_dec_ref(x_830);
lean_inc_ref(x_785);
if (lean_is_scalar(x_821)) {
 x_832 = lean_alloc_ctor(1, 1, 0);
} else {
 x_832 = x_821;
}
lean_ctor_set(x_832, 0, x_785);
x_833 = 0;
x_834 = lean_box(0);
lean_inc_ref(x_161);
x_835 = l_Lean_Meta_mkFreshExprMVar(x_832, x_833, x_834, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
lean_dec_ref(x_835);
x_837 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24));
x_838 = l_Lean_mkConst(x_837, x_814);
lean_inc(x_836);
lean_inc_ref(x_1);
lean_inc_ref(x_785);
x_839 = l_Lean_mkApp3(x_838, x_785, x_1, x_836);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_840 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_839, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
lean_dec_ref(x_840);
if (lean_obj_tag(x_841) == 1)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_842 = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(x_836, x_162);
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 x_844 = x_842;
} else {
 lean_dec_ref(x_842);
 x_844 = lean_box(0);
}
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_845 = l_Lean_Meta_Grind_preprocessLight(x_843, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
lean_dec_ref(x_845);
x_847 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_155);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
lean_dec_ref(x_847);
x_849 = lean_box(0);
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_846);
x_850 = lean_grind_internalize(x_846, x_848, x_849, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; uint8_t x_852; 
lean_dec_ref(x_850);
if (lean_is_scalar(x_844)) {
 x_851 = lean_alloc_ctor(1, 1, 0);
} else {
 x_851 = x_844;
 lean_ctor_set_tag(x_851, 1);
}
lean_ctor_set(x_851, 0, x_846);
x_852 = lean_unbox(x_807);
lean_dec(x_807);
lean_inc(x_826);
lean_inc(x_831);
x_109 = x_831;
x_110 = x_811;
x_111 = x_826;
x_112 = x_785;
x_113 = x_852;
x_114 = x_820;
x_115 = x_831;
x_116 = x_826;
x_117 = x_841;
x_118 = x_851;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_846);
lean_dec(x_844);
lean_dec_ref(x_841);
lean_dec(x_831);
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_853 = lean_ctor_get(x_850, 0);
lean_inc(x_853);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 x_854 = x_850;
} else {
 lean_dec_ref(x_850);
 x_854 = lean_box(0);
}
if (lean_is_scalar(x_854)) {
 x_855 = lean_alloc_ctor(1, 1, 0);
} else {
 x_855 = x_854;
}
lean_ctor_set(x_855, 0, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_846);
lean_dec(x_844);
lean_dec_ref(x_841);
lean_dec(x_831);
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_856 = lean_ctor_get(x_847, 0);
lean_inc(x_856);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 x_857 = x_847;
} else {
 lean_dec_ref(x_847);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 1, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_856);
return x_858;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec(x_844);
lean_dec_ref(x_841);
lean_dec(x_831);
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_859 = lean_ctor_get(x_845, 0);
lean_inc(x_859);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 x_860 = x_845;
} else {
 lean_dec_ref(x_845);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 1, 0);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_859);
return x_861;
}
}
else
{
lean_object* x_862; uint8_t x_863; 
lean_dec(x_841);
lean_dec(x_836);
x_862 = lean_box(0);
x_863 = lean_unbox(x_807);
lean_dec(x_807);
lean_inc(x_826);
lean_inc(x_831);
x_109 = x_831;
x_110 = x_811;
x_111 = x_826;
x_112 = x_785;
x_113 = x_863;
x_114 = x_820;
x_115 = x_831;
x_116 = x_826;
x_117 = x_862;
x_118 = x_862;
x_119 = x_155;
x_120 = x_156;
x_121 = x_157;
x_122 = x_158;
x_123 = x_159;
x_124 = x_160;
x_125 = x_161;
x_126 = x_162;
x_127 = x_163;
x_128 = x_164;
x_129 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_836);
lean_dec(x_831);
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_864 = lean_ctor_get(x_840, 0);
lean_inc(x_864);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 x_865 = x_840;
} else {
 lean_dec_ref(x_840);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 1, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_864);
return x_866;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_831);
lean_dec(x_826);
lean_dec(x_820);
lean_dec_ref(x_814);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_867 = lean_ctor_get(x_835, 0);
lean_inc(x_867);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 x_868 = x_835;
} else {
 lean_dec_ref(x_835);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 1, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_867);
return x_869;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_826);
lean_dec(x_821);
lean_dec(x_820);
lean_dec_ref(x_814);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_870 = lean_ctor_get(x_830, 0);
lean_inc(x_870);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 x_871 = x_830;
} else {
 lean_dec_ref(x_830);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 1, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_870);
return x_872;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec_ref(x_814);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_873 = lean_ctor_get(x_825, 0);
lean_inc(x_873);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 x_874 = x_825;
} else {
 lean_dec_ref(x_825);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 1, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_818);
lean_dec_ref(x_814);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_876 = lean_box(0);
if (lean_is_scalar(x_819)) {
 x_877 = lean_alloc_ctor(0, 1, 0);
} else {
 x_877 = x_819;
}
lean_ctor_set(x_877, 0, x_876);
return x_877;
}
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec_ref(x_814);
lean_dec(x_811);
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_878 = lean_ctor_get(x_817, 0);
lean_inc(x_878);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 x_879 = x_817;
} else {
 lean_dec_ref(x_817);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 1, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_878);
return x_880;
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_881 = lean_ctor_get(x_810, 0);
lean_inc(x_881);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 x_882 = x_810;
} else {
 lean_dec_ref(x_810);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 1, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_881);
return x_883;
}
}
else
{
lean_object* x_884; lean_object* x_885; 
lean_dec(x_807);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_884 = lean_box(0);
if (lean_is_scalar(x_808)) {
 x_885 = lean_alloc_ctor(0, 1, 0);
} else {
 x_885 = x_808;
}
lean_ctor_set(x_885, 0, x_884);
return x_885;
}
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_1);
x_886 = lean_ctor_get(x_806, 0);
lean_inc(x_886);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 x_887 = x_806;
} else {
 lean_dec_ref(x_806);
 x_887 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_888 = lean_alloc_ctor(1, 1, 0);
} else {
 x_888 = x_887;
}
lean_ctor_set(x_888, 0, x_886);
return x_888;
}
}
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_889 = lean_ctor_get(x_800, 0);
lean_inc(x_889);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 x_890 = x_800;
} else {
 lean_dec_ref(x_800);
 x_890 = lean_box(0);
}
if (lean_is_scalar(x_890)) {
 x_891 = lean_alloc_ctor(1, 1, 0);
} else {
 x_891 = x_890;
}
lean_ctor_set(x_891, 0, x_889);
return x_891;
}
}
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec_ref(x_792);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_892 = lean_ctor_get(x_794, 0);
lean_inc(x_892);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 x_893 = x_794;
} else {
 lean_dec_ref(x_794);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(1, 1, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_892);
return x_894;
}
}
else
{
lean_object* x_895; lean_object* x_896; 
lean_dec_ref(x_792);
lean_dec_ref(x_791);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_895 = lean_box(0);
if (lean_is_scalar(x_790)) {
 x_896 = lean_alloc_ctor(0, 1, 0);
} else {
 x_896 = x_790;
}
lean_ctor_set(x_896, 0, x_895);
return x_896;
}
}
else
{
lean_object* x_897; lean_object* x_898; 
lean_dec(x_789);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_897 = lean_box(0);
if (lean_is_scalar(x_790)) {
 x_898 = lean_alloc_ctor(0, 1, 0);
} else {
 x_898 = x_790;
}
lean_ctor_set(x_898, 0, x_897);
return x_898;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_899 = lean_ctor_get(x_788, 0);
lean_inc(x_899);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 x_900 = x_788;
} else {
 lean_dec_ref(x_788);
 x_900 = lean_box(0);
}
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(1, 1, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_899);
return x_901;
}
}
else
{
lean_object* x_902; lean_object* x_903; 
lean_dec_ref(x_786);
lean_dec_ref(x_785);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_902 = lean_box(0);
x_903 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_903, 0, x_902);
return x_903;
}
}
else
{
lean_object* x_904; lean_object* x_905; 
lean_dec(x_784);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_904 = lean_box(0);
x_905 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_905, 0, x_904);
return x_905;
}
}
}
else
{
uint8_t x_906; 
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_906 = !lean_is_exclusive(x_168);
if (x_906 == 0)
{
return x_168;
}
else
{
lean_object* x_907; lean_object* x_908; 
x_907 = lean_ctor_get(x_168, 0);
lean_inc(x_907);
lean_dec(x_168);
x_908 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_908, 0, x_907);
return x_908;
}
}
}
else
{
uint8_t x_909; 
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_909 = !lean_is_exclusive(x_166);
if (x_909 == 0)
{
return x_166;
}
else
{
lean_object* x_910; lean_object* x_911; 
x_910 = lean_ctor_get(x_166, 0);
lean_inc(x_910);
lean_dec(x_166);
x_911 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_911, 0, x_910);
return x_911;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_11 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(x_8, x_1, x_2);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_16, x_1);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; 
lean_dec(x_17);
lean_free_object(x_13);
lean_inc(x_2);
lean_inc_ref(x_1);
x_19 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_Grind_AC_acExt;
x_23 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_22, x_21, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_31);
lean_dec(x_30);
x_32 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(x_31, x_1);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_32);
lean_inc(x_2);
lean_inc_ref(x_1);
x_35 = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_Grind_AC_acExt;
x_39 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_38, x_37, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_40 = x_39;
} else {
 lean_dec_ref(x_39);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_getOpId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; uint8_t x_43; 
x_43 = l_Lean_Expr_isApp(x_1);
if (x_43 == 0)
{
x_14 = x_43;
goto block_42;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Expr_appFn_x21(x_1);
x_45 = l_Lean_Expr_isApp(x_44);
lean_dec_ref(x_44);
x_14 = x_45;
goto block_42;
}
block_42:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_AC_getOp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Expr_appFn_x21(x_1);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_21, x_19);
lean_dec(x_19);
lean_dec_ref(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_20);
x_23 = lean_box(0);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Expr_appArg_x21(x_20);
lean_dec_ref(x_20);
x_25 = l_Lean_Expr_appArg_x21(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = l_Lean_Expr_appFn_x21(x_1);
x_30 = l_Lean_Expr_appFn_x21(x_29);
x_31 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_30, x_28);
lean_dec(x_28);
lean_dec_ref(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_29);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = l_Lean_Expr_appArg_x21(x_29);
lean_dec_ref(x_29);
x_35 = l_Lean_Expr_appArg_x21(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_AC_isOp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 7);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
uint8_t x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_22);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_isCommutative(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 8);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
uint8_t x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 8);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_22);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_hasNeutral(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_ACM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 6);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
uint8_t x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 6);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_22);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_AC_isIdempotent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1 = _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc);
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__4);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
