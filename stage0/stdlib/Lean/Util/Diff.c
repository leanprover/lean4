// Lean compiler output
// Module: Lean.Util.Diff
// Imports: public import Init.Data.Array.Subarray.Split public import Init.Data.Slice.Array.Iterator public import Init.Data.Range public import Std.Data.HashMap.Basic public import Init.Data.String.Basic public import Init.Data.Range.Polymorphic.RangeIterator public import Init.While import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Data.ToString.Macro import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Diff_instReprAction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Diff.Action.insert"};
static const lean_object* l_Lean_Diff_instReprAction_repr___closed__0 = (const lean_object*)&l_Lean_Diff_instReprAction_repr___closed__0_value;
static const lean_ctor_object l_Lean_Diff_instReprAction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Diff_instReprAction_repr___closed__0_value)}};
static const lean_object* l_Lean_Diff_instReprAction_repr___closed__1 = (const lean_object*)&l_Lean_Diff_instReprAction_repr___closed__1_value;
static const lean_string_object l_Lean_Diff_instReprAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Diff.Action.delete"};
static const lean_object* l_Lean_Diff_instReprAction_repr___closed__2 = (const lean_object*)&l_Lean_Diff_instReprAction_repr___closed__2_value;
static const lean_ctor_object l_Lean_Diff_instReprAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Diff_instReprAction_repr___closed__2_value)}};
static const lean_object* l_Lean_Diff_instReprAction_repr___closed__3 = (const lean_object*)&l_Lean_Diff_instReprAction_repr___closed__3_value;
static const lean_string_object l_Lean_Diff_instReprAction_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Diff.Action.skip"};
static const lean_object* l_Lean_Diff_instReprAction_repr___closed__4 = (const lean_object*)&l_Lean_Diff_instReprAction_repr___closed__4_value;
static const lean_ctor_object l_Lean_Diff_instReprAction_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Diff_instReprAction_repr___closed__4_value)}};
static const lean_object* l_Lean_Diff_instReprAction_repr___closed__5 = (const lean_object*)&l_Lean_Diff_instReprAction_repr___closed__5_value;
static lean_once_cell_t l_Lean_Diff_instReprAction_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_instReprAction_repr___closed__6;
static lean_once_cell_t l_Lean_Diff_instReprAction_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_instReprAction_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Diff_instReprAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_instReprAction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_instReprAction___closed__0 = (const lean_object*)&l_Lean_Diff_instReprAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Diff_instReprAction = (const lean_object*)&l_Lean_Diff_instReprAction___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_instBEqAction_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Diff_instBEqAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_instBEqAction_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_instBEqAction___closed__0 = (const lean_object*)&l_Lean_Diff_instBEqAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Diff_instBEqAction = (const lean_object*)&l_Lean_Diff_instBEqAction___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Diff_instHashableAction_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_instHashableAction_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Diff_instHashableAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_instHashableAction_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_instHashableAction___closed__0 = (const lean_object*)&l_Lean_Diff_instHashableAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Diff_instHashableAction = (const lean_object*)&l_Lean_Diff_instHashableAction___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Diff_instInhabitedAction_default;
LEAN_EXPORT uint8_t l_Lean_Diff_instInhabitedAction;
static const lean_string_object l_Lean_Diff_instToStringAction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "insert"};
static const lean_object* l_Lean_Diff_instToStringAction___lam__0___closed__0 = (const lean_object*)&l_Lean_Diff_instToStringAction___lam__0___closed__0_value;
static const lean_string_object l_Lean_Diff_instToStringAction___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "delete"};
static const lean_object* l_Lean_Diff_instToStringAction___lam__0___closed__1 = (const lean_object*)&l_Lean_Diff_instToStringAction___lam__0___closed__1_value;
static const lean_string_object l_Lean_Diff_instToStringAction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Diff_instToStringAction___lam__0___closed__2 = (const lean_object*)&l_Lean_Diff_instToStringAction___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Diff_instToStringAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_instToStringAction___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_instToStringAction___closed__0 = (const lean_object*)&l_Lean_Diff_instToStringAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Diff_instToStringAction = (const lean_object*)&l_Lean_Diff_instToStringAction___closed__0_value;
static const lean_string_object l_Lean_Diff_Action_linePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Diff_Action_linePrefix___closed__0 = (const lean_object*)&l_Lean_Diff_Action_linePrefix___closed__0_value;
static const lean_string_object l_Lean_Diff_Action_linePrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Diff_Action_linePrefix___closed__1 = (const lean_object*)&l_Lean_Diff_Action_linePrefix___closed__1_value;
static const lean_string_object l_Lean_Diff_Action_linePrefix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Diff_Action_linePrefix___closed__2 = (const lean_object*)&l_Lean_Diff_Action_linePrefix___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_matchPrefix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_matchPrefix___redArg___closed__0 = (const lean_object*)&l_Lean_Diff_matchPrefix___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__0 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__0_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__1 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__1_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__2 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__2_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__3 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__3_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__4 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__4_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__5 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__5_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__6 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Diff_lcs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_lcs___redArg___closed__0_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__1_value)}};
static const lean_object* l_Lean_Diff_lcs___redArg___closed__7 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Diff_lcs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_lcs___redArg___closed__7_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__2_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__3_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__4_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__5_value)}};
static const lean_object* l_Lean_Diff_lcs___redArg___closed__8 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Diff_lcs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_lcs___redArg___closed__8_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__6_value)}};
static const lean_object* l_Lean_Diff_lcs___redArg___closed__9 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Diff_lcs___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___redArg___closed__10;
static lean_once_cell_t l_Lean_Diff_lcs___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___redArg___closed__11;
static lean_once_cell_t l_Lean_Diff_lcs___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___redArg___closed__12;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_lcs___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__13 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__13_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_lcs___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__14 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Diff_diff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_diff___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_diff___redArg___closed__0 = (const lean_object*)&l_Lean_Diff_diff___redArg___closed__0_value;
static const lean_closure_object l_Lean_Diff_diff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_diff___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_diff___redArg___closed__1 = (const lean_object*)&l_Lean_Diff_diff___redArg___closed__1_value;
static const lean_array_object l_Lean_Diff_diff___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___redArg___closed__2 = (const lean_object*)&l_Lean_Diff_diff___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Diff_diff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Diff_diff___redArg___closed__3 = (const lean_object*)&l_Lean_Diff_diff___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Diff_diff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___redArg___closed__2_value),((lean_object*)&l_Lean_Diff_diff___redArg___closed__3_value)}};
static const lean_object* l_Lean_Diff_diff___redArg___closed__4 = (const lean_object*)&l_Lean_Diff_diff___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Diff_linesToString___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Diff_linesToString___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Diff_linesToString___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Diff_linesToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Diff_linesToString___redArg___closed__0 = (const lean_object*)&l_Lean_Diff_linesToString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Diff_Action_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Diff_Action_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Diff_Action_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg(lean_object* v_insert_23_){
_start:
{
lean_inc(v_insert_23_);
return v_insert_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg___boxed(lean_object* v_insert_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Diff_Action_insert_elim___redArg(v_insert_24_);
lean_dec(v_insert_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_insert_29_){
_start:
{
lean_inc(v_insert_29_);
return v_insert_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_insert_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Diff_Action_insert_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_insert_33_);
lean_dec(v_insert_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg(lean_object* v_delete_36_){
_start:
{
lean_inc(v_delete_36_);
return v_delete_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg___boxed(lean_object* v_delete_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Diff_Action_delete_elim___redArg(v_delete_37_);
lean_dec(v_delete_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_delete_42_){
_start:
{
lean_inc(v_delete_42_);
return v_delete_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_delete_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Diff_Action_delete_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_delete_46_);
lean_dec(v_delete_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg(lean_object* v_skip_49_){
_start:
{
lean_inc(v_skip_49_);
return v_skip_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg___boxed(lean_object* v_skip_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Diff_Action_skip_elim___redArg(v_skip_50_);
lean_dec(v_skip_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_skip_55_){
_start:
{
lean_inc(v_skip_55_);
return v_skip_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_skip_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Diff_Action_skip_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_skip_59_);
lean_dec(v_skip_59_);
return v_res_61_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr(uint8_t v_x_75_, lean_object* v_prec_76_){
_start:
{
lean_object* v___y_78_; lean_object* v___y_85_; lean_object* v___y_92_; 
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_76_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_78_ = v___x_100_;
goto v___jp_77_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_78_ = v___x_101_;
goto v___jp_77_;
}
}
case 1:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_76_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_85_ = v___x_104_;
goto v___jp_84_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_85_ = v___x_105_;
goto v___jp_84_;
}
}
default: 
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_76_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__1));
lean_inc(v___y_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v_prec_76_);
return v___x_83_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__3));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_76_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__5));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_76_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
uint8_t v_x_177__boxed_112_; lean_object* v_res_113_; 
v_x_177__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Lean_Diff_instReprAction_repr(v_x_177__boxed_112_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t v_x_116_, uint8_t v_y_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = l_Lean_Diff_Action_ctorIdx(v_x_116_);
v___x_119_ = l_Lean_Diff_Action_ctorIdx(v_y_117_);
v___x_120_ = lean_nat_dec_eq(v___x_118_, v___x_119_);
lean_dec(v___x_119_);
lean_dec(v___x_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instBEqAction_beq___boxed(lean_object* v_x_121_, lean_object* v_y_122_){
_start:
{
uint8_t v_x_17__boxed_123_; uint8_t v_y_18__boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_x_17__boxed_123_ = lean_unbox(v_x_121_);
v_y_18__boxed_124_ = lean_unbox(v_y_122_);
v_res_125_ = l_Lean_Diff_instBEqAction_beq(v_x_17__boxed_123_, v_y_18__boxed_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint64_t l_Lean_Diff_instHashableAction_hash(uint8_t v_x_129_){
_start:
{
switch(v_x_129_)
{
case 0:
{
uint64_t v___x_130_; 
v___x_130_ = 0ULL;
return v___x_130_;
}
case 1:
{
uint64_t v___x_131_; 
v___x_131_ = 1ULL;
return v___x_131_;
}
default: 
{
uint64_t v___x_132_; 
v___x_132_ = 2ULL;
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instHashableAction_hash___boxed(lean_object* v_x_133_){
_start:
{
uint8_t v_x_40__boxed_134_; uint64_t v_res_135_; lean_object* v_r_136_; 
v_x_40__boxed_134_ = lean_unbox(v_x_133_);
v_res_135_ = l_Lean_Diff_instHashableAction_hash(v_x_40__boxed_134_);
v_r_136_ = lean_box_uint64(v_res_135_);
return v_r_136_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction_default(void){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction(void){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0(uint8_t v_x_144_){
_start:
{
switch(v_x_144_)
{
case 0:
{
lean_object* v___x_145_; 
v___x_145_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__0));
return v___x_145_;
}
case 1:
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__1));
return v___x_146_;
}
default: 
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__2));
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0___boxed(lean_object* v_x_148_){
_start:
{
uint8_t v_x_36__boxed_149_; lean_object* v_res_150_; 
v_x_36__boxed_149_ = lean_unbox(v_x_148_);
v_res_150_ = l_Lean_Diff_instToStringAction___lam__0(v_x_36__boxed_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix(uint8_t v_x_156_){
_start:
{
switch(v_x_156_)
{
case 0:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__0));
return v___x_157_;
}
case 1:
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__1));
return v___x_158_;
}
default: 
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_31__boxed_161_; lean_object* v_res_162_; 
v_x_31__boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l_Lean_Diff_Action_linePrefix(v_x_31__boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___redArg(lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_histogram_165_, lean_object* v_index_166_, lean_object* v_val_167_){
_start:
{
lean_object* v___x_168_; 
lean_inc(v_val_167_);
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_163_, v_inst_164_, v_histogram_165_, v_val_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___y_175_; lean_object* v_i_176_; lean_object* v___y_181_; lean_object* v___y_190_; lean_object* v_i_191_; lean_object* v___x_204_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v_index_166_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_box(0);
v___x_173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_173_, 0, v___x_169_);
lean_ctor_set(v___x_173_, 1, v___x_170_);
lean_ctor_set(v___x_173_, 2, v___x_171_);
lean_ctor_set(v___x_173_, 3, v___x_172_);
lean_inc(v_val_167_);
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_163_, v_inst_164_, v_histogram_165_, v_val_167_);
switch(lean_obj_tag(v___x_204_))
{
case 0:
{
lean_object* v_index_205_; lean_object* v_size_206_; lean_object* v___x_207_; 
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
v_index_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_205_);
lean_dec_ref_known(v___x_204_, 3);
v_size_206_ = lean_ctor_get(v_histogram_165_, 0);
lean_inc(v_size_206_);
v___x_207_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_165_, v_size_206_, v_index_205_, v_val_167_, v___x_173_);
lean_dec(v_index_205_);
return v___x_207_;
}
case 1:
{
lean_object* v_index_208_; lean_object* v_size_209_; lean_object* v_keyArray_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_index_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_204_, 1);
v_size_209_ = lean_ctor_get(v_histogram_165_, 0);
v_keyArray_210_ = lean_ctor_get(v_histogram_165_, 1);
v___x_211_ = lean_nat_add(v_size_209_, v___x_169_);
v___x_212_ = lean_array_get_size(v_keyArray_210_);
v___x_213_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec(v___x_211_);
lean_dec(v_index_208_);
goto v___jp_195_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_214_ = lean_unsigned_to_nat(4u);
v___x_215_ = lean_nat_mul(v___x_211_, v___x_214_);
v___x_216_ = lean_unsigned_to_nat(3u);
v___x_217_ = lean_nat_mul(v___x_212_, v___x_216_);
v___x_218_ = lean_nat_dec_le(v___x_215_, v___x_217_);
lean_dec(v___x_217_);
lean_dec(v___x_215_);
if (v___x_218_ == 0)
{
lean_dec(v___x_211_);
lean_dec(v_index_208_);
goto v___jp_195_;
}
else
{
lean_object* v___x_219_; 
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_165_, v___x_211_, v_index_208_, v_val_167_, v___x_173_);
lean_dec(v_index_208_);
return v___x_219_;
}
}
}
default: 
{
lean_object* v_size_220_; lean_object* v_keyArray_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_size_220_ = lean_ctor_get(v_histogram_165_, 0);
v_keyArray_221_ = lean_ctor_get(v_histogram_165_, 1);
v___x_222_ = lean_nat_add(v_size_220_, v___x_169_);
v___x_223_ = lean_array_get_size(v_keyArray_221_);
v___x_224_ = lean_nat_dec_lt(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec(v___x_222_);
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_163_, v_inst_164_, v_histogram_165_);
v___y_181_ = v___x_225_;
goto v___jp_180_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_226_ = lean_unsigned_to_nat(4u);
v___x_227_ = lean_nat_mul(v___x_222_, v___x_226_);
lean_dec(v___x_222_);
v___x_228_ = lean_unsigned_to_nat(3u);
v___x_229_ = lean_nat_mul(v___x_223_, v___x_228_);
v___x_230_ = lean_nat_dec_le(v___x_227_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v___x_227_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_163_, v_inst_164_, v_histogram_165_);
v___y_181_ = v___x_231_;
goto v___jp_180_;
}
else
{
v___y_181_ = v_histogram_165_;
goto v___jp_180_;
}
}
}
}
v___jp_174_:
{
lean_object* v_size_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_size_177_ = lean_ctor_get(v___y_175_, 0);
v___x_178_ = lean_nat_add(v_size_177_, v___x_169_);
v___x_179_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_175_, v___x_178_, v_i_176_, v_val_167_, v___x_173_);
lean_dec(v_i_176_);
return v___x_179_;
}
v___jp_180_:
{
lean_object* v___x_182_; 
lean_inc(v_val_167_);
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_163_, v_inst_164_, v___y_181_, v_val_167_);
switch(lean_obj_tag(v___x_182_))
{
case 0:
{
lean_object* v_index_183_; lean_object* v_size_184_; lean_object* v___x_185_; 
v_index_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_index_183_);
lean_dec_ref_known(v___x_182_, 3);
v_size_184_ = lean_ctor_get(v___y_181_, 0);
lean_inc(v_size_184_);
v___x_185_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_181_, v_size_184_, v_index_183_, v_val_167_, v___x_173_);
lean_dec(v_index_183_);
return v___x_185_;
}
case 1:
{
lean_object* v_index_186_; 
v_index_186_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_index_186_);
lean_dec_ref_known(v___x_182_, 1);
v___y_175_ = v___y_181_;
v_i_176_ = v_index_186_;
goto v___jp_174_;
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_181_, v___x_171_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_index_188_; 
v_index_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_index_188_);
lean_dec_ref_known(v___x_187_, 1);
v___y_175_ = v___y_181_;
v_i_176_ = v_index_188_;
goto v___jp_174_;
}
else
{
lean_dec_ref_known(v___x_173_, 4);
lean_dec(v_val_167_);
return v___y_181_;
}
}
}
}
v___jp_189_:
{
lean_object* v_size_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_size_192_ = lean_ctor_get(v___y_190_, 0);
v___x_193_ = lean_nat_add(v_size_192_, v___x_169_);
v___x_194_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_190_, v___x_193_, v_i_191_, v_val_167_, v___x_173_);
lean_dec(v_i_191_);
return v___x_194_;
}
v___jp_195_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_163_, v_inst_164_, v_histogram_165_);
lean_inc(v_val_167_);
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_163_, v_inst_164_, v___x_196_, v_val_167_);
switch(lean_obj_tag(v___x_197_))
{
case 0:
{
lean_object* v_index_198_; lean_object* v_size_199_; lean_object* v___x_200_; 
v_index_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_198_);
lean_dec_ref_known(v___x_197_, 3);
v_size_199_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_size_199_);
v___x_200_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_196_, v_size_199_, v_index_198_, v_val_167_, v___x_173_);
lean_dec(v_index_198_);
return v___x_200_;
}
case 1:
{
lean_object* v_index_201_; 
v_index_201_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_201_);
lean_dec_ref_known(v___x_197_, 1);
v___y_190_ = v___x_196_;
v_i_191_ = v_index_201_;
goto v___jp_189_;
}
default: 
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_196_, v___x_171_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_index_203_; 
v_index_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_202_, 1);
v___y_190_ = v___x_196_;
v_i_191_ = v_index_203_;
goto v___jp_189_;
}
else
{
lean_dec_ref_known(v___x_173_, 4);
lean_dec(v_val_167_);
return v___x_196_;
}
}
}
}
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_312_; 
v_val_232_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_312_ == 0)
{
v___x_234_ = v___x_168_;
v_isShared_235_ = v_isSharedCheck_312_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v___x_168_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_312_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_leftCount_236_; lean_object* v_rightCount_237_; lean_object* v_rightIndex_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_310_; 
v_leftCount_236_ = lean_ctor_get(v_val_232_, 0);
v_rightCount_237_ = lean_ctor_get(v_val_232_, 2);
v_rightIndex_238_ = lean_ctor_get(v_val_232_, 3);
v_isSharedCheck_310_ = !lean_is_exclusive(v_val_232_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v_val_232_, 1);
lean_dec(v_unused_311_);
v___x_240_ = v_val_232_;
v_isShared_241_ = v_isSharedCheck_310_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_rightIndex_238_);
lean_inc(v_rightCount_237_);
lean_inc(v_leftCount_236_);
lean_dec(v_val_232_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_310_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_leftCount_236_, v___x_242_);
lean_dec(v_leftCount_236_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_index_166_);
v___x_245_ = v___x_234_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_index_166_);
v___x_245_ = v_reuseFailAlloc_309_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_245_);
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_rightCount_237_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_rightIndex_238_);
v___x_247_ = v_reuseFailAlloc_308_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___y_249_; lean_object* v_i_250_; lean_object* v___y_255_; lean_object* v___y_265_; lean_object* v_i_266_; lean_object* v___x_280_; 
lean_inc(v_val_167_);
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_163_, v_inst_164_, v_histogram_165_, v_val_167_);
switch(lean_obj_tag(v___x_280_))
{
case 0:
{
lean_object* v_index_281_; lean_object* v_size_282_; lean_object* v___x_283_; 
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
v_index_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_281_);
lean_dec_ref_known(v___x_280_, 3);
v_size_282_ = lean_ctor_get(v_histogram_165_, 0);
lean_inc(v_size_282_);
v___x_283_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_165_, v_size_282_, v_index_281_, v_val_167_, v___x_247_);
lean_dec(v_index_281_);
return v___x_283_;
}
case 1:
{
lean_object* v_index_284_; lean_object* v_size_285_; lean_object* v_keyArray_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_index_284_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_284_);
lean_dec_ref_known(v___x_280_, 1);
v_size_285_ = lean_ctor_get(v_histogram_165_, 0);
v_keyArray_286_ = lean_ctor_get(v_histogram_165_, 1);
v___x_287_ = lean_nat_add(v_size_285_, v___x_242_);
v___x_288_ = lean_array_get_size(v_keyArray_286_);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec(v___x_287_);
lean_dec(v_index_284_);
goto v___jp_270_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_nat_mul(v___x_287_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = lean_nat_mul(v___x_288_, v___x_292_);
v___x_294_ = lean_nat_dec_le(v___x_291_, v___x_293_);
lean_dec(v___x_293_);
lean_dec(v___x_291_);
if (v___x_294_ == 0)
{
lean_dec(v___x_287_);
lean_dec(v_index_284_);
goto v___jp_270_;
}
else
{
lean_object* v___x_295_; 
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
v___x_295_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_165_, v___x_287_, v_index_284_, v_val_167_, v___x_247_);
lean_dec(v_index_284_);
return v___x_295_;
}
}
}
default: 
{
lean_object* v_size_296_; lean_object* v_keyArray_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_size_296_ = lean_ctor_get(v_histogram_165_, 0);
v_keyArray_297_ = lean_ctor_get(v_histogram_165_, 1);
v___x_298_ = lean_nat_add(v_size_296_, v___x_242_);
v___x_299_ = lean_array_get_size(v_keyArray_297_);
v___x_300_ = lean_nat_dec_lt(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec(v___x_298_);
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_163_, v_inst_164_, v_histogram_165_);
v___y_255_ = v___x_301_;
goto v___jp_254_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_302_ = lean_unsigned_to_nat(4u);
v___x_303_ = lean_nat_mul(v___x_298_, v___x_302_);
lean_dec(v___x_298_);
v___x_304_ = lean_unsigned_to_nat(3u);
v___x_305_ = lean_nat_mul(v___x_299_, v___x_304_);
v___x_306_ = lean_nat_dec_le(v___x_303_, v___x_305_);
lean_dec(v___x_305_);
lean_dec(v___x_303_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_163_, v_inst_164_, v_histogram_165_);
v___y_255_ = v___x_307_;
goto v___jp_254_;
}
else
{
v___y_255_ = v_histogram_165_;
goto v___jp_254_;
}
}
}
}
v___jp_248_:
{
lean_object* v_size_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_size_251_ = lean_ctor_get(v___y_249_, 0);
v___x_252_ = lean_nat_add(v_size_251_, v___x_242_);
v___x_253_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_249_, v___x_252_, v_i_250_, v_val_167_, v___x_247_);
lean_dec(v_i_250_);
return v___x_253_;
}
v___jp_254_:
{
lean_object* v___x_256_; 
lean_inc(v_val_167_);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_163_, v_inst_164_, v___y_255_, v_val_167_);
switch(lean_obj_tag(v___x_256_))
{
case 0:
{
lean_object* v_index_257_; lean_object* v_size_258_; lean_object* v___x_259_; 
v_index_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_index_257_);
lean_dec_ref_known(v___x_256_, 3);
v_size_258_ = lean_ctor_get(v___y_255_, 0);
lean_inc(v_size_258_);
v___x_259_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_255_, v_size_258_, v_index_257_, v_val_167_, v___x_247_);
lean_dec(v_index_257_);
return v___x_259_;
}
case 1:
{
lean_object* v_index_260_; 
v_index_260_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_index_260_);
lean_dec_ref_known(v___x_256_, 1);
v___y_249_ = v___y_255_;
v_i_250_ = v_index_260_;
goto v___jp_248_;
}
default: 
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_255_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_index_263_; 
v_index_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_index_263_);
lean_dec_ref_known(v___x_262_, 1);
v___y_249_ = v___y_255_;
v_i_250_ = v_index_263_;
goto v___jp_248_;
}
else
{
lean_dec_ref(v___x_247_);
lean_dec(v_val_167_);
return v___y_255_;
}
}
}
}
v___jp_264_:
{
lean_object* v_size_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_size_267_ = lean_ctor_get(v___y_265_, 0);
v___x_268_ = lean_nat_add(v_size_267_, v___x_242_);
v___x_269_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_265_, v___x_268_, v_i_266_, v_val_167_, v___x_247_);
lean_dec(v_i_266_);
return v___x_269_;
}
v___jp_270_:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_inc_ref(v_inst_164_);
lean_inc_ref(v_inst_163_);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_163_, v_inst_164_, v_histogram_165_);
lean_inc(v_val_167_);
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_163_, v_inst_164_, v___x_271_, v_val_167_);
switch(lean_obj_tag(v___x_272_))
{
case 0:
{
lean_object* v_index_273_; lean_object* v_size_274_; lean_object* v___x_275_; 
v_index_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_index_273_);
lean_dec_ref_known(v___x_272_, 3);
v_size_274_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_size_274_);
v___x_275_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_271_, v_size_274_, v_index_273_, v_val_167_, v___x_247_);
lean_dec(v_index_273_);
return v___x_275_;
}
case 1:
{
lean_object* v_index_276_; 
v_index_276_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_index_276_);
lean_dec_ref_known(v___x_272_, 1);
v___y_265_ = v___x_271_;
v_i_266_ = v_index_276_;
goto v___jp_264_;
}
default: 
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_271_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_index_279_; 
v_index_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_index_279_);
lean_dec_ref_known(v___x_278_, 1);
v___y_265_ = v___x_271_;
v_i_266_ = v_index_279_;
goto v___jp_264_;
}
else
{
lean_dec_ref(v___x_247_);
lean_dec(v_val_167_);
return v___x_271_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft(lean_object* v_00_u03b1_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_lsize_316_, lean_object* v_rsize_317_, lean_object* v_histogram_318_, lean_object* v_index_319_, lean_object* v_val_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_314_, v_inst_315_, v_histogram_318_, v_index_319_, v_val_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___boxed(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_lsize_325_, lean_object* v_rsize_326_, lean_object* v_histogram_327_, lean_object* v_index_328_, lean_object* v_val_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Diff_Histogram_addLeft(v_00_u03b1_322_, v_inst_323_, v_inst_324_, v_lsize_325_, v_rsize_326_, v_histogram_327_, v_index_328_, v_val_329_);
lean_dec(v_rsize_326_);
lean_dec(v_lsize_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___redArg(lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_histogram_333_, lean_object* v_index_334_, lean_object* v_val_335_){
_start:
{
lean_object* v___x_336_; 
lean_inc(v_val_335_);
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_331_, v_inst_332_, v_histogram_333_, v_val_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___y_343_; lean_object* v_i_344_; lean_object* v___y_349_; lean_object* v___y_358_; lean_object* v_i_359_; lean_object* v___x_372_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_box(0);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v_index_334_);
v___x_341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_341_, 0, v___x_337_);
lean_ctor_set(v___x_341_, 1, v___x_338_);
lean_ctor_set(v___x_341_, 2, v___x_339_);
lean_ctor_set(v___x_341_, 3, v___x_340_);
lean_inc(v_val_335_);
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_331_, v_inst_332_, v_histogram_333_, v_val_335_);
switch(lean_obj_tag(v___x_372_))
{
case 0:
{
lean_object* v_index_373_; lean_object* v_size_374_; lean_object* v___x_375_; 
lean_dec_ref(v_inst_332_);
lean_dec_ref(v_inst_331_);
v_index_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_index_373_);
lean_dec_ref_known(v___x_372_, 3);
v_size_374_ = lean_ctor_get(v_histogram_333_, 0);
lean_inc(v_size_374_);
v___x_375_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_333_, v_size_374_, v_index_373_, v_val_335_, v___x_341_);
lean_dec(v_index_373_);
return v___x_375_;
}
case 1:
{
lean_object* v_index_376_; lean_object* v_size_377_; lean_object* v_keyArray_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_index_376_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_index_376_);
lean_dec_ref_known(v___x_372_, 1);
v_size_377_ = lean_ctor_get(v_histogram_333_, 0);
v_keyArray_378_ = lean_ctor_get(v_histogram_333_, 1);
v___x_379_ = lean_nat_add(v_size_377_, v___x_339_);
v___x_380_ = lean_array_get_size(v_keyArray_378_);
v___x_381_ = lean_nat_dec_lt(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_dec(v___x_379_);
lean_dec(v_index_376_);
goto v___jp_363_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_382_ = lean_unsigned_to_nat(4u);
v___x_383_ = lean_nat_mul(v___x_379_, v___x_382_);
v___x_384_ = lean_unsigned_to_nat(3u);
v___x_385_ = lean_nat_mul(v___x_380_, v___x_384_);
v___x_386_ = lean_nat_dec_le(v___x_383_, v___x_385_);
lean_dec(v___x_385_);
lean_dec(v___x_383_);
if (v___x_386_ == 0)
{
lean_dec(v___x_379_);
lean_dec(v_index_376_);
goto v___jp_363_;
}
else
{
lean_object* v___x_387_; 
lean_dec_ref(v_inst_332_);
lean_dec_ref(v_inst_331_);
v___x_387_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_333_, v___x_379_, v_index_376_, v_val_335_, v___x_341_);
lean_dec(v_index_376_);
return v___x_387_;
}
}
}
default: 
{
lean_object* v_size_388_; lean_object* v_keyArray_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_size_388_ = lean_ctor_get(v_histogram_333_, 0);
v_keyArray_389_ = lean_ctor_get(v_histogram_333_, 1);
v___x_390_ = lean_nat_add(v_size_388_, v___x_339_);
v___x_391_ = lean_array_get_size(v_keyArray_389_);
v___x_392_ = lean_nat_dec_lt(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v___x_390_);
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_331_, v_inst_332_, v_histogram_333_);
v___y_349_ = v___x_393_;
goto v___jp_348_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_394_ = lean_unsigned_to_nat(4u);
v___x_395_ = lean_nat_mul(v___x_390_, v___x_394_);
lean_dec(v___x_390_);
v___x_396_ = lean_unsigned_to_nat(3u);
v___x_397_ = lean_nat_mul(v___x_391_, v___x_396_);
v___x_398_ = lean_nat_dec_le(v___x_395_, v___x_397_);
lean_dec(v___x_397_);
lean_dec(v___x_395_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_331_, v_inst_332_, v_histogram_333_);
v___y_349_ = v___x_399_;
goto v___jp_348_;
}
else
{
v___y_349_ = v_histogram_333_;
goto v___jp_348_;
}
}
}
}
v___jp_342_:
{
lean_object* v_size_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_size_345_ = lean_ctor_get(v___y_343_, 0);
v___x_346_ = lean_nat_add(v_size_345_, v___x_339_);
v___x_347_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_343_, v___x_346_, v_i_344_, v_val_335_, v___x_341_);
lean_dec(v_i_344_);
return v___x_347_;
}
v___jp_348_:
{
lean_object* v___x_350_; 
lean_inc(v_val_335_);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_331_, v_inst_332_, v___y_349_, v_val_335_);
switch(lean_obj_tag(v___x_350_))
{
case 0:
{
lean_object* v_index_351_; lean_object* v_size_352_; lean_object* v___x_353_; 
v_index_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_index_351_);
lean_dec_ref_known(v___x_350_, 3);
v_size_352_ = lean_ctor_get(v___y_349_, 0);
lean_inc(v_size_352_);
v___x_353_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_349_, v_size_352_, v_index_351_, v_val_335_, v___x_341_);
lean_dec(v_index_351_);
return v___x_353_;
}
case 1:
{
lean_object* v_index_354_; 
v_index_354_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_index_354_);
lean_dec_ref_known(v___x_350_, 1);
v___y_343_ = v___y_349_;
v_i_344_ = v_index_354_;
goto v___jp_342_;
}
default: 
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_349_, v___x_337_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_index_356_; 
v_index_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_index_356_);
lean_dec_ref_known(v___x_355_, 1);
v___y_343_ = v___y_349_;
v_i_344_ = v_index_356_;
goto v___jp_342_;
}
else
{
lean_dec_ref_known(v___x_341_, 4);
lean_dec(v_val_335_);
return v___y_349_;
}
}
}
}
v___jp_357_:
{
lean_object* v_size_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_size_360_ = lean_ctor_get(v___y_358_, 0);
v___x_361_ = lean_nat_add(v_size_360_, v___x_339_);
v___x_362_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_358_, v___x_361_, v_i_359_, v_val_335_, v___x_341_);
lean_dec(v_i_359_);
return v___x_362_;
}
v___jp_363_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_331_, v_inst_332_, v_histogram_333_);
lean_inc(v_val_335_);
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_331_, v_inst_332_, v___x_364_, v_val_335_);
switch(lean_obj_tag(v___x_365_))
{
case 0:
{
lean_object* v_index_366_; lean_object* v_size_367_; lean_object* v___x_368_; 
v_index_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_index_366_);
lean_dec_ref_known(v___x_365_, 3);
v_size_367_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_size_367_);
v___x_368_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_364_, v_size_367_, v_index_366_, v_val_335_, v___x_341_);
lean_dec(v_index_366_);
return v___x_368_;
}
case 1:
{
lean_object* v_index_369_; 
v_index_369_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_index_369_);
lean_dec_ref_known(v___x_365_, 1);
v___y_358_ = v___x_364_;
v_i_359_ = v_index_369_;
goto v___jp_357_;
}
default: 
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_364_, v___x_337_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_index_371_; 
v_index_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_index_371_);
lean_dec_ref_known(v___x_370_, 1);
v___y_358_ = v___x_364_;
v_i_359_ = v_index_371_;
goto v___jp_357_;
}
else
{
lean_dec_ref_known(v___x_341_, 4);
lean_dec(v_val_335_);
return v___x_364_;
}
}
}
}
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_480_; 
v_val_400_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_480_ == 0)
{
v___x_402_ = v___x_336_;
v_isShared_403_ = v_isSharedCheck_480_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v___x_336_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_480_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_leftCount_404_; lean_object* v_leftIndex_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_477_; 
v_leftCount_404_ = lean_ctor_get(v_val_400_, 0);
v_leftIndex_405_ = lean_ctor_get(v_val_400_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_val_400_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_478_ = lean_ctor_get(v_val_400_, 3);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_val_400_, 2);
lean_dec(v_unused_479_);
v___x_407_ = v_val_400_;
v_isShared_408_ = v_isSharedCheck_477_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_leftIndex_405_);
lean_inc(v_leftCount_404_);
lean_dec(v_val_400_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_477_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_leftCount_404_, v___x_409_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_index_334_);
v___x_412_ = v___x_402_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_index_334_);
v___x_412_ = v_reuseFailAlloc_476_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 3, v___x_412_);
lean_ctor_set(v___x_407_, 2, v___x_410_);
v___x_414_ = v___x_407_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_leftCount_404_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_leftIndex_405_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v___x_412_);
v___x_414_ = v_reuseFailAlloc_475_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___y_416_; lean_object* v_i_417_; lean_object* v___y_422_; lean_object* v___y_432_; lean_object* v_i_433_; lean_object* v___x_447_; 
lean_inc(v_val_335_);
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_331_, v_inst_332_, v_histogram_333_, v_val_335_);
switch(lean_obj_tag(v___x_447_))
{
case 0:
{
lean_object* v_index_448_; lean_object* v_size_449_; lean_object* v___x_450_; 
lean_dec_ref(v_inst_332_);
lean_dec_ref(v_inst_331_);
v_index_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_index_448_);
lean_dec_ref_known(v___x_447_, 3);
v_size_449_ = lean_ctor_get(v_histogram_333_, 0);
lean_inc(v_size_449_);
v___x_450_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_333_, v_size_449_, v_index_448_, v_val_335_, v___x_414_);
lean_dec(v_index_448_);
return v___x_450_;
}
case 1:
{
lean_object* v_index_451_; lean_object* v_size_452_; lean_object* v_keyArray_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_index_451_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_index_451_);
lean_dec_ref_known(v___x_447_, 1);
v_size_452_ = lean_ctor_get(v_histogram_333_, 0);
v_keyArray_453_ = lean_ctor_get(v_histogram_333_, 1);
v___x_454_ = lean_nat_add(v_size_452_, v___x_409_);
v___x_455_ = lean_array_get_size(v_keyArray_453_);
v___x_456_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec(v___x_454_);
lean_dec(v_index_451_);
goto v___jp_437_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_457_ = lean_unsigned_to_nat(4u);
v___x_458_ = lean_nat_mul(v___x_454_, v___x_457_);
v___x_459_ = lean_unsigned_to_nat(3u);
v___x_460_ = lean_nat_mul(v___x_455_, v___x_459_);
v___x_461_ = lean_nat_dec_le(v___x_458_, v___x_460_);
lean_dec(v___x_460_);
lean_dec(v___x_458_);
if (v___x_461_ == 0)
{
lean_dec(v___x_454_);
lean_dec(v_index_451_);
goto v___jp_437_;
}
else
{
lean_object* v___x_462_; 
lean_dec_ref(v_inst_332_);
lean_dec_ref(v_inst_331_);
v___x_462_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_333_, v___x_454_, v_index_451_, v_val_335_, v___x_414_);
lean_dec(v_index_451_);
return v___x_462_;
}
}
}
default: 
{
lean_object* v_size_463_; lean_object* v_keyArray_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_size_463_ = lean_ctor_get(v_histogram_333_, 0);
v_keyArray_464_ = lean_ctor_get(v_histogram_333_, 1);
v___x_465_ = lean_nat_add(v_size_463_, v___x_409_);
v___x_466_ = lean_array_get_size(v_keyArray_464_);
v___x_467_ = lean_nat_dec_lt(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v___x_465_);
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_331_, v_inst_332_, v_histogram_333_);
v___y_422_ = v___x_468_;
goto v___jp_421_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_469_ = lean_unsigned_to_nat(4u);
v___x_470_ = lean_nat_mul(v___x_465_, v___x_469_);
lean_dec(v___x_465_);
v___x_471_ = lean_unsigned_to_nat(3u);
v___x_472_ = lean_nat_mul(v___x_466_, v___x_471_);
v___x_473_ = lean_nat_dec_le(v___x_470_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_470_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_331_, v_inst_332_, v_histogram_333_);
v___y_422_ = v___x_474_;
goto v___jp_421_;
}
else
{
v___y_422_ = v_histogram_333_;
goto v___jp_421_;
}
}
}
}
v___jp_415_:
{
lean_object* v_size_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_size_418_ = lean_ctor_get(v___y_416_, 0);
v___x_419_ = lean_nat_add(v_size_418_, v___x_409_);
v___x_420_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_416_, v___x_419_, v_i_417_, v_val_335_, v___x_414_);
lean_dec(v_i_417_);
return v___x_420_;
}
v___jp_421_:
{
lean_object* v___x_423_; 
lean_inc(v_val_335_);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_331_, v_inst_332_, v___y_422_, v_val_335_);
switch(lean_obj_tag(v___x_423_))
{
case 0:
{
lean_object* v_index_424_; lean_object* v_size_425_; lean_object* v___x_426_; 
v_index_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_423_, 3);
v_size_425_ = lean_ctor_get(v___y_422_, 0);
lean_inc(v_size_425_);
v___x_426_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_422_, v_size_425_, v_index_424_, v_val_335_, v___x_414_);
lean_dec(v_index_424_);
return v___x_426_;
}
case 1:
{
lean_object* v_index_427_; 
v_index_427_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_427_);
lean_dec_ref_known(v___x_423_, 1);
v___y_416_ = v___y_422_;
v_i_417_ = v_index_427_;
goto v___jp_415_;
}
default: 
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_422_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_index_430_; 
v_index_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_index_430_);
lean_dec_ref_known(v___x_429_, 1);
v___y_416_ = v___y_422_;
v_i_417_ = v_index_430_;
goto v___jp_415_;
}
else
{
lean_dec_ref(v___x_414_);
lean_dec(v_val_335_);
return v___y_422_;
}
}
}
}
v___jp_431_:
{
lean_object* v_size_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_size_434_ = lean_ctor_get(v___y_432_, 0);
v___x_435_ = lean_nat_add(v_size_434_, v___x_409_);
v___x_436_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_432_, v___x_435_, v_i_433_, v_val_335_, v___x_414_);
lean_dec(v_i_433_);
return v___x_436_;
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_inc_ref(v_inst_332_);
lean_inc_ref(v_inst_331_);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_331_, v_inst_332_, v_histogram_333_);
lean_inc(v_val_335_);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_331_, v_inst_332_, v___x_438_, v_val_335_);
switch(lean_obj_tag(v___x_439_))
{
case 0:
{
lean_object* v_index_440_; lean_object* v_size_441_; lean_object* v___x_442_; 
v_index_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_440_);
lean_dec_ref_known(v___x_439_, 3);
v_size_441_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_size_441_);
v___x_442_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_438_, v_size_441_, v_index_440_, v_val_335_, v___x_414_);
lean_dec(v_index_440_);
return v___x_442_;
}
case 1:
{
lean_object* v_index_443_; 
v_index_443_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_439_, 1);
v___y_432_ = v___x_438_;
v_i_433_ = v_index_443_;
goto v___jp_431_;
}
default: 
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_438_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_index_446_; 
v_index_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_index_446_);
lean_dec_ref_known(v___x_445_, 1);
v___y_432_ = v___x_438_;
v_i_433_ = v_index_446_;
goto v___jp_431_;
}
else
{
lean_dec_ref(v___x_414_);
lean_dec(v_val_335_);
return v___x_438_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight(lean_object* v_00_u03b1_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_lsize_484_, lean_object* v_rsize_485_, lean_object* v_histogram_486_, lean_object* v_index_487_, lean_object* v_val_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_482_, v_inst_483_, v_histogram_486_, v_index_487_, v_val_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___boxed(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_lsize_493_, lean_object* v_rsize_494_, lean_object* v_histogram_495_, lean_object* v_index_496_, lean_object* v_val_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Diff_Histogram_addRight(v_00_u03b1_490_, v_inst_491_, v_inst_492_, v_lsize_493_, v_rsize_494_, v_histogram_495_, v_index_496_, v_val_497_);
lean_dec(v_rsize_494_);
lean_dec(v_lsize_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(lean_object* v_inst_499_, lean_object* v_left_500_, lean_object* v_right_501_, lean_object* v_pref_502_){
_start:
{
lean_object* v_start_503_; lean_object* v_stop_504_; lean_object* v_i_505_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_start_503_ = lean_ctor_get(v_left_500_, 1);
v_stop_504_ = lean_ctor_get(v_left_500_, 2);
v_i_505_ = lean_array_get_size(v_pref_502_);
v___x_511_ = lean_nat_sub(v_stop_504_, v_start_503_);
v___x_512_ = lean_nat_dec_lt(v_i_505_, v___x_511_);
lean_dec(v___x_511_);
if (v___x_512_ == 0)
{
lean_dec_ref(v_inst_499_);
goto v___jp_506_;
}
else
{
lean_object* v_start_513_; lean_object* v_stop_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_start_513_ = lean_ctor_get(v_right_501_, 1);
v_stop_514_ = lean_ctor_get(v_right_501_, 2);
v___x_515_ = lean_nat_sub(v_stop_514_, v_start_513_);
v___x_516_ = lean_nat_dec_lt(v_i_505_, v___x_515_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v_inst_499_);
goto v___jp_506_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_517_ = l_Subarray_get___redArg(v_left_500_, v_i_505_);
v___x_518_ = l_Subarray_get___redArg(v_right_501_, v_i_505_);
lean_inc_ref(v_inst_499_);
lean_inc(v___x_517_);
v___x_519_ = lean_apply_2(v_inst_499_, v___x_517_, v___x_518_);
v___x_520_ = lean_unbox(v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v___x_517_);
lean_dec_ref(v_inst_499_);
v___x_521_ = l_Subarray_drop___redArg(v_left_500_, v_i_505_);
v___x_522_ = l_Subarray_drop___redArg(v_right_501_, v_i_505_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_pref_502_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_array_push(v_pref_502_, v___x_517_);
v_pref_502_ = v___x_525_;
goto _start;
}
}
}
v___jp_506_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = l_Subarray_drop___redArg(v_left_500_, v_i_505_);
v___x_508_ = l_Subarray_drop___redArg(v_right_501_, v_i_505_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_pref_502_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(lean_object* v_00_u03b1_527_, lean_object* v_inst_528_, lean_object* v_left_529_, lean_object* v_right_530_, lean_object* v_pref_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_528_, v_left_529_, v_right_530_, v_pref_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___redArg(lean_object* v_inst_535_, lean_object* v_left_536_, lean_object* v_right_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_539_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_535_, v_left_536_, v_right_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix(lean_object* v_00_u03b1_540_, lean_object* v_inst_541_, lean_object* v_left_542_, lean_object* v_right_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Diff_matchPrefix___redArg(v_inst_541_, v_left_542_, v_right_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(lean_object* v_it_545_, lean_object* v_acc_546_, lean_object* v_recur_547_){
_start:
{
lean_object* v_array_548_; lean_object* v_start_549_; lean_object* v_stop_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_563_; 
v_array_548_ = lean_ctor_get(v_it_545_, 0);
v_start_549_ = lean_ctor_get(v_it_545_, 1);
v_stop_550_ = lean_ctor_get(v_it_545_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v_it_545_);
if (v_isSharedCheck_563_ == 0)
{
v___x_552_ = v_it_545_;
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_stop_550_);
lean_inc(v_start_549_);
lean_inc(v_array_548_);
lean_dec(v_it_545_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_nat_dec_lt(v_start_549_, v_stop_550_);
if (v___x_554_ == 0)
{
lean_del_object(v___x_552_);
lean_dec(v_stop_550_);
lean_dec(v_start_549_);
lean_dec_ref(v_array_548_);
lean_dec_ref(v_recur_547_);
return v_acc_546_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_start_549_, v___x_555_);
lean_inc_ref(v_array_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_556_);
v___x_558_ = v___x_552_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_array_548_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_stop_550_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_array_fget(v_array_548_, v_start_549_);
lean_dec(v_start_549_);
lean_dec_ref(v_array_548_);
v___x_560_ = lean_array_push(v_acc_546_, v___x_559_);
v___x_561_ = lean_apply_3(v_recur_547_, v___x_558_, v___x_560_, lean_box(0));
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(lean_object* v_inst_565_, lean_object* v_left_566_, lean_object* v_right_567_, lean_object* v_i_568_){
_start:
{
lean_object* v_start_569_; lean_object* v_stop_570_; lean_object* v___f_571_; lean_object* v___x_572_; uint8_t v___x_586_; 
v_start_569_ = lean_ctor_get(v_left_566_, 1);
v_stop_570_ = lean_ctor_get(v_left_566_, 2);
v___f_571_ = ((lean_object*)(l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0));
v___x_572_ = lean_nat_sub(v_stop_570_, v_start_569_);
v___x_586_ = lean_nat_dec_lt(v_i_568_, v___x_572_);
if (v___x_586_ == 0)
{
lean_dec_ref(v_inst_565_);
goto v___jp_573_;
}
else
{
lean_object* v_start_587_; lean_object* v_stop_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_start_587_ = lean_ctor_get(v_right_567_, 1);
v_stop_588_ = lean_ctor_get(v_right_567_, 2);
v___x_589_ = lean_nat_sub(v_stop_588_, v_start_587_);
v___x_590_ = lean_nat_dec_lt(v_i_568_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec(v___x_589_);
lean_dec_ref(v_inst_565_);
goto v___jp_573_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_591_ = lean_nat_sub(v___x_572_, v_i_568_);
lean_dec(v___x_572_);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_sub(v___x_591_, v___x_592_);
v___x_594_ = l_Subarray_get___redArg(v_left_566_, v___x_593_);
lean_dec(v___x_593_);
v___x_595_ = lean_nat_sub(v___x_589_, v_i_568_);
lean_dec(v___x_589_);
v___x_596_ = lean_nat_sub(v___x_595_, v___x_592_);
v___x_597_ = l_Subarray_get___redArg(v_right_567_, v___x_596_);
lean_dec(v___x_596_);
lean_inc_ref(v_inst_565_);
v___x_598_ = lean_apply_2(v_inst_565_, v___x_594_, v___x_597_);
v___x_599_ = lean_unbox(v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_i_568_);
lean_dec_ref(v_inst_565_);
lean_inc_ref(v_left_566_);
v___x_600_ = l_Subarray_take___redArg(v_left_566_, v___x_591_);
v___x_601_ = l_Subarray_take___redArg(v_right_567_, v___x_595_);
lean_dec(v___x_595_);
v___x_602_ = l_Subarray_drop___redArg(v_left_566_, v___x_591_);
lean_dec(v___x_591_);
v___x_603_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_604_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_571_, v___x_602_, v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_601_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_600_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; 
lean_dec(v___x_595_);
lean_dec(v___x_591_);
v___x_607_ = lean_nat_add(v_i_568_, v___x_592_);
lean_dec(v_i_568_);
v_i_568_ = v___x_607_;
goto _start;
}
}
}
v___jp_573_:
{
lean_object* v_start_574_; lean_object* v_stop_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_start_574_ = lean_ctor_get(v_right_567_, 1);
v_stop_575_ = lean_ctor_get(v_right_567_, 2);
v___x_576_ = lean_nat_sub(v___x_572_, v_i_568_);
lean_dec(v___x_572_);
lean_inc_ref(v_left_566_);
v___x_577_ = l_Subarray_take___redArg(v_left_566_, v___x_576_);
v___x_578_ = lean_nat_sub(v_stop_575_, v_start_574_);
v___x_579_ = lean_nat_sub(v___x_578_, v_i_568_);
lean_dec(v_i_568_);
lean_dec(v___x_578_);
v___x_580_ = l_Subarray_take___redArg(v_right_567_, v___x_579_);
lean_dec(v___x_579_);
v___x_581_ = l_Subarray_drop___redArg(v_left_566_, v___x_576_);
lean_dec(v___x_576_);
v___x_582_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_583_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_571_, v___x_581_, v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_577_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object* v_00_u03b1_609_, lean_object* v_inst_610_, lean_object* v_left_611_, lean_object* v_right_612_, lean_object* v_i_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_610_, v_left_611_, v_right_612_, v_i_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object* v_inst_615_, lean_object* v_left_616_, lean_object* v_right_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_615_, v_left_616_, v_right_617_, v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object* v_00_u03b1_620_, lean_object* v_inst_621_, lean_object* v_left_622_, lean_object* v_right_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Diff_matchSuffix___redArg(v_inst_621_, v_left_622_, v_right_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object* v_x1_625_, lean_object* v_x2_626_, lean_object* v_x3_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_x2_626_);
lean_ctor_set(v___x_628_, 1, v_x3_627_);
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_x1_625_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object* v_a_630_, lean_object* v_x_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_snd_633_; lean_object* v_leftIndex_634_; 
v_snd_633_ = lean_ctor_get(v_a_630_, 1);
lean_inc(v_snd_633_);
v_leftIndex_634_ = lean_ctor_get(v_snd_633_, 1);
lean_inc(v_leftIndex_634_);
if (lean_obj_tag(v_leftIndex_634_) == 1)
{
lean_object* v_rightIndex_635_; 
v_rightIndex_635_ = lean_ctor_get(v_snd_633_, 3);
lean_inc(v_rightIndex_635_);
if (lean_obj_tag(v_rightIndex_635_) == 1)
{
if (lean_obj_tag(v___y_632_) == 0)
{
lean_object* v_fst_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_664_; 
v_fst_636_ = lean_ctor_get(v_a_630_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_a_630_, 1);
lean_dec(v_unused_665_);
v___x_638_ = v_a_630_;
v_isShared_639_ = v_isSharedCheck_664_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_fst_636_);
lean_dec(v_a_630_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_664_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_leftCount_640_; lean_object* v_rightCount_641_; lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_663_; 
v_leftCount_640_ = lean_ctor_get(v_snd_633_, 0);
lean_inc(v_leftCount_640_);
v_rightCount_641_ = lean_ctor_get(v_snd_633_, 2);
lean_inc(v_rightCount_641_);
lean_dec(v_snd_633_);
v_val_642_ = lean_ctor_get(v_leftIndex_634_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_leftIndex_634_);
if (v_isSharedCheck_663_ == 0)
{
v___x_644_ = v_leftIndex_634_;
v_isShared_645_ = v_isSharedCheck_663_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_dec(v_leftIndex_634_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_663_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_val_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_662_; 
v_val_646_ = lean_ctor_get(v_rightIndex_635_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_rightIndex_635_);
if (v_isSharedCheck_662_ == 0)
{
v___x_648_ = v_rightIndex_635_;
v_isShared_649_ = v_isSharedCheck_662_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_val_646_);
lean_dec(v_rightIndex_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_662_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_nat_add(v_leftCount_640_, v_rightCount_641_);
lean_dec(v_rightCount_641_);
lean_dec(v_leftCount_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v_val_646_);
lean_ctor_set(v___x_638_, 0, v_val_642_);
v___x_652_ = v___x_638_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_val_642_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_val_646_);
v___x_652_ = v_reuseFailAlloc_661_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_fst_636_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_650_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_654_);
v___x_656_ = v___x_648_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_660_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_656_);
v___x_658_ = v___x_644_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_666_; lean_object* v_fst_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_708_; 
v_val_666_ = lean_ctor_get(v___y_632_, 0);
lean_inc(v_val_666_);
v_fst_667_ = lean_ctor_get(v_a_630_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_a_630_, 1);
lean_dec(v_unused_709_);
v___x_669_ = v_a_630_;
v_isShared_670_ = v_isSharedCheck_708_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_fst_667_);
lean_dec(v_a_630_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_708_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_leftCount_671_; lean_object* v_rightCount_672_; lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_707_; 
v_leftCount_671_ = lean_ctor_get(v_snd_633_, 0);
lean_inc(v_leftCount_671_);
v_rightCount_672_ = lean_ctor_get(v_snd_633_, 2);
lean_inc(v_rightCount_672_);
lean_dec(v_snd_633_);
v_val_673_ = lean_ctor_get(v_leftIndex_634_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_leftIndex_634_);
if (v_isSharedCheck_707_ == 0)
{
v___x_675_ = v_leftIndex_634_;
v_isShared_676_ = v_isSharedCheck_707_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_dec(v_leftIndex_634_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_707_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_val_677_; lean_object* v_fst_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_705_; 
v_val_677_ = lean_ctor_get(v_rightIndex_635_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_rightIndex_635_, 1);
v_fst_678_ = lean_ctor_get(v_val_666_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_val_666_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_val_666_, 1);
lean_dec(v_unused_706_);
v___x_680_ = v_val_666_;
v_isShared_681_ = v_isSharedCheck_705_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_fst_678_);
lean_dec(v_val_666_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_705_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_nat_add(v_leftCount_671_, v_rightCount_672_);
lean_dec(v_rightCount_672_);
lean_dec(v_leftCount_671_);
v___x_683_ = lean_nat_dec_lt(v___x_682_, v_fst_678_);
lean_dec(v_fst_678_);
if (v___x_683_ == 0)
{
lean_object* v___x_685_; 
lean_dec(v___x_682_);
lean_del_object(v___x_680_);
lean_dec(v_val_677_);
lean_dec(v_val_673_);
lean_del_object(v___x_669_);
lean_dec(v_fst_667_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___y_632_);
v___x_685_ = v___x_675_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___y_632_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
else
{
lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_703_; 
v_isSharedCheck_703_ = !lean_is_exclusive(v___y_632_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___y_632_, 0);
lean_dec(v_unused_704_);
v___x_688_ = v___y_632_;
v_isShared_689_ = v_isSharedCheck_703_;
goto v_resetjp_687_;
}
else
{
lean_dec(v___y_632_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_703_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_val_677_);
lean_ctor_set(v___x_680_, 0, v_val_673_);
v___x_691_ = v___x_680_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_val_673_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_val_677_);
v___x_691_ = v_reuseFailAlloc_702_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_691_);
v___x_693_ = v___x_669_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_701_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_682_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_694_);
v___x_696_ = v___x_688_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_696_);
v___x_698_ = v___x_675_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_rightIndex_635_);
lean_dec(v_snd_633_);
lean_dec_ref(v_a_630_);
v_isSharedCheck_716_ = !lean_is_exclusive(v_leftIndex_634_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v_leftIndex_634_, 0);
lean_dec(v_unused_717_);
v___x_711_ = v_leftIndex_634_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_dec(v_leftIndex_634_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___y_632_);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___y_632_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v___x_718_; 
lean_dec(v_leftIndex_634_);
lean_dec(v_snd_633_);
lean_dec_ref(v_a_630_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___y_632_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object* v___x_719_, lean_object* v_fst_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_next_723_, lean_object* v_acc_724_, lean_object* v_h_725_, lean_object* v_G_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_nat_dec_lt(v_next_723_, v___x_719_);
if (v___x_727_ == 0)
{
lean_dec_ref(v_G_726_);
lean_dec(v_next_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_inst_721_);
return v_acc_724_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_728_ = l_Subarray_get___redArg(v_fst_720_, v_next_723_);
lean_inc(v_next_723_);
v___x_729_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_721_, v_inst_722_, v_acc_724_, v_next_723_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_next_723_, v___x_730_);
lean_dec(v_next_723_);
v___x_732_ = lean_apply_4(v_G_726_, v___x_731_, v___x_729_, lean_box(0), lean_box(0));
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2___boxed(lean_object* v___x_733_, lean_object* v_fst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_next_737_, lean_object* v_acc_738_, lean_object* v_h_739_, lean_object* v_G_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Diff_lcs___redArg___lam__2(v___x_733_, v_fst_734_, v_inst_735_, v_inst_736_, v_next_737_, v_acc_738_, v_h_739_, v_G_740_);
lean_dec_ref(v_fst_734_);
lean_dec(v___x_733_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object* v___x_742_, lean_object* v_fst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_next_746_, lean_object* v_acc_747_, lean_object* v_h_748_, lean_object* v_G_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_lt(v_next_746_, v___x_742_);
if (v___x_750_ == 0)
{
lean_dec_ref(v_G_749_);
lean_dec(v_next_746_);
lean_dec_ref(v_inst_745_);
lean_dec_ref(v_inst_744_);
return v_acc_747_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_751_ = l_Subarray_get___redArg(v_fst_743_, v_next_746_);
lean_inc(v_next_746_);
v___x_752_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_744_, v_inst_745_, v_acc_747_, v_next_746_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_next_746_, v___x_753_);
lean_dec(v_next_746_);
v___x_755_ = lean_apply_4(v_G_749_, v___x_754_, v___x_752_, lean_box(0), lean_box(0));
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3___boxed(lean_object* v___x_756_, lean_object* v_fst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_next_760_, lean_object* v_acc_761_, lean_object* v_h_762_, lean_object* v_G_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Diff_lcs___redArg___lam__3(v___x_756_, v_fst_757_, v_inst_758_, v_inst_759_, v_next_760_, v_acc_761_, v_h_762_, v_G_763_);
lean_dec_ref(v_fst_757_);
lean_dec(v___x_756_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__10(void){
_start:
{
lean_object* v_cellCount_784_; lean_object* v___x_785_; 
v_cellCount_784_ = lean_unsigned_to_nat(16u);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__11(void){
_start:
{
lean_object* v_cellCount_786_; lean_object* v___x_787_; 
v_cellCount_786_ = lean_unsigned_to_nat(16u);
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__12(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_hist_791_; 
v___x_788_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__11, &l_Lean_Diff_lcs___redArg___closed__11_once, _init_l_Lean_Diff_lcs___redArg___closed__11);
v___x_789_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__10, &l_Lean_Diff_lcs___redArg___closed__10_once, _init_l_Lean_Diff_lcs___redArg___closed__10);
v___x_790_ = lean_unsigned_to_nat(0u);
v_hist_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hist_791_, 0, v___x_790_);
lean_ctor_set(v_hist_791_, 1, v___x_789_);
lean_ctor_set(v_hist_791_, 2, v___x_788_);
return v_hist_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_left_796_, lean_object* v_right_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_snd_800_; lean_object* v_fst_801_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_804_; lean_object* v_snd_805_; lean_object* v_fst_806_; lean_object* v_fst_807_; lean_object* v_snd_808_; lean_object* v_start_809_; lean_object* v_stop_810_; lean_object* v_start_811_; lean_object* v_stop_812_; lean_object* v___x_813_; lean_object* v_hist_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_798_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
lean_inc_ref_n(v_inst_794_, 4);
v___x_799_ = l_Lean_Diff_matchPrefix___redArg(v_inst_794_, v_left_796_, v_right_797_);
v_snd_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_snd_800_);
v_fst_801_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_fst_801_);
lean_dec_ref(v___x_799_);
v_fst_802_ = lean_ctor_get(v_snd_800_, 0);
lean_inc(v_fst_802_);
v_snd_803_ = lean_ctor_get(v_snd_800_, 1);
lean_inc(v_snd_803_);
lean_dec(v_snd_800_);
v___x_804_ = l_Lean_Diff_matchSuffix___redArg(v_inst_794_, v_fst_802_, v_snd_803_);
v_snd_805_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_snd_805_);
v_fst_806_ = lean_ctor_get(v___x_804_, 0);
lean_inc_n(v_fst_806_, 2);
lean_dec_ref(v___x_804_);
v_fst_807_ = lean_ctor_get(v_snd_805_, 0);
lean_inc_n(v_fst_807_, 2);
v_snd_808_ = lean_ctor_get(v_snd_805_, 1);
lean_inc(v_snd_808_);
lean_dec(v_snd_805_);
v_start_809_ = lean_ctor_get(v_fst_806_, 1);
v_stop_810_ = lean_ctor_get(v_fst_806_, 2);
v_start_811_ = lean_ctor_get(v_fst_807_, 1);
v_stop_812_ = lean_ctor_get(v_fst_807_, 2);
v___x_813_ = lean_unsigned_to_nat(0u);
v_hist_814_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__12, &l_Lean_Diff_lcs___redArg___closed__12_once, _init_l_Lean_Diff_lcs___redArg___closed__12);
v___f_815_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__13));
v___f_816_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__14));
v___x_817_ = lean_nat_sub(v_stop_810_, v_start_809_);
lean_inc_ref_n(v_inst_795_, 2);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__2___boxed), 8, 4);
lean_closure_set(v___f_818_, 0, v___x_817_);
lean_closure_set(v___f_818_, 1, v_fst_806_);
lean_closure_set(v___f_818_, 2, v_inst_794_);
lean_closure_set(v___f_818_, 3, v_inst_795_);
v___x_819_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_818_, v___x_813_, v_hist_814_, lean_box(0));
v___x_820_ = lean_nat_sub(v_stop_812_, v_start_811_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__3___boxed), 8, 4);
lean_closure_set(v___f_821_, 0, v___x_820_);
lean_closure_set(v___f_821_, 1, v_fst_807_);
lean_closure_set(v___f_821_, 2, v_inst_794_);
lean_closure_set(v___f_821_, 3, v_inst_795_);
v___x_822_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_821_, v___x_813_, v___x_819_, lean_box(0));
v___x_823_ = lean_box(0);
v___x_824_ = lean_box(0);
v___x_825_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_798_, v___f_815_, v___x_822_, v___x_824_, v___x_813_);
lean_dec(v___x_822_);
v___x_826_ = l_List_forIn_x27_loop___redArg(v___x_798_, v___f_816_, v___x_825_, v___x_823_);
lean_dec(v___x_825_);
if (lean_obj_tag(v___x_826_) == 1)
{
lean_object* v_val_827_; lean_object* v_snd_828_; lean_object* v_snd_829_; lean_object* v_fst_830_; lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_833_; lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v___x_836_; lean_object* v_fst_837_; lean_object* v_snd_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_val_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v___x_826_, 1);
v_snd_828_ = lean_ctor_get(v_val_827_, 1);
lean_inc(v_snd_828_);
lean_dec(v_val_827_);
v_snd_829_ = lean_ctor_get(v_snd_828_, 1);
lean_inc(v_snd_829_);
v_fst_830_ = lean_ctor_get(v_snd_828_, 0);
lean_inc(v_fst_830_);
lean_dec(v_snd_828_);
v_fst_831_ = lean_ctor_get(v_snd_829_, 0);
lean_inc(v_fst_831_);
v_snd_832_ = lean_ctor_get(v_snd_829_, 1);
lean_inc(v_snd_832_);
lean_dec(v_snd_829_);
v___x_833_ = l_Subarray_split___redArg(v_fst_806_, v_fst_831_);
lean_dec(v_fst_831_);
v_fst_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_fst_834_);
v_snd_835_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_snd_835_);
lean_dec_ref(v___x_833_);
v___x_836_ = l_Subarray_split___redArg(v_fst_807_, v_snd_832_);
lean_dec(v_snd_832_);
v_fst_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_fst_837_);
v_snd_838_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_snd_838_);
lean_dec_ref(v___x_836_);
lean_inc_ref(v_inst_795_);
lean_inc_ref(v_inst_794_);
v___x_839_ = l_Lean_Diff_lcs___redArg(v_inst_794_, v_inst_795_, v_fst_834_, v_fst_837_);
v___x_840_ = l_Array_append___redArg(v_fst_801_, v___x_839_);
lean_dec_ref(v___x_839_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_mk_empty_array_with_capacity(v___x_841_);
v___x_843_ = lean_array_push(v___x_842_, v_fst_830_);
v___x_844_ = l_Array_append___redArg(v___x_840_, v___x_843_);
lean_dec_ref(v___x_843_);
v___x_845_ = l_Subarray_drop___redArg(v_snd_835_, v___x_841_);
v___x_846_ = l_Subarray_drop___redArg(v_snd_838_, v___x_841_);
v___x_847_ = l_Lean_Diff_lcs___redArg(v_inst_794_, v_inst_795_, v___x_845_, v___x_846_);
v___x_848_ = l_Array_append___redArg(v___x_844_, v___x_847_);
lean_dec_ref(v___x_847_);
v___x_849_ = l_Array_append___redArg(v___x_848_, v_snd_808_);
lean_dec(v_snd_808_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; 
lean_dec(v___x_826_);
lean_dec(v_fst_807_);
lean_dec(v_fst_806_);
lean_dec_ref(v_inst_795_);
lean_dec_ref(v_inst_794_);
v___x_850_ = l_Array_append___redArg(v_fst_801_, v_snd_808_);
lean_dec(v_snd_808_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object* v_00_u03b1_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_left_854_, lean_object* v_right_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Diff_lcs___redArg(v_inst_852_, v_inst_853_, v_left_854_, v_right_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object* v_x_857_){
_start:
{
uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = 0;
v___x_859_ = lean_box(v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_x_857_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object* v_x_861_){
_start:
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = 1;
v___x_863_ = lean_box(v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v_x_861_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object* v_inst_865_, lean_object* v_original_866_, lean_object* v___x_867_, lean_object* v_inst_868_, lean_object* v_a_869_, lean_object* v_b_870_){
_start:
{
lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_896_; 
v_fst_871_ = lean_ctor_get(v_b_870_, 0);
v_snd_872_ = lean_ctor_get(v_b_870_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_b_870_);
if (v_isSharedCheck_896_ == 0)
{
v___x_874_ = v_b_870_;
v_isShared_875_ = v_isSharedCheck_896_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
lean_dec(v_b_870_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_896_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
uint8_t v___y_882_; uint8_t v___x_892_; 
v___x_892_ = lean_nat_dec_lt(v_snd_872_, v___x_867_);
if (v___x_892_ == 0)
{
lean_dec(v_a_869_);
lean_dec_ref(v_inst_868_);
v___y_882_ = v___x_892_;
goto v___jp_881_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_array_get_borrowed(v_inst_865_, v_original_866_, v_snd_872_);
lean_inc(v___x_893_);
v___x_894_ = lean_apply_2(v_inst_868_, v___x_893_, v_a_869_);
v___x_895_ = lean_unbox(v___x_894_);
if (v___x_895_ == 0)
{
v___y_882_ = v___x_892_;
goto v___jp_881_;
}
else
{
goto v___jp_876_;
}
}
v___jp_876_:
{
lean_object* v___x_878_; 
if (v_isShared_875_ == 0)
{
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_871_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_snd_872_);
v___x_878_ = v_reuseFailAlloc_880_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
v___jp_881_:
{
if (v___y_882_ == 0)
{
goto v___jp_876_;
}
else
{
uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_874_);
v___x_883_ = 1;
v___x_884_ = lean_array_get_borrowed(v_inst_865_, v_original_866_, v_snd_872_);
v___x_885_ = lean_box(v___x_883_);
lean_inc(v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
v___x_887_ = lean_array_push(v_fst_871_, v___x_886_);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_snd_872_, v___x_888_);
lean_dec(v_snd_872_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_887_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object* v_inst_897_, lean_object* v_original_898_, lean_object* v___x_899_, lean_object* v_inst_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Diff_diff___redArg___lam__2(v_inst_897_, v_original_898_, v___x_899_, v_inst_900_, v_a_901_, v_b_902_);
lean_dec(v___x_899_);
lean_dec_ref(v_original_898_);
lean_dec(v_inst_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object* v_inst_904_, lean_object* v_edited_905_, lean_object* v___x_906_, lean_object* v_inst_907_, lean_object* v_a_908_, lean_object* v_b_909_){
_start:
{
lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_935_; 
v_fst_910_ = lean_ctor_get(v_b_909_, 0);
v_snd_911_ = lean_ctor_get(v_b_909_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_b_909_);
if (v_isSharedCheck_935_ == 0)
{
v___x_913_ = v_b_909_;
v_isShared_914_ = v_isSharedCheck_935_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snd_911_);
lean_inc(v_fst_910_);
lean_dec(v_b_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_935_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___y_921_; uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_lt(v_snd_911_, v___x_906_);
if (v___x_931_ == 0)
{
lean_dec(v_a_908_);
lean_dec_ref(v_inst_907_);
v___y_921_ = v___x_931_;
goto v___jp_920_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_array_get_borrowed(v_inst_904_, v_edited_905_, v_snd_911_);
lean_inc(v___x_932_);
v___x_933_ = lean_apply_2(v_inst_907_, v___x_932_, v_a_908_);
v___x_934_ = lean_unbox(v___x_933_);
if (v___x_934_ == 0)
{
v___y_921_ = v___x_931_;
goto v___jp_920_;
}
else
{
goto v___jp_915_;
}
}
v___jp_915_:
{
lean_object* v___x_917_; 
if (v_isShared_914_ == 0)
{
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_snd_911_);
v___x_917_ = v_reuseFailAlloc_919_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
v___jp_920_:
{
if (v___y_921_ == 0)
{
goto v___jp_915_;
}
else
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_del_object(v___x_913_);
v___x_922_ = 0;
v___x_923_ = lean_array_get_borrowed(v_inst_904_, v_edited_905_, v_snd_911_);
v___x_924_ = lean_box(v___x_922_);
lean_inc(v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
v___x_926_ = lean_array_push(v_fst_910_, v___x_925_);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_snd_911_, v___x_927_);
lean_dec(v_snd_911_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object* v_inst_936_, lean_object* v_edited_937_, lean_object* v___x_938_, lean_object* v_inst_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Diff_diff___redArg___lam__3(v_inst_936_, v_edited_937_, v___x_938_, v_inst_939_, v_a_940_, v_b_941_);
lean_dec(v___x_938_);
lean_dec_ref(v_edited_937_);
lean_dec(v_inst_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object* v_inst_943_, lean_object* v_original_944_, lean_object* v___x_945_, lean_object* v_inst_946_, lean_object* v___x_947_, lean_object* v_edited_948_, lean_object* v___x_949_, lean_object* v_a_950_, lean_object* v_x_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_snd_953_; lean_object* v_fst_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1000_; 
v_snd_953_ = lean_ctor_get(v___y_952_, 1);
v_fst_954_ = lean_ctor_get(v___y_952_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___y_952_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_956_ = v___y_952_;
v_isShared_957_ = v_isSharedCheck_1000_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_954_);
lean_dec(v___y_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1000_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_999_; 
v_fst_958_ = lean_ctor_get(v_snd_953_, 0);
v_snd_959_ = lean_ctor_get(v_snd_953_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_snd_953_);
if (v_isSharedCheck_999_ == 0)
{
v___x_961_ = v_snd_953_;
v_isShared_962_ = v_isSharedCheck_999_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v_snd_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_999_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___f_963_; lean_object* v___x_965_; 
lean_inc(v_a_950_);
lean_inc_ref(v_inst_946_);
lean_inc(v_inst_943_);
v___f_963_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_963_, 0, v_inst_943_);
lean_closure_set(v___f_963_, 1, v_original_944_);
lean_closure_set(v___f_963_, 2, v___x_945_);
lean_closure_set(v___f_963_, 3, v_inst_946_);
lean_closure_set(v___f_963_, 4, v_a_950_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v_fst_958_);
lean_ctor_set(v___x_961_, 0, v_fst_954_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fst_954_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_fst_958_);
v___x_965_ = v_reuseFailAlloc_998_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_997_; 
lean_inc_ref(v___x_947_);
v___x_966_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_947_, v___f_963_, v___x_965_);
v_fst_967_ = lean_ctor_get(v___x_966_, 0);
v_snd_968_ = lean_ctor_get(v___x_966_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_997_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_997_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_snd_968_);
lean_inc(v_fst_967_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_997_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___f_972_; lean_object* v___x_974_; 
lean_inc(v_a_950_);
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_972_, 0, v_inst_943_);
lean_closure_set(v___f_972_, 1, v_edited_948_);
lean_closure_set(v___f_972_, 2, v___x_949_);
lean_closure_set(v___f_972_, 3, v_inst_946_);
lean_closure_set(v___f_972_, 4, v_a_950_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v_snd_959_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_fst_967_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_snd_959_);
v___x_974_ = v_reuseFailAlloc_996_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_995_; 
v___x_975_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_947_, v___f_972_, v___x_974_);
v_fst_976_ = lean_ctor_get(v___x_975_, 0);
v_snd_977_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_995_ == 0)
{
v___x_979_ = v___x_975_;
v_isShared_980_ = v_isSharedCheck_995_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_inc(v_fst_976_);
lean_dec(v___x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_995_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_981_ = 2;
v___x_982_ = lean_box(v___x_981_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_a_950_);
lean_ctor_set(v___x_979_, 0, v___x_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_950_);
v___x_984_ = v_reuseFailAlloc_994_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_985_ = lean_array_push(v_fst_976_, v___x_984_);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_add(v_snd_968_, v___x_986_);
lean_dec(v_snd_968_);
v___x_988_ = lean_nat_add(v_snd_977_, v___x_986_);
lean_dec(v_snd_977_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_988_);
lean_ctor_set(v___x_956_, 0, v___x_987_);
v___x_990_ = v___x_956_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_985_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5(lean_object* v___x_1001_, lean_object* v_original_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1025_; 
v_fst_1004_ = lean_ctor_get(v_b_1003_, 0);
v_snd_1005_ = lean_ctor_get(v_b_1003_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_b_1003_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1007_ = v_b_1003_;
v_isShared_1008_ = v_isSharedCheck_1025_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_snd_1005_);
lean_inc(v_fst_1004_);
lean_dec(v_b_1003_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1025_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_lt(v_snd_1005_, v___x_1001_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1011_; 
if (v_isShared_1008_ == 0)
{
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_fst_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_snd_1005_);
v___x_1011_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
else
{
uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1014_ = 1;
v___x_1015_ = lean_array_fget_borrowed(v_original_1002_, v_snd_1005_);
v___x_1016_ = lean_box(v___x_1014_);
lean_inc(v___x_1015_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1015_);
lean_ctor_set(v___x_1007_, 0, v___x_1016_);
v___x_1018_ = v___x_1007_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1015_);
v___x_1018_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1019_ = lean_array_push(v_fst_1004_, v___x_1018_);
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_snd_1005_, v___x_1020_);
lean_dec(v_snd_1005_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1019_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5___boxed(lean_object* v___x_1026_, lean_object* v_original_1027_, lean_object* v_b_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Diff_diff___redArg___lam__5(v___x_1026_, v_original_1027_, v_b_1028_);
lean_dec_ref(v_original_1027_);
lean_dec(v___x_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6(lean_object* v___x_1030_, lean_object* v_edited_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1054_; 
v_fst_1033_ = lean_ctor_get(v_b_1032_, 0);
v_snd_1034_ = lean_ctor_get(v_b_1032_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_b_1032_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1036_ = v_b_1032_;
v_isShared_1037_ = v_isSharedCheck_1054_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_snd_1034_);
lean_inc(v_fst_1033_);
lean_dec(v_b_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1054_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_lt(v_snd_1034_, v___x_1030_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1040_; 
if (v_isShared_1037_ == 0)
{
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_fst_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_snd_1034_);
v___x_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
else
{
uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1043_ = 0;
v___x_1044_ = lean_array_fget_borrowed(v_edited_1031_, v_snd_1034_);
v___x_1045_ = lean_box(v___x_1043_);
lean_inc(v___x_1044_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1044_);
lean_ctor_set(v___x_1036_, 0, v___x_1045_);
v___x_1047_ = v___x_1036_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1044_);
v___x_1047_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = lean_array_push(v_fst_1033_, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_add(v_snd_1034_, v___x_1049_);
lean_dec(v_snd_1034_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1048_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6___boxed(lean_object* v___x_1055_, lean_object* v_edited_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Diff_diff___redArg___lam__6(v___x_1055_, v_edited_1056_, v_b_1057_);
lean_dec_ref(v_edited_1056_);
lean_dec(v___x_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_original_1071_, lean_object* v_edited_1072_){
_start:
{
lean_object* v_i_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_i_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_array_get_size(v_original_1071_);
v___x_1075_ = lean_nat_dec_lt(v_i_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___f_1076_; lean_object* v___x_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
lean_dec_ref(v_original_1071_);
lean_dec(v_inst_1070_);
lean_dec_ref(v_inst_1069_);
lean_dec_ref(v_inst_1068_);
v___f_1076_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__0));
v___x_1077_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_sz_1078_ = lean_array_size(v_edited_1072_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1077_, v___f_1076_, v_sz_1078_, v___x_1079_, v_edited_1072_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_array_get_size(v_edited_1072_);
v___x_1082_ = lean_nat_dec_lt(v_i_1073_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___f_1083_; lean_object* v___x_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref(v_edited_1072_);
lean_dec(v_inst_1070_);
lean_dec_ref(v_inst_1069_);
lean_dec_ref(v_inst_1068_);
v___f_1083_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__1));
v___x_1084_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_sz_1085_ = lean_array_size(v_original_1071_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1084_, v___f_1083_, v_sz_1085_, v___x_1086_, v_original_1071_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_ds_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; size_t v_sz_1094_; size_t v___x_1095_; lean_object* v___x_1096_; lean_object* v_snd_1097_; lean_object* v_fst_1098_; lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1121_; 
lean_inc_ref_n(v_original_1071_, 2);
v___x_1088_ = l_Array_toSubarray___redArg(v_original_1071_, v_i_1073_, v___x_1074_);
lean_inc_ref_n(v_edited_1072_, 2);
v___x_1089_ = l_Array_toSubarray___redArg(v_edited_1072_, v_i_1073_, v___x_1081_);
lean_inc_ref(v_inst_1068_);
v_ds_1090_ = l_Lean_Diff_lcs___redArg(v_inst_1068_, v_inst_1069_, v___x_1088_, v___x_1089_);
v___x_1091_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__4), 10, 7);
lean_closure_set(v___f_1092_, 0, v_inst_1070_);
lean_closure_set(v___f_1092_, 1, v_original_1071_);
lean_closure_set(v___f_1092_, 2, v___x_1074_);
lean_closure_set(v___f_1092_, 3, v_inst_1068_);
lean_closure_set(v___f_1092_, 4, v___x_1091_);
lean_closure_set(v___f_1092_, 5, v_edited_1072_);
lean_closure_set(v___f_1092_, 6, v___x_1081_);
v___x_1093_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__4));
v_sz_1094_ = lean_array_size(v_ds_1090_);
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1091_, v_ds_1090_, v___f_1092_, v_sz_1094_, v___x_1095_, v___x_1093_);
v_snd_1097_ = lean_ctor_get(v___x_1096_, 1);
lean_inc(v_snd_1097_);
v_fst_1098_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_fst_1098_);
lean_dec(v___x_1096_);
v_fst_1099_ = lean_ctor_get(v_snd_1097_, 0);
v_snd_1100_ = lean_ctor_get(v_snd_1097_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_snd_1097_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1102_ = v_snd_1097_;
v_isShared_1103_ = v_isSharedCheck_1121_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snd_1100_);
lean_inc(v_fst_1099_);
lean_dec(v_snd_1097_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1121_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___x_1106_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_1104_, 0, v___x_1074_);
lean_closure_set(v___f_1104_, 1, v_original_1071_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v_fst_1099_);
lean_ctor_set(v___x_1102_, 0, v_fst_1098_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_fst_1098_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_fst_1099_);
v___x_1106_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1118_; 
v___x_1107_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1091_, v___f_1104_, v___x_1106_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v___x_1107_, 1);
lean_dec(v_unused_1119_);
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_fst_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___f_1112_; lean_object* v___x_1114_; 
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1112_, 0, v___x_1081_);
lean_closure_set(v___f_1112_, 1, v_edited_1072_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_snd_1100_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_fst_1108_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_snd_1100_);
v___x_1114_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v_fst_1116_; 
v___x_1115_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1091_, v___f_1112_, v___x_1114_);
v_fst_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_fst_1116_);
lean_dec(v___x_1115_);
return v_fst_1116_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object* v_00_u03b1_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_original_1126_, lean_object* v_edited_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Diff_diff___redArg(v_inst_1123_, v_inst_1124_, v_inst_1125_, v_original_1126_, v_edited_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object* v_inst_1130_, lean_object* v_out_1131_, lean_object* v_a_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_fst_1135_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v_a_1132_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v_a_1132_);
v___x_1137_ = lean_apply_1(v_inst_1130_, v_snd_1136_);
v___x_1138_ = lean_string_dec_eq(v___x_1137_, v_out_1131_);
if (v___x_1138_ == 0)
{
uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1139_ = lean_unbox(v_fst_1135_);
lean_dec(v_fst_1135_);
v___x_1140_ = l_Lean_Diff_Action_linePrefix(v___x_1139_);
v___x_1141_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
v___x_1142_ = lean_string_append(v___x_1140_, v___x_1141_);
v___x_1143_ = lean_string_append(v___x_1142_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1144_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_string_append(v___y_1134_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
else
{
uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec_ref(v___x_1137_);
v___x_1148_ = lean_unbox(v_fst_1135_);
lean_dec(v_fst_1135_);
v___x_1149_ = l_Lean_Diff_Action_linePrefix(v___x_1148_);
v___x_1150_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_1151_ = lean_string_append(v___x_1149_, v___x_1150_);
v___x_1152_ = lean_string_append(v___y_1134_, v___x_1151_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object* v_inst_1154_, lean_object* v_out_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Diff_linesToString___redArg___lam__0(v_inst_1154_, v_out_1155_, v_a_1156_, v_x_1157_, v___y_1158_);
lean_dec_ref(v_out_1155_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object* v_inst_1161_, lean_object* v_lines_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v_out_1164_; lean_object* v___f_1165_; size_t v_sz_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1163_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_out_1164_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___closed__0));
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Diff_linesToString___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1165_, 0, v_inst_1161_);
lean_closure_set(v___f_1165_, 1, v_out_1164_);
v_sz_1166_ = lean_array_size(v_lines_1162_);
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1163_, v_lines_1162_, v___f_1165_, v_sz_1166_, v___x_1167_, v_out_1164_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object* v_00_u03b1_1169_, lean_object* v_inst_1170_, lean_object* v_lines_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Diff_linesToString___redArg(v_inst_1170_, v_lines_1171_);
return v___x_1172_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Diff(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Diff_instInhabitedAction_default = _init_l_Lean_Diff_instInhabitedAction_default();
l_Lean_Diff_instInhabitedAction = _init_l_Lean_Diff_instInhabitedAction();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Diff(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Diff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Diff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Diff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Diff(builtin);
}
#ifdef __cplusplus
}
#endif
