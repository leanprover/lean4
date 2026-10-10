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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_lcs___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__12 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__12_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_lcs___redArg___lam__3, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Diff_lcs___redArg___closed__13 = (const lean_object*)&l_Lean_Diff_lcs___redArg___closed__13_value;
static const lean_closure_object l_Lean_Diff_lcs___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Diff_lcs___redArg___lam__4, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Diff_lcs___redArg___closed__9_value),((lean_object*)&l_Lean_Diff_lcs___redArg___closed__13_value)} };
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
lean_object* l_Lean_Diff_Action_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Diff_Action_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Diff_Action_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Diff_Action_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_Diff_Action_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Diff_Action_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Diff_Action_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Diff_Action_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg(lean_object* v_insert_24_){
_start:
{
lean_inc(v_insert_24_);
return v_insert_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg___boxed(lean_object* v_insert_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Diff_Action_insert_elim___redArg(v_insert_25_);
lean_dec(v_insert_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Diff_Action_insert_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_insert_30_){
_start:
{
lean_inc(v_insert_30_);
return v_insert_30_;
}
}
LEAN_EXPORT void l_Lean_Diff_Action_insert_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_insert_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Diff_Action_insert_elim(lean_box(0), v_t_28_, lean_box(0), v_insert_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_insert_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Diff_Action_insert_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_insert_35_);
lean_dec(v_insert_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg(lean_object* v_delete_38_){
_start:
{
lean_inc(v_delete_38_);
return v_delete_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg___boxed(lean_object* v_delete_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Diff_Action_delete_elim___redArg(v_delete_39_);
lean_dec(v_delete_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Diff_Action_delete_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_delete_44_){
_start:
{
lean_inc(v_delete_44_);
return v_delete_44_;
}
}
LEAN_EXPORT void l_Lean_Diff_Action_delete_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_delete_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Diff_Action_delete_elim(lean_box(0), v_t_42_, lean_box(0), v_delete_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_delete_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Diff_Action_delete_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_delete_49_);
lean_dec(v_delete_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg(lean_object* v_skip_52_){
_start:
{
lean_inc(v_skip_52_);
return v_skip_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg___boxed(lean_object* v_skip_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Diff_Action_skip_elim___redArg(v_skip_53_);
lean_dec(v_skip_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Diff_Action_skip_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_skip_58_){
_start:
{
lean_inc(v_skip_58_);
return v_skip_58_;
}
}
LEAN_EXPORT void l_Lean_Diff_Action_skip_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_skip_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Diff_Action_skip_elim(lean_box(0), v_t_56_, lean_box(0), v_skip_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_skip_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Diff_Action_skip_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_skip_63_);
lean_dec(v_skip_63_);
return v_res_65_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
lean_object* l_Lean_Diff_instReprAction_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_89_; lean_object* v___y_96_; 
switch(v_x_79_)
{
case 0:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_80_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_82_ = v___x_104_;
goto v___jp_81_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_82_ = v___x_105_;
goto v___jp_81_;
}
}
case 1:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_80_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_89_ = v___x_108_;
goto v___jp_88_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_89_ = v___x_109_;
goto v___jp_88_;
}
}
default: 
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_80_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_96_ = v___x_112_;
goto v___jp_95_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_96_ = v___x_113_;
goto v___jp_95_;
}
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__1));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_80_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__3));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_80_);
return v___x_94_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__5));
lean_inc(v___y_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
v___x_101_ = l_Repr_addAppParen(v___x_100_, v_prec_80_);
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Lean_Diff_instReprAction_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_79_ = stack[0].m_num;
lean_object* v_prec_80_ = stack[1].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Diff_instReprAction_repr(v_x_79_, v_prec_80_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_171__boxed_117_; lean_object* v_res_118_; 
v_x_171__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lean_Diff_instReprAction_repr(v_x_171__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t v_x_121_, uint8_t v_y_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_123_ = lean_box(v_x_121_);
v___x_124_ = lean_obj_tag_nat(v___x_123_);
lean_dec(v___x_123_);
v___x_125_ = lean_box(v_y_122_);
v___x_126_ = lean_obj_tag_nat(v___x_125_);
lean_dec(v___x_125_);
v___x_127_ = lean_nat_dec_eq(v___x_124_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_Diff_instBEqAction_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_121_ = stack[0].m_num;
uint8_t v_y_122_ = stack[1].m_num;
uint8_t v_res_128_;
v_res_128_ = l_Lean_Diff_instBEqAction_beq(v_x_121_, v_y_122_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_instBEqAction_beq___boxed(lean_object* v_x_129_, lean_object* v_y_130_){
_start:
{
uint8_t v_x_24__boxed_131_; uint8_t v_y_25__boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_x_24__boxed_131_ = lean_unbox(v_x_129_);
v_y_25__boxed_132_ = lean_unbox(v_y_130_);
v_res_133_ = l_Lean_Diff_instBEqAction_beq(v_x_24__boxed_131_, v_y_25__boxed_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
uint64_t l_Lean_Diff_instHashableAction_hash(uint8_t v_x_137_){
_start:
{
switch(v_x_137_)
{
case 0:
{
uint64_t v___x_138_; 
v___x_138_ = 0ULL;
return v___x_138_;
}
case 1:
{
uint64_t v___x_139_; 
v___x_139_ = 1ULL;
return v___x_139_;
}
default: 
{
uint64_t v___x_140_; 
v___x_140_ = 2ULL;
return v___x_140_;
}
}
}
}
LEAN_EXPORT void l_Lean_Diff_instHashableAction_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_137_ = stack[0].m_num;
uint64_t v_res_141_;
v_res_141_ = l_Lean_Diff_instHashableAction_hash(v_x_137_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_instHashableAction_hash___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_x_40__boxed_143_; uint64_t v_res_144_; lean_object* v_r_145_; 
v_x_40__boxed_143_ = lean_unbox(v_x_142_);
v_res_144_ = l_Lean_Diff_instHashableAction_hash(v_x_40__boxed_143_);
v_r_145_ = lean_box_uint64(v_res_144_);
return v_r_145_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction_default(void){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction(void){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
lean_object* l_Lean_Diff_instToStringAction___lam__0(uint8_t v_x_153_){
_start:
{
switch(v_x_153_)
{
case 0:
{
lean_object* v___x_154_; 
v___x_154_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__0));
return v___x_154_;
}
case 1:
{
lean_object* v___x_155_; 
v___x_155_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__1));
return v___x_155_;
}
default: 
{
lean_object* v___x_156_; 
v___x_156_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__2));
return v___x_156_;
}
}
}
}
LEAN_EXPORT void l_Lean_Diff_instToStringAction___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_153_ = stack[0].m_num;
lean_object* v_res_157_;
v_res_157_ = l_Lean_Diff_instToStringAction___lam__0(v_x_153_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0___boxed(lean_object* v_x_158_){
_start:
{
uint8_t v_x_36__boxed_159_; lean_object* v_res_160_; 
v_x_36__boxed_159_ = lean_unbox(v_x_158_);
v_res_160_ = l_Lean_Diff_instToStringAction___lam__0(v_x_36__boxed_159_);
return v_res_160_;
}
}
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t v_x_166_){
_start:
{
switch(v_x_166_)
{
case 0:
{
lean_object* v___x_167_; 
v___x_167_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__0));
return v___x_167_;
}
case 1:
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__1));
return v___x_168_;
}
default: 
{
lean_object* v___x_169_; 
v___x_169_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
return v___x_169_;
}
}
}
}
LEAN_EXPORT void l_Lean_Diff_Action_linePrefix_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_166_ = stack[0].m_num;
lean_object* v_res_170_;
v_res_170_ = l_Lean_Diff_Action_linePrefix(v_x_166_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix___boxed(lean_object* v_x_171_){
_start:
{
uint8_t v_x_31__boxed_172_; lean_object* v_res_173_; 
v_x_31__boxed_172_ = lean_unbox(v_x_171_);
v_res_173_ = l_Lean_Diff_Action_linePrefix(v_x_31__boxed_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___redArg(lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_histogram_176_, lean_object* v_index_177_, lean_object* v_val_178_){
_start:
{
lean_object* v___x_179_; 
lean_inc(v_val_178_);
lean_inc_ref(v_inst_175_);
lean_inc_ref(v_inst_174_);
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_174_, v_inst_175_, v_histogram_176_, v_val_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_index_177_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v___x_180_);
lean_ctor_set(v___x_184_, 1, v___x_181_);
lean_ctor_set(v___x_184_, 2, v___x_182_);
lean_ctor_set(v___x_184_, 3, v___x_183_);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_174_, v_inst_175_, v_histogram_176_, v_val_178_, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_207_; 
v_val_186_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_207_ == 0)
{
v___x_188_ = v___x_179_;
v_isShared_189_ = v_isSharedCheck_207_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_val_186_);
lean_dec(v___x_179_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_207_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_leftCount_190_; lean_object* v_rightCount_191_; lean_object* v_rightIndex_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_205_; 
v_leftCount_190_ = lean_ctor_get(v_val_186_, 0);
v_rightCount_191_ = lean_ctor_get(v_val_186_, 2);
v_rightIndex_192_ = lean_ctor_get(v_val_186_, 3);
v_isSharedCheck_205_ = !lean_is_exclusive(v_val_186_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_val_186_, 1);
lean_dec(v_unused_206_);
v___x_194_ = v_val_186_;
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_rightIndex_192_);
lean_inc(v_rightCount_191_);
lean_inc(v_leftCount_190_);
lean_dec(v_val_186_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_leftCount_190_, v___x_196_);
lean_dec(v_leftCount_190_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v_index_177_);
v___x_199_ = v___x_188_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_index_177_);
v___x_199_ = v_reuseFailAlloc_204_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_199_);
lean_ctor_set(v___x_194_, 0, v___x_197_);
v___x_201_ = v___x_194_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_rightCount_191_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_rightIndex_192_);
v___x_201_ = v_reuseFailAlloc_203_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_174_, v_inst_175_, v_histogram_176_, v_val_178_, v___x_201_);
return v___x_202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft(lean_object* v_00_u03b1_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_lsize_211_, lean_object* v_rsize_212_, lean_object* v_histogram_213_, lean_object* v_index_214_, lean_object* v_val_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_209_, v_inst_210_, v_histogram_213_, v_index_214_, v_val_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___boxed(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_lsize_220_, lean_object* v_rsize_221_, lean_object* v_histogram_222_, lean_object* v_index_223_, lean_object* v_val_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Diff_Histogram_addLeft(v_00_u03b1_217_, v_inst_218_, v_inst_219_, v_lsize_220_, v_rsize_221_, v_histogram_222_, v_index_223_, v_val_224_);
lean_dec(v_rsize_221_);
lean_dec(v_lsize_220_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___redArg(lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_histogram_228_, lean_object* v_index_229_, lean_object* v_val_230_){
_start:
{
lean_object* v___x_231_; 
lean_inc(v_val_230_);
lean_inc_ref(v_inst_227_);
lean_inc_ref(v_inst_226_);
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_226_, v_inst_227_, v_histogram_228_, v_val_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_box(0);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_index_229_);
v___x_236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_236_, 0, v___x_232_);
lean_ctor_set(v___x_236_, 1, v___x_233_);
lean_ctor_set(v___x_236_, 2, v___x_234_);
lean_ctor_set(v___x_236_, 3, v___x_235_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_226_, v_inst_227_, v_histogram_228_, v_val_230_, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_259_; 
v_val_238_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_259_ == 0)
{
v___x_240_ = v___x_231_;
v_isShared_241_ = v_isSharedCheck_259_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_231_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_259_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_leftCount_242_; lean_object* v_leftIndex_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_256_; 
v_leftCount_242_ = lean_ctor_get(v_val_238_, 0);
v_leftIndex_243_ = lean_ctor_get(v_val_238_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_val_238_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_257_ = lean_ctor_get(v_val_238_, 3);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_val_238_, 2);
lean_dec(v_unused_258_);
v___x_245_ = v_val_238_;
v_isShared_246_ = v_isSharedCheck_256_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_leftIndex_243_);
lean_inc(v_leftCount_242_);
lean_dec(v_val_238_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_256_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_add(v_leftCount_242_, v___x_247_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v_index_229_);
v___x_250_ = v___x_240_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_index_229_);
v___x_250_ = v_reuseFailAlloc_255_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 3, v___x_250_);
lean_ctor_set(v___x_245_, 2, v___x_248_);
v___x_252_ = v___x_245_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_leftCount_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_leftIndex_243_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_250_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_226_, v_inst_227_, v_histogram_228_, v_val_230_, v___x_252_);
return v___x_253_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight(lean_object* v_00_u03b1_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_lsize_263_, lean_object* v_rsize_264_, lean_object* v_histogram_265_, lean_object* v_index_266_, lean_object* v_val_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_261_, v_inst_262_, v_histogram_265_, v_index_266_, v_val_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___boxed(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_lsize_272_, lean_object* v_rsize_273_, lean_object* v_histogram_274_, lean_object* v_index_275_, lean_object* v_val_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Diff_Histogram_addRight(v_00_u03b1_269_, v_inst_270_, v_inst_271_, v_lsize_272_, v_rsize_273_, v_histogram_274_, v_index_275_, v_val_276_);
lean_dec(v_rsize_273_);
lean_dec(v_lsize_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(lean_object* v_inst_278_, lean_object* v_left_279_, lean_object* v_right_280_, lean_object* v_pref_281_){
_start:
{
lean_object* v_start_282_; lean_object* v_stop_283_; lean_object* v_i_284_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_start_282_ = lean_ctor_get(v_left_279_, 1);
v_stop_283_ = lean_ctor_get(v_left_279_, 2);
v_i_284_ = lean_array_get_size(v_pref_281_);
v___x_290_ = lean_nat_sub(v_stop_283_, v_start_282_);
v___x_291_ = lean_nat_dec_lt(v_i_284_, v___x_290_);
lean_dec(v___x_290_);
if (v___x_291_ == 0)
{
lean_dec_ref(v_inst_278_);
goto v___jp_285_;
}
else
{
lean_object* v_start_292_; lean_object* v_stop_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_start_292_ = lean_ctor_get(v_right_280_, 1);
v_stop_293_ = lean_ctor_get(v_right_280_, 2);
v___x_294_ = lean_nat_sub(v_stop_293_, v_start_292_);
v___x_295_ = lean_nat_dec_lt(v_i_284_, v___x_294_);
lean_dec(v___x_294_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_inst_278_);
goto v___jp_285_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_296_ = l_Subarray_get___redArg(v_left_279_, v_i_284_);
v___x_297_ = l_Subarray_get___redArg(v_right_280_, v_i_284_);
lean_inc_ref(v_inst_278_);
lean_inc(v___x_296_);
v___x_298_ = lean_apply_2(v_inst_278_, v___x_296_, v___x_297_);
v___x_299_ = lean_unbox(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v___x_296_);
lean_dec_ref(v_inst_278_);
v___x_300_ = l_Subarray_drop___redArg(v_left_279_, v_i_284_);
v___x_301_ = l_Subarray_drop___redArg(v_right_280_, v_i_284_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_pref_281_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_array_push(v_pref_281_, v___x_296_);
v_pref_281_ = v___x_304_;
goto _start;
}
}
}
v___jp_285_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = l_Subarray_drop___redArg(v_left_279_, v_i_284_);
v___x_287_ = l_Subarray_drop___redArg(v_right_280_, v_i_284_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_pref_281_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_left_308_, lean_object* v_right_309_, lean_object* v_pref_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_307_, v_left_308_, v_right_309_, v_pref_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___redArg(lean_object* v_inst_314_, lean_object* v_left_315_, lean_object* v_right_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_318_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_314_, v_left_315_, v_right_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_left_321_, lean_object* v_right_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Diff_matchPrefix___redArg(v_inst_320_, v_left_321_, v_right_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(lean_object* v_it_324_, lean_object* v_acc_325_, lean_object* v_recur_326_){
_start:
{
lean_object* v_array_327_; lean_object* v_start_328_; lean_object* v_stop_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_342_; 
v_array_327_ = lean_ctor_get(v_it_324_, 0);
v_start_328_ = lean_ctor_get(v_it_324_, 1);
v_stop_329_ = lean_ctor_get(v_it_324_, 2);
v_isSharedCheck_342_ = !lean_is_exclusive(v_it_324_);
if (v_isSharedCheck_342_ == 0)
{
v___x_331_ = v_it_324_;
v_isShared_332_ = v_isSharedCheck_342_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_stop_329_);
lean_inc(v_start_328_);
lean_inc(v_array_327_);
lean_dec(v_it_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_342_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
uint8_t v___x_333_; 
v___x_333_ = lean_nat_dec_lt(v_start_328_, v_stop_329_);
if (v___x_333_ == 0)
{
lean_del_object(v___x_331_);
lean_dec(v_stop_329_);
lean_dec(v_start_328_);
lean_dec_ref(v_array_327_);
lean_dec_ref(v_recur_326_);
return v_acc_325_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_start_328_, v___x_334_);
lean_inc_ref(v_array_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_335_);
v___x_337_ = v___x_331_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_array_327_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_stop_329_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_array_fget(v_array_327_, v_start_328_);
lean_dec(v_start_328_);
lean_dec_ref(v_array_327_);
v___x_339_ = lean_array_push(v_acc_325_, v___x_338_);
v___x_340_ = lean_apply_3(v_recur_326_, v___x_337_, v___x_339_, lean_box(0));
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(lean_object* v_inst_344_, lean_object* v_left_345_, lean_object* v_right_346_, lean_object* v_i_347_){
_start:
{
lean_object* v_start_348_; lean_object* v_stop_349_; lean_object* v___f_350_; lean_object* v___x_351_; uint8_t v___x_365_; 
v_start_348_ = lean_ctor_get(v_left_345_, 1);
v_stop_349_ = lean_ctor_get(v_left_345_, 2);
v___f_350_ = ((lean_object*)(l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0));
v___x_351_ = lean_nat_sub(v_stop_349_, v_start_348_);
v___x_365_ = lean_nat_dec_lt(v_i_347_, v___x_351_);
if (v___x_365_ == 0)
{
lean_dec_ref(v_inst_344_);
goto v___jp_352_;
}
else
{
lean_object* v_start_366_; lean_object* v_stop_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_start_366_ = lean_ctor_get(v_right_346_, 1);
v_stop_367_ = lean_ctor_get(v_right_346_, 2);
v___x_368_ = lean_nat_sub(v_stop_367_, v_start_366_);
v___x_369_ = lean_nat_dec_lt(v_i_347_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v___x_368_);
lean_dec_ref(v_inst_344_);
goto v___jp_352_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_370_ = lean_nat_sub(v___x_351_, v_i_347_);
lean_dec(v___x_351_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_sub(v___x_370_, v___x_371_);
v___x_373_ = l_Subarray_get___redArg(v_left_345_, v___x_372_);
lean_dec(v___x_372_);
v___x_374_ = lean_nat_sub(v___x_368_, v_i_347_);
lean_dec(v___x_368_);
v___x_375_ = lean_nat_sub(v___x_374_, v___x_371_);
v___x_376_ = l_Subarray_get___redArg(v_right_346_, v___x_375_);
lean_dec(v___x_375_);
lean_inc_ref(v_inst_344_);
v___x_377_ = lean_apply_2(v_inst_344_, v___x_373_, v___x_376_);
v___x_378_ = lean_unbox(v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_i_347_);
lean_dec_ref(v_inst_344_);
lean_inc_ref(v_left_345_);
v___x_379_ = l_Subarray_take___redArg(v_left_345_, v___x_370_);
v___x_380_ = l_Subarray_take___redArg(v_right_346_, v___x_374_);
lean_dec(v___x_374_);
v___x_381_ = l_Subarray_drop___redArg(v_left_345_, v___x_370_);
lean_dec(v___x_370_);
v___x_382_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_383_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_350_, v___x_381_, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_380_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_379_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
lean_dec(v___x_374_);
lean_dec(v___x_370_);
v___x_386_ = lean_nat_add(v_i_347_, v___x_371_);
lean_dec(v_i_347_);
v_i_347_ = v___x_386_;
goto _start;
}
}
}
v___jp_352_:
{
lean_object* v_start_353_; lean_object* v_stop_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_start_353_ = lean_ctor_get(v_right_346_, 1);
v_stop_354_ = lean_ctor_get(v_right_346_, 2);
v___x_355_ = lean_nat_sub(v___x_351_, v_i_347_);
lean_dec(v___x_351_);
lean_inc_ref(v_left_345_);
v___x_356_ = l_Subarray_take___redArg(v_left_345_, v___x_355_);
v___x_357_ = lean_nat_sub(v_stop_354_, v_start_353_);
v___x_358_ = lean_nat_sub(v___x_357_, v_i_347_);
lean_dec(v_i_347_);
lean_dec(v___x_357_);
v___x_359_ = l_Subarray_take___redArg(v_right_346_, v___x_358_);
lean_dec(v___x_358_);
v___x_360_ = l_Subarray_drop___redArg(v_left_345_, v___x_355_);
lean_dec(v___x_355_);
v___x_361_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_362_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_350_, v___x_360_, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_359_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_356_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_left_390_, lean_object* v_right_391_, lean_object* v_i_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_389_, v_left_390_, v_right_391_, v_i_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object* v_inst_394_, lean_object* v_left_395_, lean_object* v_right_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_394_, v_left_395_, v_right_396_, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_left_401_, lean_object* v_right_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Diff_matchSuffix___redArg(v_inst_400_, v_left_401_, v_right_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object* v___x_404_, lean_object* v_fst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_next_408_, lean_object* v_acc_409_, lean_object* v_h_410_, lean_object* v_G_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_lt(v_next_408_, v___x_404_);
if (v___x_412_ == 0)
{
lean_dec_ref(v_G_411_);
lean_dec(v_next_408_);
lean_dec_ref(v_inst_407_);
lean_dec_ref(v_inst_406_);
return v_acc_409_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_413_ = l_Subarray_get___redArg(v_fst_405_, v_next_408_);
lean_inc(v_next_408_);
v___x_414_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_406_, v_inst_407_, v_acc_409_, v_next_408_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_next_408_, v___x_415_);
lean_dec(v_next_408_);
v___x_417_ = lean_apply_4(v_G_411_, v___x_416_, v___x_414_, lean_box(0), lean_box(0));
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0___boxed(lean_object* v___x_418_, lean_object* v_fst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_next_422_, lean_object* v_acc_423_, lean_object* v_h_424_, lean_object* v_G_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Diff_lcs___redArg___lam__0(v___x_418_, v_fst_419_, v_inst_420_, v_inst_421_, v_next_422_, v_acc_423_, v_h_424_, v_G_425_);
lean_dec_ref(v_fst_419_);
lean_dec(v___x_418_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object* v___x_427_, lean_object* v_fst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_next_431_, lean_object* v_acc_432_, lean_object* v_h_433_, lean_object* v_G_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_nat_dec_lt(v_next_431_, v___x_427_);
if (v___x_435_ == 0)
{
lean_dec_ref(v_G_434_);
lean_dec(v_next_431_);
lean_dec_ref(v_inst_430_);
lean_dec_ref(v_inst_429_);
return v_acc_432_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_436_ = l_Subarray_get___redArg(v_fst_428_, v_next_431_);
lean_inc(v_next_431_);
v___x_437_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_429_, v_inst_430_, v_acc_432_, v_next_431_, v___x_436_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_next_431_, v___x_438_);
lean_dec(v_next_431_);
v___x_440_ = lean_apply_4(v_G_434_, v___x_439_, v___x_437_, lean_box(0), lean_box(0));
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1___boxed(lean_object* v___x_441_, lean_object* v_fst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_next_445_, lean_object* v_acc_446_, lean_object* v_h_447_, lean_object* v_G_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Diff_lcs___redArg___lam__1(v___x_441_, v_fst_442_, v_inst_443_, v_inst_444_, v_next_445_, v_acc_446_, v_h_447_, v_G_448_);
lean_dec_ref(v_fst_442_);
lean_dec(v___x_441_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object* v_a_450_, lean_object* v_x_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_snd_453_; lean_object* v_leftIndex_454_; 
v_snd_453_ = lean_ctor_get(v_a_450_, 1);
lean_inc(v_snd_453_);
v_leftIndex_454_ = lean_ctor_get(v_snd_453_, 1);
lean_inc(v_leftIndex_454_);
if (lean_obj_tag(v_leftIndex_454_) == 1)
{
lean_object* v_rightIndex_455_; 
v_rightIndex_455_ = lean_ctor_get(v_snd_453_, 3);
lean_inc(v_rightIndex_455_);
if (lean_obj_tag(v_rightIndex_455_) == 1)
{
if (lean_obj_tag(v___y_452_) == 0)
{
lean_object* v_fst_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_484_; 
v_fst_456_ = lean_ctor_get(v_a_450_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_a_450_, 1);
lean_dec(v_unused_485_);
v___x_458_ = v_a_450_;
v_isShared_459_ = v_isSharedCheck_484_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_fst_456_);
lean_dec(v_a_450_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_484_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_leftCount_460_; lean_object* v_rightCount_461_; lean_object* v_val_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_483_; 
v_leftCount_460_ = lean_ctor_get(v_snd_453_, 0);
lean_inc(v_leftCount_460_);
v_rightCount_461_ = lean_ctor_get(v_snd_453_, 2);
lean_inc(v_rightCount_461_);
lean_dec(v_snd_453_);
v_val_462_ = lean_ctor_get(v_leftIndex_454_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_leftIndex_454_);
if (v_isSharedCheck_483_ == 0)
{
v___x_464_ = v_leftIndex_454_;
v_isShared_465_ = v_isSharedCheck_483_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_val_462_);
lean_dec(v_leftIndex_454_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_483_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_val_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_482_; 
v_val_466_ = lean_ctor_get(v_rightIndex_455_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v_rightIndex_455_);
if (v_isSharedCheck_482_ == 0)
{
v___x_468_ = v_rightIndex_455_;
v_isShared_469_ = v_isSharedCheck_482_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_val_466_);
lean_dec(v_rightIndex_455_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_482_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_nat_add(v_leftCount_460_, v_rightCount_461_);
lean_dec(v_rightCount_461_);
lean_dec(v_leftCount_460_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v_val_466_);
lean_ctor_set(v___x_458_, 0, v_val_462_);
v___x_472_ = v___x_458_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_val_462_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_val_466_);
v___x_472_ = v_reuseFailAlloc_481_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v_fst_456_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_470_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_474_);
v___x_476_ = v___x_468_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_476_);
v___x_478_ = v___x_464_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_486_; lean_object* v_fst_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_528_; 
v_val_486_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_val_486_);
v_fst_487_ = lean_ctor_get(v_a_450_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_a_450_, 1);
lean_dec(v_unused_529_);
v___x_489_ = v_a_450_;
v_isShared_490_ = v_isSharedCheck_528_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_fst_487_);
lean_dec(v_a_450_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_528_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_leftCount_491_; lean_object* v_rightCount_492_; lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_527_; 
v_leftCount_491_ = lean_ctor_get(v_snd_453_, 0);
lean_inc(v_leftCount_491_);
v_rightCount_492_ = lean_ctor_get(v_snd_453_, 2);
lean_inc(v_rightCount_492_);
lean_dec(v_snd_453_);
v_val_493_ = lean_ctor_get(v_leftIndex_454_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_leftIndex_454_);
if (v_isSharedCheck_527_ == 0)
{
v___x_495_ = v_leftIndex_454_;
v_isShared_496_ = v_isSharedCheck_527_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v_leftIndex_454_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_527_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_val_497_; lean_object* v_fst_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_525_; 
v_val_497_ = lean_ctor_get(v_rightIndex_455_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_rightIndex_455_, 1);
v_fst_498_ = lean_ctor_get(v_val_486_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_val_486_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_val_486_, 1);
lean_dec(v_unused_526_);
v___x_500_ = v_val_486_;
v_isShared_501_ = v_isSharedCheck_525_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_fst_498_);
lean_dec(v_val_486_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_525_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_nat_add(v_leftCount_491_, v_rightCount_492_);
lean_dec(v_rightCount_492_);
lean_dec(v_leftCount_491_);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v_fst_498_);
lean_dec(v_fst_498_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v___x_502_);
lean_del_object(v___x_500_);
lean_dec(v_val_497_);
lean_dec(v_val_493_);
lean_del_object(v___x_489_);
lean_dec(v_fst_487_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___y_452_);
v___x_505_ = v___x_495_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___y_452_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___y_452_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___y_452_, 0);
lean_dec(v_unused_524_);
v___x_508_ = v___y_452_;
v_isShared_509_ = v_isSharedCheck_523_;
goto v_resetjp_507_;
}
else
{
lean_dec(v___y_452_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_523_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v_val_497_);
lean_ctor_set(v___x_500_, 0, v_val_493_);
v___x_511_ = v___x_500_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_val_493_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_val_497_);
v___x_511_ = v_reuseFailAlloc_522_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_511_);
v___x_513_ = v___x_489_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_521_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_502_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_514_);
v___x_516_ = v___x_508_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_516_);
v___x_518_ = v___x_495_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
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
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_rightIndex_455_);
lean_dec(v_snd_453_);
lean_dec_ref(v_a_450_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_leftIndex_454_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_leftIndex_454_, 0);
lean_dec(v_unused_537_);
v___x_531_ = v_leftIndex_454_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_leftIndex_454_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___y_452_);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___y_452_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_538_; 
lean_dec(v_leftIndex_454_);
lean_dec(v_snd_453_);
lean_dec_ref(v_a_450_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___y_452_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object* v_a_539_, lean_object* v_b_540_, lean_object* v_d_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_539_);
lean_ctor_set(v___x_542_, 1, v_b_540_);
v___x_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_d_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__4(lean_object* v___x_544_, lean_object* v___f_545_, lean_object* v_l_546_, lean_object* v_acc_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_544_, v___f_545_, v_acc_547_, v_l_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__10(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_unsigned_to_nat(16u);
v___x_570_ = lean_mk_array(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__11(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_hist_573_; 
v___x_571_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__10, &l_Lean_Diff_lcs___redArg___closed__10_once, _init_l_Lean_Diff_lcs___redArg___closed__10);
v___x_572_ = lean_unsigned_to_nat(0u);
v_hist_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_573_, 0, v___x_572_);
lean_ctor_set(v_hist_573_, 1, v___x_571_);
return v_hist_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_left_581_, lean_object* v_right_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_snd_585_; lean_object* v_fst_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v_snd_590_; lean_object* v_fst_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v_start_594_; lean_object* v_stop_595_; lean_object* v_start_596_; lean_object* v_stop_597_; lean_object* v___x_598_; lean_object* v_hist_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v_buckets_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___y_610_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_583_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
lean_inc_ref_n(v_inst_579_, 4);
v___x_584_ = l_Lean_Diff_matchPrefix___redArg(v_inst_579_, v_left_581_, v_right_582_);
v_snd_585_ = lean_ctor_get(v___x_584_, 1);
lean_inc(v_snd_585_);
v_fst_586_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_fst_586_);
lean_dec_ref(v___x_584_);
v_fst_587_ = lean_ctor_get(v_snd_585_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_snd_585_, 1);
lean_inc(v_snd_588_);
lean_dec(v_snd_585_);
v___x_589_ = l_Lean_Diff_matchSuffix___redArg(v_inst_579_, v_fst_587_, v_snd_588_);
v_snd_590_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_snd_590_);
v_fst_591_ = lean_ctor_get(v___x_589_, 0);
lean_inc_n(v_fst_591_, 2);
lean_dec_ref(v___x_589_);
v_fst_592_ = lean_ctor_get(v_snd_590_, 0);
lean_inc_n(v_fst_592_, 2);
v_snd_593_ = lean_ctor_get(v_snd_590_, 1);
lean_inc(v_snd_593_);
lean_dec(v_snd_590_);
v_start_594_ = lean_ctor_get(v_fst_591_, 1);
v_stop_595_ = lean_ctor_get(v_fst_591_, 2);
v_start_596_ = lean_ctor_get(v_fst_592_, 1);
v_stop_597_ = lean_ctor_get(v_fst_592_, 2);
v___x_598_ = lean_unsigned_to_nat(0u);
v_hist_599_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__11, &l_Lean_Diff_lcs___redArg___closed__11_once, _init_l_Lean_Diff_lcs___redArg___closed__11);
v___x_600_ = lean_nat_sub(v_stop_595_, v_start_594_);
lean_inc_ref_n(v_inst_580_, 2);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_601_, 0, v___x_600_);
lean_closure_set(v___f_601_, 1, v_fst_591_);
lean_closure_set(v___f_601_, 2, v_inst_579_);
lean_closure_set(v___f_601_, 3, v_inst_580_);
v___x_602_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_601_, v___x_598_, v_hist_599_, lean_box(0));
v___x_603_ = lean_nat_sub(v_stop_597_, v_start_596_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_604_, 0, v___x_603_);
lean_closure_set(v___f_604_, 1, v_fst_592_);
lean_closure_set(v___f_604_, 2, v_inst_579_);
lean_closure_set(v___f_604_, 3, v_inst_580_);
v___x_605_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_604_, v___x_598_, v___x_602_, lean_box(0));
v_buckets_606_ = lean_ctor_get(v___x_605_, 1);
lean_inc_ref(v_buckets_606_);
lean_dec(v___x_605_);
v___f_607_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__12));
v___x_608_ = lean_box(0);
v___x_636_ = lean_box(0);
v___x_637_ = lean_array_get_size(v_buckets_606_);
v___x_638_ = lean_nat_dec_lt(v___x_598_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec_ref(v_buckets_606_);
v___y_610_ = v___x_636_;
goto v___jp_609_;
}
else
{
lean_object* v___f_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___f_639_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__14));
v___x_640_ = lean_usize_of_nat(v___x_637_);
v___x_641_ = ((size_t)0ULL);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_583_, v___f_639_, v_buckets_606_, v___x_640_, v___x_641_, v___x_636_);
v___y_610_ = v___x_642_;
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = l_List_forIn_x27_loop___redArg(v___x_583_, v___f_607_, v___y_610_, v___x_608_);
lean_dec(v___y_610_);
if (lean_obj_tag(v___x_611_) == 1)
{
lean_object* v_val_612_; lean_object* v_snd_613_; lean_object* v_snd_614_; lean_object* v_fst_615_; lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___x_618_; lean_object* v_fst_619_; lean_object* v_snd_620_; lean_object* v___x_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_val_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_612_);
lean_dec_ref_known(v___x_611_, 1);
v_snd_613_ = lean_ctor_get(v_val_612_, 1);
lean_inc(v_snd_613_);
lean_dec(v_val_612_);
v_snd_614_ = lean_ctor_get(v_snd_613_, 1);
lean_inc(v_snd_614_);
v_fst_615_ = lean_ctor_get(v_snd_613_, 0);
lean_inc(v_fst_615_);
lean_dec(v_snd_613_);
v_fst_616_ = lean_ctor_get(v_snd_614_, 0);
lean_inc(v_fst_616_);
v_snd_617_ = lean_ctor_get(v_snd_614_, 1);
lean_inc(v_snd_617_);
lean_dec(v_snd_614_);
v___x_618_ = l_Subarray_split___redArg(v_fst_591_, v_fst_616_);
lean_dec(v_fst_616_);
v_fst_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_fst_619_);
v_snd_620_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_snd_620_);
lean_dec_ref(v___x_618_);
v___x_621_ = l_Subarray_split___redArg(v_fst_592_, v_snd_617_);
lean_dec(v_snd_617_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v___x_621_);
lean_inc_ref(v_inst_580_);
lean_inc_ref(v_inst_579_);
v___x_624_ = l_Lean_Diff_lcs___redArg(v_inst_579_, v_inst_580_, v_fst_619_, v_fst_622_);
v___x_625_ = l_Array_append___redArg(v_fst_586_, v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_mk_empty_array_with_capacity(v___x_626_);
v___x_628_ = lean_array_push(v___x_627_, v_fst_615_);
v___x_629_ = l_Array_append___redArg(v___x_625_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_630_ = l_Subarray_drop___redArg(v_snd_620_, v___x_626_);
v___x_631_ = l_Subarray_drop___redArg(v_snd_623_, v___x_626_);
v___x_632_ = l_Lean_Diff_lcs___redArg(v_inst_579_, v_inst_580_, v___x_630_, v___x_631_);
v___x_633_ = l_Array_append___redArg(v___x_629_, v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Array_append___redArg(v___x_633_, v_snd_593_);
lean_dec(v_snd_593_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec(v___x_611_);
lean_dec(v_fst_592_);
lean_dec(v_fst_591_);
lean_dec_ref(v_inst_580_);
lean_dec_ref(v_inst_579_);
v___x_635_ = l_Array_append___redArg(v_fst_586_, v_snd_593_);
lean_dec(v_snd_593_);
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object* v_00_u03b1_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_left_646_, lean_object* v_right_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Diff_lcs___redArg(v_inst_644_, v_inst_645_, v_left_646_, v_right_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object* v_x_649_){
_start:
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = 0;
v___x_651_ = lean_box(v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_x_649_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object* v_x_653_){
_start:
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = 1;
v___x_655_ = lean_box(v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_x_653_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object* v___x_657_, lean_object* v_inst_658_, lean_object* v_original_659_, lean_object* v_inst_660_, lean_object* v_a_661_, lean_object* v_b_662_){
_start:
{
lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_685_; 
v_fst_663_ = lean_ctor_get(v_b_662_, 0);
v_snd_664_ = lean_ctor_get(v_b_662_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_b_662_);
if (v_isSharedCheck_685_ == 0)
{
v___x_666_ = v_b_662_;
v_isShared_667_ = v_isSharedCheck_685_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_snd_664_);
lean_inc(v_fst_663_);
lean_dec(v_b_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_685_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_snd_664_, v___x_657_);
if (v___x_673_ == 0)
{
lean_dec(v_a_661_);
lean_dec_ref(v_inst_660_);
goto v___jp_668_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_array_get_borrowed(v_inst_658_, v_original_659_, v_snd_664_);
lean_inc(v___x_674_);
v___x_675_ = lean_apply_2(v_inst_660_, v___x_674_, v_a_661_);
v___x_676_ = lean_unbox(v___x_675_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_del_object(v___x_666_);
v___x_677_ = 1;
v___x_678_ = lean_box(v___x_677_);
lean_inc(v___x_674_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_674_);
v___x_680_ = lean_array_push(v_fst_663_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_snd_664_, v___x_681_);
lean_dec(v_snd_664_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
else
{
goto v___jp_668_;
}
}
v___jp_668_:
{
lean_object* v___x_670_; 
if (v_isShared_667_ == 0)
{
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_fst_663_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_snd_664_);
v___x_670_ = v_reuseFailAlloc_672_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object* v___x_686_, lean_object* v_inst_687_, lean_object* v_original_688_, lean_object* v_inst_689_, lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Diff_diff___redArg___lam__2(v___x_686_, v_inst_687_, v_original_688_, v_inst_689_, v_a_690_, v_b_691_);
lean_dec_ref(v_original_688_);
lean_dec(v_inst_687_);
lean_dec(v___x_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object* v___x_693_, lean_object* v_inst_694_, lean_object* v_edited_695_, lean_object* v_inst_696_, lean_object* v_a_697_, lean_object* v_b_698_){
_start:
{
lean_object* v_fst_699_; lean_object* v_snd_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_721_; 
v_fst_699_ = lean_ctor_get(v_b_698_, 0);
v_snd_700_ = lean_ctor_get(v_b_698_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_b_698_);
if (v_isSharedCheck_721_ == 0)
{
v___x_702_ = v_b_698_;
v_isShared_703_ = v_isSharedCheck_721_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_snd_700_);
lean_inc(v_fst_699_);
lean_dec(v_b_698_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_721_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___x_709_; 
v___x_709_ = lean_nat_dec_lt(v_snd_700_, v___x_693_);
if (v___x_709_ == 0)
{
lean_dec(v_a_697_);
lean_dec_ref(v_inst_696_);
goto v___jp_704_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = lean_array_get_borrowed(v_inst_694_, v_edited_695_, v_snd_700_);
lean_inc(v___x_710_);
v___x_711_ = lean_apply_2(v_inst_696_, v___x_710_, v_a_697_);
v___x_712_ = lean_unbox(v___x_711_);
if (v___x_712_ == 0)
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_del_object(v___x_702_);
v___x_713_ = 0;
v___x_714_ = lean_box(v___x_713_);
lean_inc(v___x_710_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_710_);
v___x_716_ = lean_array_push(v_fst_699_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_add(v_snd_700_, v___x_717_);
lean_dec(v_snd_700_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_716_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
else
{
goto v___jp_704_;
}
}
v___jp_704_:
{
lean_object* v___x_706_; 
if (v_isShared_703_ == 0)
{
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_fst_699_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_snd_700_);
v___x_706_ = v_reuseFailAlloc_708_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object* v___x_722_, lean_object* v_inst_723_, lean_object* v_edited_724_, lean_object* v_inst_725_, lean_object* v_a_726_, lean_object* v_b_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Diff_diff___redArg___lam__3(v___x_722_, v_inst_723_, v_edited_724_, v_inst_725_, v_a_726_, v_b_727_);
lean_dec_ref(v_edited_724_);
lean_dec(v_inst_723_);
lean_dec(v___x_722_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object* v___x_729_, lean_object* v_inst_730_, lean_object* v_original_731_, lean_object* v_inst_732_, lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v_edited_735_, lean_object* v_a_736_, lean_object* v_x_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_snd_739_; lean_object* v_fst_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_786_; 
v_snd_739_ = lean_ctor_get(v___y_738_, 1);
v_fst_740_ = lean_ctor_get(v___y_738_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___y_738_);
if (v_isSharedCheck_786_ == 0)
{
v___x_742_ = v___y_738_;
v_isShared_743_ = v_isSharedCheck_786_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_740_);
lean_dec(v___y_738_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_786_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_fst_744_; lean_object* v_snd_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_785_; 
v_fst_744_ = lean_ctor_get(v_snd_739_, 0);
v_snd_745_ = lean_ctor_get(v_snd_739_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_snd_739_);
if (v_isSharedCheck_785_ == 0)
{
v___x_747_ = v_snd_739_;
v_isShared_748_ = v_isSharedCheck_785_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snd_745_);
lean_inc(v_fst_744_);
lean_dec(v_snd_739_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_785_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___f_749_; lean_object* v___x_751_; 
lean_inc(v_a_736_);
lean_inc_ref(v_inst_732_);
lean_inc(v_inst_730_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_749_, 0, v___x_729_);
lean_closure_set(v___f_749_, 1, v_inst_730_);
lean_closure_set(v___f_749_, 2, v_original_731_);
lean_closure_set(v___f_749_, 3, v_inst_732_);
lean_closure_set(v___f_749_, 4, v_a_736_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_fst_744_);
lean_ctor_set(v___x_747_, 0, v_fst_740_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fst_740_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_fst_744_);
v___x_751_ = v_reuseFailAlloc_784_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_783_; 
lean_inc_ref(v___x_733_);
v___x_752_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_733_, v___f_749_, v___x_751_);
v_fst_753_ = lean_ctor_get(v___x_752_, 0);
v_snd_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_783_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_783_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_snd_754_);
lean_inc(v_fst_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_783_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___f_758_; lean_object* v___x_760_; 
lean_inc(v_a_736_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_758_, 0, v___x_734_);
lean_closure_set(v___f_758_, 1, v_inst_730_);
lean_closure_set(v___f_758_, 2, v_edited_735_);
lean_closure_set(v___f_758_, 3, v_inst_732_);
lean_closure_set(v___f_758_, 4, v_a_736_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_snd_745_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_fst_753_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_745_);
v___x_760_ = v_reuseFailAlloc_782_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_781_; 
v___x_761_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_733_, v___f_758_, v___x_760_);
v_fst_762_ = lean_ctor_get(v___x_761_, 0);
v_snd_763_ = lean_ctor_get(v___x_761_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_781_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_snd_763_);
lean_inc(v_fst_762_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = 2;
v___x_768_ = lean_box(v___x_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_a_736_);
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_736_);
v___x_770_ = v_reuseFailAlloc_780_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_771_ = lean_array_push(v_fst_762_, v___x_770_);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_snd_754_, v___x_772_);
lean_dec(v_snd_754_);
v___x_774_ = lean_nat_add(v_snd_763_, v___x_772_);
lean_dec(v_snd_763_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_774_);
lean_ctor_set(v___x_742_, 0, v___x_773_);
v___x_776_ = v___x_742_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_779_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_771_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5(lean_object* v___x_787_, lean_object* v_original_788_, lean_object* v_b_789_){
_start:
{
lean_object* v_fst_790_; lean_object* v_snd_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_811_; 
v_fst_790_ = lean_ctor_get(v_b_789_, 0);
v_snd_791_ = lean_ctor_get(v_b_789_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_b_789_);
if (v_isSharedCheck_811_ == 0)
{
v___x_793_ = v_b_789_;
v_isShared_794_ = v_isSharedCheck_811_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snd_791_);
lean_inc(v_fst_790_);
lean_dec(v_b_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_811_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_lt(v_snd_791_, v___x_787_);
if (v___x_795_ == 0)
{
lean_object* v___x_797_; 
if (v_isShared_794_ == 0)
{
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_fst_790_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_791_);
v___x_797_ = v_reuseFailAlloc_799_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
else
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_800_ = 1;
v___x_801_ = lean_array_fget_borrowed(v_original_788_, v_snd_791_);
v___x_802_ = lean_box(v___x_800_);
lean_inc(v___x_801_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_801_);
lean_ctor_set(v___x_793_, 0, v___x_802_);
v___x_804_ = v___x_793_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_801_);
v___x_804_ = v_reuseFailAlloc_810_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_805_ = lean_array_push(v_fst_790_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_snd_791_, v___x_806_);
lean_dec(v_snd_791_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_805_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5___boxed(lean_object* v___x_812_, lean_object* v_original_813_, lean_object* v_b_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Diff_diff___redArg___lam__5(v___x_812_, v_original_813_, v_b_814_);
lean_dec_ref(v_original_813_);
lean_dec(v___x_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6(lean_object* v___x_816_, lean_object* v_edited_817_, lean_object* v_b_818_){
_start:
{
lean_object* v_fst_819_; lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_840_; 
v_fst_819_ = lean_ctor_get(v_b_818_, 0);
v_snd_820_ = lean_ctor_get(v_b_818_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_b_818_);
if (v_isSharedCheck_840_ == 0)
{
v___x_822_ = v_b_818_;
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_inc(v_fst_819_);
lean_dec(v_b_818_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_lt(v_snd_820_, v___x_816_);
if (v___x_824_ == 0)
{
lean_object* v___x_826_; 
if (v_isShared_823_ == 0)
{
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_fst_819_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_snd_820_);
v___x_826_ = v_reuseFailAlloc_828_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
else
{
uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_829_ = 0;
v___x_830_ = lean_array_fget_borrowed(v_edited_817_, v_snd_820_);
v___x_831_ = lean_box(v___x_829_);
lean_inc(v___x_830_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_830_);
lean_ctor_set(v___x_822_, 0, v___x_831_);
v___x_833_ = v___x_822_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_830_);
v___x_833_ = v_reuseFailAlloc_839_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_834_ = lean_array_push(v_fst_819_, v___x_833_);
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_add(v_snd_820_, v___x_835_);
lean_dec(v_snd_820_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_834_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6___boxed(lean_object* v___x_841_, lean_object* v_edited_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Diff_diff___redArg___lam__6(v___x_841_, v_edited_842_, v_b_843_);
lean_dec_ref(v_edited_842_);
lean_dec(v___x_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg(lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_original_857_, lean_object* v_edited_858_){
_start:
{
lean_object* v___x_859_; lean_object* v_i_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_859_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_i_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_array_get_size(v_original_857_);
v___x_862_ = lean_nat_dec_lt(v_i_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___f_863_; size_t v_sz_864_; size_t v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_original_857_);
lean_dec(v_inst_856_);
lean_dec_ref(v_inst_855_);
lean_dec_ref(v_inst_854_);
v___f_863_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__0));
v_sz_864_ = lean_array_size(v_edited_858_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_859_, v___f_863_, v_sz_864_, v___x_865_, v_edited_858_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_array_get_size(v_edited_858_);
v___x_868_ = lean_nat_dec_lt(v_i_860_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___f_869_; size_t v_sz_870_; size_t v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_edited_858_);
lean_dec(v_inst_856_);
lean_dec_ref(v_inst_855_);
lean_dec_ref(v_inst_854_);
v___f_869_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__1));
v_sz_870_ = lean_array_size(v_original_857_);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_859_, v___f_869_, v_sz_870_, v___x_871_, v_original_857_);
return v___x_872_;
}
else
{
lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_ds_876_; lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v_snd_881_; lean_object* v_fst_882_; lean_object* v_fst_883_; lean_object* v_snd_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_905_; 
lean_inc_ref_n(v_edited_858_, 2);
lean_inc_ref(v_inst_854_);
lean_inc_ref_n(v_original_857_, 2);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__4), 10, 7);
lean_closure_set(v___f_873_, 0, v___x_861_);
lean_closure_set(v___f_873_, 1, v_inst_856_);
lean_closure_set(v___f_873_, 2, v_original_857_);
lean_closure_set(v___f_873_, 3, v_inst_854_);
lean_closure_set(v___f_873_, 4, v___x_859_);
lean_closure_set(v___f_873_, 5, v___x_867_);
lean_closure_set(v___f_873_, 6, v_edited_858_);
v___x_874_ = l_Array_toSubarray___redArg(v_original_857_, v_i_860_, v___x_861_);
v___x_875_ = l_Array_toSubarray___redArg(v_edited_858_, v_i_860_, v___x_867_);
v_ds_876_ = l_Lean_Diff_lcs___redArg(v_inst_854_, v_inst_855_, v___x_874_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__4));
v_sz_878_ = lean_array_size(v_ds_876_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_859_, v_ds_876_, v___f_873_, v_sz_878_, v___x_879_, v___x_877_);
v_snd_881_ = lean_ctor_get(v___x_880_, 1);
lean_inc(v_snd_881_);
v_fst_882_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_fst_882_);
lean_dec(v___x_880_);
v_fst_883_ = lean_ctor_get(v_snd_881_, 0);
v_snd_884_ = lean_ctor_get(v_snd_881_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_snd_881_);
if (v_isSharedCheck_905_ == 0)
{
v___x_886_ = v_snd_881_;
v_isShared_887_ = v_isSharedCheck_905_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_snd_884_);
lean_inc(v_fst_883_);
lean_dec(v_snd_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_905_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___f_888_; lean_object* v___x_890_; 
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_888_, 0, v___x_861_);
lean_closure_set(v___f_888_, 1, v_original_857_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v_fst_883_);
lean_ctor_set(v___x_886_, 0, v_fst_882_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_fst_882_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_fst_883_);
v___x_890_ = v_reuseFailAlloc_904_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v_fst_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_902_; 
v___x_891_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_859_, v___f_888_, v___x_890_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_891_, 1);
lean_dec(v_unused_903_);
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_902_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_fst_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_902_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___f_896_; lean_object* v___x_898_; 
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_896_, 0, v___x_867_);
lean_closure_set(v___f_896_, 1, v_edited_858_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_snd_884_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_fst_892_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_snd_884_);
v___x_898_ = v_reuseFailAlloc_901_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v_fst_900_; 
v___x_899_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_859_, v___f_896_, v___x_898_);
v_fst_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_fst_900_);
lean_dec(v___x_899_);
return v_fst_900_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object* v_00_u03b1_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_original_910_, lean_object* v_edited_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Diff_diff___redArg(v_inst_907_, v_inst_908_, v_inst_909_, v_original_910_, v_edited_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object* v_inst_914_, lean_object* v_out_915_, lean_object* v_a_916_, lean_object* v_x_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_fst_919_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_fst_919_);
v_snd_920_ = lean_ctor_get(v_a_916_, 1);
lean_inc(v_snd_920_);
lean_dec_ref(v_a_916_);
v___x_921_ = lean_apply_1(v_inst_914_, v_snd_920_);
v___x_922_ = lean_string_dec_eq(v___x_921_, v_out_915_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_923_ = lean_unbox(v_fst_919_);
lean_dec(v_fst_919_);
v___x_924_ = l_Lean_Diff_Action_linePrefix(v___x_923_);
v___x_925_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
v___x_927_ = lean_string_append(v___x_926_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_928_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
v___x_930_ = lean_string_append(v___y_918_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
else
{
uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v___x_921_);
v___x_932_ = lean_unbox(v_fst_919_);
lean_dec(v_fst_919_);
v___x_933_ = l_Lean_Diff_Action_linePrefix(v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
v___x_936_ = lean_string_append(v___y_918_, v___x_935_);
lean_dec_ref(v___x_935_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object* v_inst_938_, lean_object* v_out_939_, lean_object* v_a_940_, lean_object* v_x_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Diff_linesToString___redArg___lam__0(v_inst_938_, v_out_939_, v_a_940_, v_x_941_, v___y_942_);
lean_dec_ref(v_out_939_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object* v_inst_945_, lean_object* v_lines_946_){
_start:
{
lean_object* v___x_947_; lean_object* v_out_948_; lean_object* v___f_949_; size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v___x_947_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_out_948_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___closed__0));
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Diff_linesToString___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_949_, 0, v_inst_945_);
lean_closure_set(v___f_949_, 1, v_out_948_);
v_sz_950_ = lean_array_size(v_lines_946_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_947_, v_lines_946_, v___f_949_, v_sz_950_, v___x_951_, v_out_948_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object* v_00_u03b1_953_, lean_object* v_inst_954_, lean_object* v_lines_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Diff_linesToString___redArg(v_inst_954_, v_lines_955_);
return v___x_956_;
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
