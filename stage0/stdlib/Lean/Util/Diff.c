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
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Diff_Action_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Diff_Action_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Diff_Action_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg(lean_object* v_insert_22_){
_start:
{
lean_inc(v_insert_22_);
return v_insert_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg___boxed(lean_object* v_insert_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Diff_Action_insert_elim___redArg(v_insert_23_);
lean_dec(v_insert_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_insert_28_){
_start:
{
lean_inc(v_insert_28_);
return v_insert_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_insert_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Diff_Action_insert_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_insert_32_);
lean_dec(v_insert_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg(lean_object* v_delete_35_){
_start:
{
lean_inc(v_delete_35_);
return v_delete_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg___boxed(lean_object* v_delete_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Diff_Action_delete_elim___redArg(v_delete_36_);
lean_dec(v_delete_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_delete_41_){
_start:
{
lean_inc(v_delete_41_);
return v_delete_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_delete_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Diff_Action_delete_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_delete_45_);
lean_dec(v_delete_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg(lean_object* v_skip_48_){
_start:
{
lean_inc(v_skip_48_);
return v_skip_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg___boxed(lean_object* v_skip_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Diff_Action_skip_elim___redArg(v_skip_49_);
lean_dec(v_skip_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_skip_54_){
_start:
{
lean_inc(v_skip_54_);
return v_skip_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_skip_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Diff_Action_skip_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_skip_58_);
lean_dec(v_skip_58_);
return v_res_60_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__7(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr(uint8_t v_x_74_, lean_object* v_prec_75_){
_start:
{
lean_object* v___y_77_; lean_object* v___y_84_; lean_object* v___y_91_; 
switch(v_x_74_)
{
case 0:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_75_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_77_ = v___x_99_;
goto v___jp_76_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_77_ = v___x_100_;
goto v___jp_76_;
}
}
case 1:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1024u);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_prec_75_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_84_ = v___x_103_;
goto v___jp_83_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_84_ = v___x_104_;
goto v___jp_83_;
}
}
default: 
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_75_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_91_ = v___x_107_;
goto v___jp_90_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_91_ = v___x_108_;
goto v___jp_90_;
}
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__1));
lean_inc(v___y_77_);
v___x_79_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_79_, 0, v___y_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = 0;
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_80_);
v___x_82_ = l_Repr_addAppParen(v___x_81_, v_prec_75_);
return v___x_82_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__3));
lean_inc(v___y_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_75_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__5));
lean_inc(v___y_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___y_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = l_Repr_addAppParen(v___x_95_, v_prec_75_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr___boxed(lean_object* v_x_109_, lean_object* v_prec_110_){
_start:
{
uint8_t v_x_171__boxed_111_; lean_object* v_res_112_; 
v_x_171__boxed_111_ = lean_unbox(v_x_109_);
v_res_112_ = l_Lean_Diff_instReprAction_repr(v_x_171__boxed_111_, v_prec_110_);
lean_dec(v_prec_110_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t v_x_115_, uint8_t v_y_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_117_ = lean_box(v_x_115_);
v___x_118_ = lean_obj_tag_nat(v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = lean_box(v_y_116_);
v___x_120_ = lean_obj_tag_nat(v___x_119_);
lean_dec(v___x_119_);
v___x_121_ = lean_nat_dec_eq(v___x_118_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instBEqAction_beq___boxed(lean_object* v_x_122_, lean_object* v_y_123_){
_start:
{
uint8_t v_x_24__boxed_124_; uint8_t v_y_25__boxed_125_; uint8_t v_res_126_; lean_object* v_r_127_; 
v_x_24__boxed_124_ = lean_unbox(v_x_122_);
v_y_25__boxed_125_ = lean_unbox(v_y_123_);
v_res_126_ = l_Lean_Diff_instBEqAction_beq(v_x_24__boxed_124_, v_y_25__boxed_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint64_t l_Lean_Diff_instHashableAction_hash(uint8_t v_x_130_){
_start:
{
switch(v_x_130_)
{
case 0:
{
uint64_t v___x_131_; 
v___x_131_ = 0ULL;
return v___x_131_;
}
case 1:
{
uint64_t v___x_132_; 
v___x_132_ = 1ULL;
return v___x_132_;
}
default: 
{
uint64_t v___x_133_; 
v___x_133_ = 2ULL;
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instHashableAction_hash___boxed(lean_object* v_x_134_){
_start:
{
uint8_t v_x_40__boxed_135_; uint64_t v_res_136_; lean_object* v_r_137_; 
v_x_40__boxed_135_ = lean_unbox(v_x_134_);
v_res_136_ = l_Lean_Diff_instHashableAction_hash(v_x_40__boxed_135_);
v_r_137_ = lean_box_uint64(v_res_136_);
return v_r_137_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction_default(void){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction(void){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__0));
return v___x_146_;
}
case 1:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__1));
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
v___x_148_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__2));
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_36__boxed_150_; lean_object* v_res_151_; 
v_x_36__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_Diff_instToStringAction___lam__0(v_x_36__boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix(uint8_t v_x_157_){
_start:
{
switch(v_x_157_)
{
case 0:
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__0));
return v___x_158_;
}
case 1:
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__1));
return v___x_159_;
}
default: 
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix___boxed(lean_object* v_x_161_){
_start:
{
uint8_t v_x_31__boxed_162_; lean_object* v_res_163_; 
v_x_31__boxed_162_ = lean_unbox(v_x_161_);
v_res_163_ = l_Lean_Diff_Action_linePrefix(v_x_31__boxed_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___redArg(lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_histogram_166_, lean_object* v_index_167_, lean_object* v_val_168_){
_start:
{
lean_object* v___x_169_; 
lean_inc(v_val_168_);
lean_inc_ref(v_inst_165_);
lean_inc_ref(v_inst_164_);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_164_, v_inst_165_, v_histogram_166_, v_val_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v_index_167_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_174_, 0, v___x_170_);
lean_ctor_set(v___x_174_, 1, v___x_171_);
lean_ctor_set(v___x_174_, 2, v___x_172_);
lean_ctor_set(v___x_174_, 3, v___x_173_);
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_164_, v_inst_165_, v_histogram_166_, v_val_168_, v___x_174_);
return v___x_175_;
}
else
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_197_; 
v_val_176_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_197_ == 0)
{
v___x_178_ = v___x_169_;
v_isShared_179_ = v_isSharedCheck_197_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v___x_169_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_197_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_leftCount_180_; lean_object* v_rightCount_181_; lean_object* v_rightIndex_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_leftCount_180_ = lean_ctor_get(v_val_176_, 0);
v_rightCount_181_ = lean_ctor_get(v_val_176_, 2);
v_rightIndex_182_ = lean_ctor_get(v_val_176_, 3);
v_isSharedCheck_195_ = !lean_is_exclusive(v_val_176_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_val_176_, 1);
lean_dec(v_unused_196_);
v___x_184_ = v_val_176_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_rightIndex_182_);
lean_inc(v_rightCount_181_);
lean_inc(v_leftCount_180_);
lean_dec(v_val_176_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_leftCount_180_, v___x_186_);
lean_dec(v_leftCount_180_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v_index_167_);
v___x_189_ = v___x_178_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_index_167_);
v___x_189_ = v_reuseFailAlloc_194_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_189_);
lean_ctor_set(v___x_184_, 0, v___x_187_);
v___x_191_ = v___x_184_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_rightCount_181_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_rightIndex_182_);
v___x_191_ = v_reuseFailAlloc_193_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_164_, v_inst_165_, v_histogram_166_, v_val_168_, v___x_191_);
return v___x_192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_lsize_201_, lean_object* v_rsize_202_, lean_object* v_histogram_203_, lean_object* v_index_204_, lean_object* v_val_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_199_, v_inst_200_, v_histogram_203_, v_index_204_, v_val_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___boxed(lean_object* v_00_u03b1_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_lsize_210_, lean_object* v_rsize_211_, lean_object* v_histogram_212_, lean_object* v_index_213_, lean_object* v_val_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Diff_Histogram_addLeft(v_00_u03b1_207_, v_inst_208_, v_inst_209_, v_lsize_210_, v_rsize_211_, v_histogram_212_, v_index_213_, v_val_214_);
lean_dec(v_rsize_211_);
lean_dec(v_lsize_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_histogram_218_, lean_object* v_index_219_, lean_object* v_val_220_){
_start:
{
lean_object* v___x_221_; 
lean_inc(v_val_220_);
lean_inc_ref(v_inst_217_);
lean_inc_ref(v_inst_216_);
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_216_, v_inst_217_, v_histogram_218_, v_val_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_box(0);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_index_219_);
v___x_226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_226_, 0, v___x_222_);
lean_ctor_set(v___x_226_, 1, v___x_223_);
lean_ctor_set(v___x_226_, 2, v___x_224_);
lean_ctor_set(v___x_226_, 3, v___x_225_);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_216_, v_inst_217_, v_histogram_218_, v_val_220_, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_249_; 
v_val_228_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_249_ == 0)
{
v___x_230_ = v___x_221_;
v_isShared_231_ = v_isSharedCheck_249_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_val_228_);
lean_dec(v___x_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_249_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_leftCount_232_; lean_object* v_leftIndex_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_246_; 
v_leftCount_232_ = lean_ctor_get(v_val_228_, 0);
v_leftIndex_233_ = lean_ctor_get(v_val_228_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_val_228_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_247_ = lean_ctor_get(v_val_228_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_val_228_, 2);
lean_dec(v_unused_248_);
v___x_235_ = v_val_228_;
v_isShared_236_ = v_isSharedCheck_246_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_leftIndex_233_);
lean_inc(v_leftCount_232_);
lean_dec(v_val_228_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_246_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_leftCount_232_, v___x_237_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v_index_219_);
v___x_240_ = v___x_230_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_index_219_);
v___x_240_ = v_reuseFailAlloc_245_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 3, v___x_240_);
lean_ctor_set(v___x_235_, 2, v___x_238_);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_leftCount_232_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_leftIndex_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v___x_240_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_216_, v_inst_217_, v_histogram_218_, v_val_220_, v___x_242_);
return v___x_243_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight(lean_object* v_00_u03b1_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_lsize_253_, lean_object* v_rsize_254_, lean_object* v_histogram_255_, lean_object* v_index_256_, lean_object* v_val_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_251_, v_inst_252_, v_histogram_255_, v_index_256_, v_val_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___boxed(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_lsize_262_, lean_object* v_rsize_263_, lean_object* v_histogram_264_, lean_object* v_index_265_, lean_object* v_val_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Diff_Histogram_addRight(v_00_u03b1_259_, v_inst_260_, v_inst_261_, v_lsize_262_, v_rsize_263_, v_histogram_264_, v_index_265_, v_val_266_);
lean_dec(v_rsize_263_);
lean_dec(v_lsize_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(lean_object* v_inst_268_, lean_object* v_left_269_, lean_object* v_right_270_, lean_object* v_pref_271_){
_start:
{
lean_object* v_start_272_; lean_object* v_stop_273_; lean_object* v_i_274_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_start_272_ = lean_ctor_get(v_left_269_, 1);
v_stop_273_ = lean_ctor_get(v_left_269_, 2);
v_i_274_ = lean_array_get_size(v_pref_271_);
v___x_280_ = lean_nat_sub(v_stop_273_, v_start_272_);
v___x_281_ = lean_nat_dec_lt(v_i_274_, v___x_280_);
lean_dec(v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_inst_268_);
goto v___jp_275_;
}
else
{
lean_object* v_start_282_; lean_object* v_stop_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_start_282_ = lean_ctor_get(v_right_270_, 1);
v_stop_283_ = lean_ctor_get(v_right_270_, 2);
v___x_284_ = lean_nat_sub(v_stop_283_, v_start_282_);
v___x_285_ = lean_nat_dec_lt(v_i_274_, v___x_284_);
lean_dec(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v_inst_268_);
goto v___jp_275_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = l_Subarray_get___redArg(v_left_269_, v_i_274_);
v___x_287_ = l_Subarray_get___redArg(v_right_270_, v_i_274_);
lean_inc_ref(v_inst_268_);
lean_inc(v___x_286_);
v___x_288_ = lean_apply_2(v_inst_268_, v___x_286_, v___x_287_);
v___x_289_ = lean_unbox(v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v___x_286_);
lean_dec_ref(v_inst_268_);
v___x_290_ = l_Subarray_drop___redArg(v_left_269_, v_i_274_);
v___x_291_ = l_Subarray_drop___redArg(v_right_270_, v_i_274_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_pref_271_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_array_push(v_pref_271_, v___x_286_);
v_pref_271_ = v___x_294_;
goto _start;
}
}
}
v___jp_275_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_276_ = l_Subarray_drop___redArg(v_left_269_, v_i_274_);
v___x_277_ = l_Subarray_drop___redArg(v_right_270_, v_i_274_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_pref_271_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(lean_object* v_00_u03b1_296_, lean_object* v_inst_297_, lean_object* v_left_298_, lean_object* v_right_299_, lean_object* v_pref_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_297_, v_left_298_, v_right_299_, v_pref_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___redArg(lean_object* v_inst_304_, lean_object* v_left_305_, lean_object* v_right_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_308_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_304_, v_left_305_, v_right_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_left_311_, lean_object* v_right_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Diff_matchPrefix___redArg(v_inst_310_, v_left_311_, v_right_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(lean_object* v_it_314_, lean_object* v_acc_315_, lean_object* v_recur_316_){
_start:
{
lean_object* v_array_317_; lean_object* v_start_318_; lean_object* v_stop_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_332_; 
v_array_317_ = lean_ctor_get(v_it_314_, 0);
v_start_318_ = lean_ctor_get(v_it_314_, 1);
v_stop_319_ = lean_ctor_get(v_it_314_, 2);
v_isSharedCheck_332_ = !lean_is_exclusive(v_it_314_);
if (v_isSharedCheck_332_ == 0)
{
v___x_321_ = v_it_314_;
v_isShared_322_ = v_isSharedCheck_332_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_stop_319_);
lean_inc(v_start_318_);
lean_inc(v_array_317_);
lean_dec(v_it_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_332_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_lt(v_start_318_, v_stop_319_);
if (v___x_323_ == 0)
{
lean_del_object(v___x_321_);
lean_dec(v_stop_319_);
lean_dec(v_start_318_);
lean_dec_ref(v_array_317_);
lean_dec_ref(v_recur_316_);
return v_acc_315_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_start_318_, v___x_324_);
lean_inc_ref(v_array_317_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_325_);
v___x_327_ = v___x_321_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_array_317_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_stop_319_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_array_fget(v_array_317_, v_start_318_);
lean_dec(v_start_318_);
lean_dec_ref(v_array_317_);
v___x_329_ = lean_array_push(v_acc_315_, v___x_328_);
v___x_330_ = lean_apply_3(v_recur_316_, v___x_327_, v___x_329_, lean_box(0));
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(lean_object* v_inst_334_, lean_object* v_left_335_, lean_object* v_right_336_, lean_object* v_i_337_){
_start:
{
lean_object* v_start_338_; lean_object* v_stop_339_; lean_object* v___f_340_; lean_object* v___x_341_; uint8_t v___x_355_; 
v_start_338_ = lean_ctor_get(v_left_335_, 1);
v_stop_339_ = lean_ctor_get(v_left_335_, 2);
v___f_340_ = ((lean_object*)(l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0));
v___x_341_ = lean_nat_sub(v_stop_339_, v_start_338_);
v___x_355_ = lean_nat_dec_lt(v_i_337_, v___x_341_);
if (v___x_355_ == 0)
{
lean_dec_ref(v_inst_334_);
goto v___jp_342_;
}
else
{
lean_object* v_start_356_; lean_object* v_stop_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_start_356_ = lean_ctor_get(v_right_336_, 1);
v_stop_357_ = lean_ctor_get(v_right_336_, 2);
v___x_358_ = lean_nat_sub(v_stop_357_, v_start_356_);
v___x_359_ = lean_nat_dec_lt(v_i_337_, v___x_358_);
if (v___x_359_ == 0)
{
lean_dec(v___x_358_);
lean_dec_ref(v_inst_334_);
goto v___jp_342_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_360_ = lean_nat_sub(v___x_341_, v_i_337_);
lean_dec(v___x_341_);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_sub(v___x_360_, v___x_361_);
v___x_363_ = l_Subarray_get___redArg(v_left_335_, v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = lean_nat_sub(v___x_358_, v_i_337_);
lean_dec(v___x_358_);
v___x_365_ = lean_nat_sub(v___x_364_, v___x_361_);
v___x_366_ = l_Subarray_get___redArg(v_right_336_, v___x_365_);
lean_dec(v___x_365_);
lean_inc_ref(v_inst_334_);
v___x_367_ = lean_apply_2(v_inst_334_, v___x_363_, v___x_366_);
v___x_368_ = lean_unbox(v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_i_337_);
lean_dec_ref(v_inst_334_);
lean_inc_ref(v_left_335_);
v___x_369_ = l_Subarray_take___redArg(v_left_335_, v___x_360_);
v___x_370_ = l_Subarray_take___redArg(v_right_336_, v___x_364_);
lean_dec(v___x_364_);
v___x_371_ = l_Subarray_drop___redArg(v_left_335_, v___x_360_);
lean_dec(v___x_360_);
v___x_372_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_373_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_340_, v___x_371_, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_370_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_369_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v___x_364_);
lean_dec(v___x_360_);
v___x_376_ = lean_nat_add(v_i_337_, v___x_361_);
lean_dec(v_i_337_);
v_i_337_ = v___x_376_;
goto _start;
}
}
}
v___jp_342_:
{
lean_object* v_start_343_; lean_object* v_stop_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_start_343_ = lean_ctor_get(v_right_336_, 1);
v_stop_344_ = lean_ctor_get(v_right_336_, 2);
v___x_345_ = lean_nat_sub(v___x_341_, v_i_337_);
lean_dec(v___x_341_);
lean_inc_ref(v_left_335_);
v___x_346_ = l_Subarray_take___redArg(v_left_335_, v___x_345_);
v___x_347_ = lean_nat_sub(v_stop_344_, v_start_343_);
v___x_348_ = lean_nat_sub(v___x_347_, v_i_337_);
lean_dec(v_i_337_);
lean_dec(v___x_347_);
v___x_349_ = l_Subarray_take___redArg(v_right_336_, v___x_348_);
lean_dec(v___x_348_);
v___x_350_ = l_Subarray_drop___redArg(v_left_335_, v___x_345_);
lean_dec(v___x_345_);
v___x_351_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_352_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_340_, v___x_350_, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_346_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_left_380_, lean_object* v_right_381_, lean_object* v_i_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_379_, v_left_380_, v_right_381_, v_i_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object* v_inst_384_, lean_object* v_left_385_, lean_object* v_right_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_384_, v_left_385_, v_right_386_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object* v_00_u03b1_389_, lean_object* v_inst_390_, lean_object* v_left_391_, lean_object* v_right_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Diff_matchSuffix___redArg(v_inst_390_, v_left_391_, v_right_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object* v___x_394_, lean_object* v_fst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_next_398_, lean_object* v_acc_399_, lean_object* v_h_400_, lean_object* v_G_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_nat_dec_lt(v_next_398_, v___x_394_);
if (v___x_402_ == 0)
{
lean_dec_ref(v_G_401_);
lean_dec(v_next_398_);
lean_dec_ref(v_inst_397_);
lean_dec_ref(v_inst_396_);
return v_acc_399_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_403_ = l_Subarray_get___redArg(v_fst_395_, v_next_398_);
lean_inc(v_next_398_);
v___x_404_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_396_, v_inst_397_, v_acc_399_, v_next_398_, v___x_403_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_add(v_next_398_, v___x_405_);
lean_dec(v_next_398_);
v___x_407_ = lean_apply_4(v_G_401_, v___x_406_, v___x_404_, lean_box(0), lean_box(0));
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0___boxed(lean_object* v___x_408_, lean_object* v_fst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_next_412_, lean_object* v_acc_413_, lean_object* v_h_414_, lean_object* v_G_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Diff_lcs___redArg___lam__0(v___x_408_, v_fst_409_, v_inst_410_, v_inst_411_, v_next_412_, v_acc_413_, v_h_414_, v_G_415_);
lean_dec_ref(v_fst_409_);
lean_dec(v___x_408_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object* v___x_417_, lean_object* v_fst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_next_421_, lean_object* v_acc_422_, lean_object* v_h_423_, lean_object* v_G_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_lt(v_next_421_, v___x_417_);
if (v___x_425_ == 0)
{
lean_dec_ref(v_G_424_);
lean_dec(v_next_421_);
lean_dec_ref(v_inst_420_);
lean_dec_ref(v_inst_419_);
return v_acc_422_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = l_Subarray_get___redArg(v_fst_418_, v_next_421_);
lean_inc(v_next_421_);
v___x_427_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_419_, v_inst_420_, v_acc_422_, v_next_421_, v___x_426_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_next_421_, v___x_428_);
lean_dec(v_next_421_);
v___x_430_ = lean_apply_4(v_G_424_, v___x_429_, v___x_427_, lean_box(0), lean_box(0));
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1___boxed(lean_object* v___x_431_, lean_object* v_fst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_next_435_, lean_object* v_acc_436_, lean_object* v_h_437_, lean_object* v_G_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Diff_lcs___redArg___lam__1(v___x_431_, v_fst_432_, v_inst_433_, v_inst_434_, v_next_435_, v_acc_436_, v_h_437_, v_G_438_);
lean_dec_ref(v_fst_432_);
lean_dec(v___x_431_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object* v_a_440_, lean_object* v_x_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_snd_443_; lean_object* v_leftIndex_444_; 
v_snd_443_ = lean_ctor_get(v_a_440_, 1);
lean_inc(v_snd_443_);
v_leftIndex_444_ = lean_ctor_get(v_snd_443_, 1);
lean_inc(v_leftIndex_444_);
if (lean_obj_tag(v_leftIndex_444_) == 1)
{
lean_object* v_rightIndex_445_; 
v_rightIndex_445_ = lean_ctor_get(v_snd_443_, 3);
lean_inc(v_rightIndex_445_);
if (lean_obj_tag(v_rightIndex_445_) == 1)
{
if (lean_obj_tag(v___y_442_) == 0)
{
lean_object* v_fst_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_474_; 
v_fst_446_ = lean_ctor_get(v_a_440_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_a_440_, 1);
lean_dec(v_unused_475_);
v___x_448_ = v_a_440_;
v_isShared_449_ = v_isSharedCheck_474_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_fst_446_);
lean_dec(v_a_440_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_474_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_leftCount_450_; lean_object* v_rightCount_451_; lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_473_; 
v_leftCount_450_ = lean_ctor_get(v_snd_443_, 0);
lean_inc(v_leftCount_450_);
v_rightCount_451_ = lean_ctor_get(v_snd_443_, 2);
lean_inc(v_rightCount_451_);
lean_dec(v_snd_443_);
v_val_452_ = lean_ctor_get(v_leftIndex_444_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_leftIndex_444_);
if (v_isSharedCheck_473_ == 0)
{
v___x_454_ = v_leftIndex_444_;
v_isShared_455_ = v_isSharedCheck_473_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_leftIndex_444_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_473_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_472_; 
v_val_456_ = lean_ctor_get(v_rightIndex_445_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_rightIndex_445_);
if (v_isSharedCheck_472_ == 0)
{
v___x_458_ = v_rightIndex_445_;
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v_rightIndex_445_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_nat_add(v_leftCount_450_, v_rightCount_451_);
lean_dec(v_rightCount_451_);
lean_dec(v_leftCount_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 1, v_val_456_);
lean_ctor_set(v___x_448_, 0, v_val_452_);
v___x_462_ = v___x_448_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_val_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_val_456_);
v___x_462_ = v_reuseFailAlloc_471_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_fst_446_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_460_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_464_);
v___x_466_ = v___x_458_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_466_);
v___x_468_ = v___x_454_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_476_; lean_object* v_fst_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_518_; 
v_val_476_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_val_476_);
v_fst_477_ = lean_ctor_get(v_a_440_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_a_440_, 1);
lean_dec(v_unused_519_);
v___x_479_ = v_a_440_;
v_isShared_480_ = v_isSharedCheck_518_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_fst_477_);
lean_dec(v_a_440_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_518_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_leftCount_481_; lean_object* v_rightCount_482_; lean_object* v_val_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_517_; 
v_leftCount_481_ = lean_ctor_get(v_snd_443_, 0);
lean_inc(v_leftCount_481_);
v_rightCount_482_ = lean_ctor_get(v_snd_443_, 2);
lean_inc(v_rightCount_482_);
lean_dec(v_snd_443_);
v_val_483_ = lean_ctor_get(v_leftIndex_444_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_leftIndex_444_);
if (v_isSharedCheck_517_ == 0)
{
v___x_485_ = v_leftIndex_444_;
v_isShared_486_ = v_isSharedCheck_517_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_val_483_);
lean_dec(v_leftIndex_444_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_517_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_val_487_; lean_object* v_fst_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_515_; 
v_val_487_ = lean_ctor_get(v_rightIndex_445_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v_rightIndex_445_, 1);
v_fst_488_ = lean_ctor_get(v_val_476_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_val_476_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_val_476_, 1);
lean_dec(v_unused_516_);
v___x_490_ = v_val_476_;
v_isShared_491_ = v_isSharedCheck_515_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_fst_488_);
lean_dec(v_val_476_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_515_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_nat_add(v_leftCount_481_, v_rightCount_482_);
lean_dec(v_rightCount_482_);
lean_dec(v_leftCount_481_);
v___x_493_ = lean_nat_dec_lt(v___x_492_, v_fst_488_);
lean_dec(v_fst_488_);
if (v___x_493_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v___x_492_);
lean_del_object(v___x_490_);
lean_dec(v_val_487_);
lean_dec(v_val_483_);
lean_del_object(v___x_479_);
lean_dec(v_fst_477_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___y_442_);
v___x_495_ = v___x_485_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___y_442_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_513_; 
v_isSharedCheck_513_ = !lean_is_exclusive(v___y_442_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v___y_442_, 0);
lean_dec(v_unused_514_);
v___x_498_ = v___y_442_;
v_isShared_499_ = v_isSharedCheck_513_;
goto v_resetjp_497_;
}
else
{
lean_dec(v___y_442_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_513_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_val_487_);
lean_ctor_set(v___x_490_, 0, v_val_483_);
v___x_501_ = v___x_490_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_val_487_);
v___x_501_ = v_reuseFailAlloc_512_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_501_);
v___x_503_ = v___x_479_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_fst_477_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_511_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_492_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_504_);
v___x_506_ = v___x_498_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_506_);
v___x_508_ = v___x_485_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
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
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_rightIndex_445_);
lean_dec(v_snd_443_);
lean_dec_ref(v_a_440_);
v_isSharedCheck_526_ = !lean_is_exclusive(v_leftIndex_444_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v_leftIndex_444_, 0);
lean_dec(v_unused_527_);
v___x_521_ = v_leftIndex_444_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_leftIndex_444_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___y_442_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___y_442_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v_leftIndex_444_);
lean_dec(v_snd_443_);
lean_dec_ref(v_a_440_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___y_442_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object* v_a_529_, lean_object* v_b_530_, lean_object* v_d_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_529_);
lean_ctor_set(v___x_532_, 1, v_b_530_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_d_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__4(lean_object* v___x_534_, lean_object* v___f_535_, lean_object* v_l_536_, lean_object* v_acc_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_534_, v___f_535_, v_acc_537_, v_l_536_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__10(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_box(0);
v___x_559_ = lean_unsigned_to_nat(16u);
v___x_560_ = lean_mk_array(v___x_559_, v___x_558_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__11(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_hist_563_; 
v___x_561_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__10, &l_Lean_Diff_lcs___redArg___closed__10_once, _init_l_Lean_Diff_lcs___redArg___closed__10);
v___x_562_ = lean_unsigned_to_nat(0u);
v_hist_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_563_, 0, v___x_562_);
lean_ctor_set(v_hist_563_, 1, v___x_561_);
return v_hist_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_left_571_, lean_object* v_right_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_snd_575_; lean_object* v_fst_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; lean_object* v_snd_580_; lean_object* v_fst_581_; lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v_start_584_; lean_object* v_stop_585_; lean_object* v_start_586_; lean_object* v_stop_587_; lean_object* v___x_588_; lean_object* v_hist_589_; lean_object* v___x_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v_buckets_596_; lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___y_600_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_573_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
lean_inc_ref_n(v_inst_569_, 4);
v___x_574_ = l_Lean_Diff_matchPrefix___redArg(v_inst_569_, v_left_571_, v_right_572_);
v_snd_575_ = lean_ctor_get(v___x_574_, 1);
lean_inc(v_snd_575_);
v_fst_576_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_fst_576_);
lean_dec_ref(v___x_574_);
v_fst_577_ = lean_ctor_get(v_snd_575_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_snd_575_, 1);
lean_inc(v_snd_578_);
lean_dec(v_snd_575_);
v___x_579_ = l_Lean_Diff_matchSuffix___redArg(v_inst_569_, v_fst_577_, v_snd_578_);
v_snd_580_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_snd_580_);
v_fst_581_ = lean_ctor_get(v___x_579_, 0);
lean_inc_n(v_fst_581_, 2);
lean_dec_ref(v___x_579_);
v_fst_582_ = lean_ctor_get(v_snd_580_, 0);
lean_inc_n(v_fst_582_, 2);
v_snd_583_ = lean_ctor_get(v_snd_580_, 1);
lean_inc(v_snd_583_);
lean_dec(v_snd_580_);
v_start_584_ = lean_ctor_get(v_fst_581_, 1);
v_stop_585_ = lean_ctor_get(v_fst_581_, 2);
v_start_586_ = lean_ctor_get(v_fst_582_, 1);
v_stop_587_ = lean_ctor_get(v_fst_582_, 2);
v___x_588_ = lean_unsigned_to_nat(0u);
v_hist_589_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__11, &l_Lean_Diff_lcs___redArg___closed__11_once, _init_l_Lean_Diff_lcs___redArg___closed__11);
v___x_590_ = lean_nat_sub(v_stop_585_, v_start_584_);
lean_inc_ref_n(v_inst_570_, 2);
v___f_591_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_591_, 0, v___x_590_);
lean_closure_set(v___f_591_, 1, v_fst_581_);
lean_closure_set(v___f_591_, 2, v_inst_569_);
lean_closure_set(v___f_591_, 3, v_inst_570_);
v___x_592_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_591_, v___x_588_, v_hist_589_, lean_box(0));
v___x_593_ = lean_nat_sub(v_stop_587_, v_start_586_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_594_, 0, v___x_593_);
lean_closure_set(v___f_594_, 1, v_fst_582_);
lean_closure_set(v___f_594_, 2, v_inst_569_);
lean_closure_set(v___f_594_, 3, v_inst_570_);
v___x_595_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_594_, v___x_588_, v___x_592_, lean_box(0));
v_buckets_596_ = lean_ctor_get(v___x_595_, 1);
lean_inc_ref(v_buckets_596_);
lean_dec(v___x_595_);
v___f_597_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__12));
v___x_598_ = lean_box(0);
v___x_626_ = lean_box(0);
v___x_627_ = lean_array_get_size(v_buckets_596_);
v___x_628_ = lean_nat_dec_lt(v___x_588_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec_ref(v_buckets_596_);
v___y_600_ = v___x_626_;
goto v___jp_599_;
}
else
{
lean_object* v___f_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___f_629_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__14));
v___x_630_ = lean_usize_of_nat(v___x_627_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_573_, v___f_629_, v_buckets_596_, v___x_630_, v___x_631_, v___x_626_);
v___y_600_ = v___x_632_;
goto v___jp_599_;
}
v___jp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = l_List_forIn_x27_loop___redArg(v___x_573_, v___f_597_, v___y_600_, v___x_598_);
lean_dec(v___y_600_);
if (lean_obj_tag(v___x_601_) == 1)
{
lean_object* v_val_602_; lean_object* v_snd_603_; lean_object* v_snd_604_; lean_object* v_fst_605_; lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_608_; lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_611_; lean_object* v_fst_612_; lean_object* v_snd_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_val_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v___x_601_, 1);
v_snd_603_ = lean_ctor_get(v_val_602_, 1);
lean_inc(v_snd_603_);
lean_dec(v_val_602_);
v_snd_604_ = lean_ctor_get(v_snd_603_, 1);
lean_inc(v_snd_604_);
v_fst_605_ = lean_ctor_get(v_snd_603_, 0);
lean_inc(v_fst_605_);
lean_dec(v_snd_603_);
v_fst_606_ = lean_ctor_get(v_snd_604_, 0);
lean_inc(v_fst_606_);
v_snd_607_ = lean_ctor_get(v_snd_604_, 1);
lean_inc(v_snd_607_);
lean_dec(v_snd_604_);
v___x_608_ = l_Subarray_split___redArg(v_fst_581_, v_fst_606_);
lean_dec(v_fst_606_);
v_fst_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_fst_609_);
v_snd_610_ = lean_ctor_get(v___x_608_, 1);
lean_inc(v_snd_610_);
lean_dec_ref(v___x_608_);
v___x_611_ = l_Subarray_split___redArg(v_fst_582_, v_snd_607_);
lean_dec(v_snd_607_);
v_fst_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_fst_612_);
v_snd_613_ = lean_ctor_get(v___x_611_, 1);
lean_inc(v_snd_613_);
lean_dec_ref(v___x_611_);
lean_inc_ref(v_inst_570_);
lean_inc_ref(v_inst_569_);
v___x_614_ = l_Lean_Diff_lcs___redArg(v_inst_569_, v_inst_570_, v_fst_609_, v_fst_612_);
v___x_615_ = l_Array_append___redArg(v_fst_576_, v___x_614_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_616_);
v___x_618_ = lean_array_push(v___x_617_, v_fst_605_);
v___x_619_ = l_Array_append___redArg(v___x_615_, v___x_618_);
lean_dec_ref(v___x_618_);
v___x_620_ = l_Subarray_drop___redArg(v_snd_610_, v___x_616_);
v___x_621_ = l_Subarray_drop___redArg(v_snd_613_, v___x_616_);
v___x_622_ = l_Lean_Diff_lcs___redArg(v_inst_569_, v_inst_570_, v___x_620_, v___x_621_);
v___x_623_ = l_Array_append___redArg(v___x_619_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = l_Array_append___redArg(v___x_623_, v_snd_583_);
lean_dec(v_snd_583_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; 
lean_dec(v___x_601_);
lean_dec(v_fst_582_);
lean_dec(v_fst_581_);
lean_dec_ref(v_inst_570_);
lean_dec_ref(v_inst_569_);
v___x_625_ = l_Array_append___redArg(v_fst_576_, v_snd_583_);
lean_dec(v_snd_583_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object* v_00_u03b1_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_left_636_, lean_object* v_right_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Diff_lcs___redArg(v_inst_634_, v_inst_635_, v_left_636_, v_right_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object* v_x_639_){
_start:
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = 0;
v___x_641_ = lean_box(v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v_x_639_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object* v_x_643_){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = 1;
v___x_645_ = lean_box(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_x_643_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object* v___x_647_, lean_object* v_inst_648_, lean_object* v_original_649_, lean_object* v_inst_650_, lean_object* v_a_651_, lean_object* v_b_652_){
_start:
{
lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_675_; 
v_fst_653_ = lean_ctor_get(v_b_652_, 0);
v_snd_654_ = lean_ctor_get(v_b_652_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_b_652_);
if (v_isSharedCheck_675_ == 0)
{
v___x_656_ = v_b_652_;
v_isShared_657_ = v_isSharedCheck_675_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snd_654_);
lean_inc(v_fst_653_);
lean_dec(v_b_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_675_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_lt(v_snd_654_, v___x_647_);
if (v___x_663_ == 0)
{
lean_dec(v_a_651_);
lean_dec_ref(v_inst_650_);
goto v___jp_658_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_array_get_borrowed(v_inst_648_, v_original_649_, v_snd_654_);
lean_inc(v___x_664_);
v___x_665_ = lean_apply_2(v_inst_650_, v___x_664_, v_a_651_);
v___x_666_ = lean_unbox(v___x_665_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_del_object(v___x_656_);
v___x_667_ = 1;
v___x_668_ = lean_box(v___x_667_);
lean_inc(v___x_664_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_664_);
v___x_670_ = lean_array_push(v_fst_653_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_snd_654_, v___x_671_);
lean_dec(v_snd_654_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_670_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
else
{
goto v___jp_658_;
}
}
v___jp_658_:
{
lean_object* v___x_660_; 
if (v_isShared_657_ == 0)
{
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_fst_653_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_snd_654_);
v___x_660_ = v_reuseFailAlloc_662_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object* v___x_676_, lean_object* v_inst_677_, lean_object* v_original_678_, lean_object* v_inst_679_, lean_object* v_a_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Diff_diff___redArg___lam__2(v___x_676_, v_inst_677_, v_original_678_, v_inst_679_, v_a_680_, v_b_681_);
lean_dec_ref(v_original_678_);
lean_dec(v_inst_677_);
lean_dec(v___x_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object* v___x_683_, lean_object* v_inst_684_, lean_object* v_edited_685_, lean_object* v_inst_686_, lean_object* v_a_687_, lean_object* v_b_688_){
_start:
{
lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_711_; 
v_fst_689_ = lean_ctor_get(v_b_688_, 0);
v_snd_690_ = lean_ctor_get(v_b_688_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_b_688_);
if (v_isSharedCheck_711_ == 0)
{
v___x_692_ = v_b_688_;
v_isShared_693_ = v_isSharedCheck_711_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_689_);
lean_dec(v_b_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_711_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_lt(v_snd_690_, v___x_683_);
if (v___x_699_ == 0)
{
lean_dec(v_a_687_);
lean_dec_ref(v_inst_686_);
goto v___jp_694_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_array_get_borrowed(v_inst_684_, v_edited_685_, v_snd_690_);
lean_inc(v___x_700_);
v___x_701_ = lean_apply_2(v_inst_686_, v___x_700_, v_a_687_);
v___x_702_ = lean_unbox(v___x_701_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_del_object(v___x_692_);
v___x_703_ = 0;
v___x_704_ = lean_box(v___x_703_);
lean_inc(v___x_700_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_700_);
v___x_706_ = lean_array_push(v_fst_689_, v___x_705_);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_snd_690_, v___x_707_);
lean_dec(v_snd_690_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_706_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
goto v___jp_694_;
}
}
v___jp_694_:
{
lean_object* v___x_696_; 
if (v_isShared_693_ == 0)
{
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_fst_689_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_690_);
v___x_696_ = v_reuseFailAlloc_698_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object* v___x_712_, lean_object* v_inst_713_, lean_object* v_edited_714_, lean_object* v_inst_715_, lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Diff_diff___redArg___lam__3(v___x_712_, v_inst_713_, v_edited_714_, v_inst_715_, v_a_716_, v_b_717_);
lean_dec_ref(v_edited_714_);
lean_dec(v_inst_713_);
lean_dec(v___x_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object* v___x_719_, lean_object* v_inst_720_, lean_object* v_original_721_, lean_object* v_inst_722_, lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v_edited_725_, lean_object* v_a_726_, lean_object* v_x_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_snd_729_; lean_object* v_fst_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_776_; 
v_snd_729_ = lean_ctor_get(v___y_728_, 1);
v_fst_730_ = lean_ctor_get(v___y_728_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___y_728_);
if (v_isSharedCheck_776_ == 0)
{
v___x_732_ = v___y_728_;
v_isShared_733_ = v_isSharedCheck_776_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_730_);
lean_dec(v___y_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_776_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_775_; 
v_fst_734_ = lean_ctor_get(v_snd_729_, 0);
v_snd_735_ = lean_ctor_get(v_snd_729_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_snd_729_);
if (v_isSharedCheck_775_ == 0)
{
v___x_737_ = v_snd_729_;
v_isShared_738_ = v_isSharedCheck_775_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_735_);
lean_inc(v_fst_734_);
lean_dec(v_snd_729_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_775_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___f_739_; lean_object* v___x_741_; 
lean_inc(v_a_726_);
lean_inc_ref(v_inst_722_);
lean_inc(v_inst_720_);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_739_, 0, v___x_719_);
lean_closure_set(v___f_739_, 1, v_inst_720_);
lean_closure_set(v___f_739_, 2, v_original_721_);
lean_closure_set(v___f_739_, 3, v_inst_722_);
lean_closure_set(v___f_739_, 4, v_a_726_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v_fst_734_);
lean_ctor_set(v___x_737_, 0, v_fst_730_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_fst_730_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_fst_734_);
v___x_741_ = v_reuseFailAlloc_774_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_773_; 
lean_inc_ref(v___x_723_);
v___x_742_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_723_, v___f_739_, v___x_741_);
v_fst_743_ = lean_ctor_get(v___x_742_, 0);
v_snd_744_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_773_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_773_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_773_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___f_748_; lean_object* v___x_750_; 
lean_inc(v_a_726_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_748_, 0, v___x_724_);
lean_closure_set(v___f_748_, 1, v_inst_720_);
lean_closure_set(v___f_748_, 2, v_edited_725_);
lean_closure_set(v___f_748_, 3, v_inst_722_);
lean_closure_set(v___f_748_, 4, v_a_726_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_snd_735_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_743_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_snd_735_);
v___x_750_ = v_reuseFailAlloc_772_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_771_; 
v___x_751_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_723_, v___f_748_, v___x_750_);
v_fst_752_ = lean_ctor_get(v___x_751_, 0);
v_snd_753_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_771_ == 0)
{
v___x_755_ = v___x_751_;
v_isShared_756_ = v_isSharedCheck_771_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snd_753_);
lean_inc(v_fst_752_);
lean_dec(v___x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_771_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = 2;
v___x_758_ = lean_box(v___x_757_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_a_726_);
lean_ctor_set(v___x_755_, 0, v___x_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_726_);
v___x_760_ = v_reuseFailAlloc_770_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_761_ = lean_array_push(v_fst_752_, v___x_760_);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_snd_744_, v___x_762_);
lean_dec(v_snd_744_);
v___x_764_ = lean_nat_add(v_snd_753_, v___x_762_);
lean_dec(v_snd_753_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_764_);
lean_ctor_set(v___x_732_, 0, v___x_763_);
v___x_766_ = v___x_732_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_769_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_761_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5(lean_object* v___x_777_, lean_object* v_original_778_, lean_object* v_b_779_){
_start:
{
lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_801_; 
v_fst_780_ = lean_ctor_get(v_b_779_, 0);
v_snd_781_ = lean_ctor_get(v_b_779_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_779_);
if (v_isSharedCheck_801_ == 0)
{
v___x_783_ = v_b_779_;
v_isShared_784_ = v_isSharedCheck_801_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_b_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_801_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_lt(v_snd_781_, v___x_777_);
if (v___x_785_ == 0)
{
lean_object* v___x_787_; 
if (v_isShared_784_ == 0)
{
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_snd_781_);
v___x_787_ = v_reuseFailAlloc_789_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
else
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_790_ = 1;
v___x_791_ = lean_array_fget_borrowed(v_original_778_, v_snd_781_);
v___x_792_ = lean_box(v___x_790_);
lean_inc(v___x_791_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_791_);
lean_ctor_set(v___x_783_, 0, v___x_792_);
v___x_794_ = v___x_783_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_791_);
v___x_794_ = v_reuseFailAlloc_800_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_795_ = lean_array_push(v_fst_780_, v___x_794_);
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_snd_781_, v___x_796_);
lean_dec(v_snd_781_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5___boxed(lean_object* v___x_802_, lean_object* v_original_803_, lean_object* v_b_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Diff_diff___redArg___lam__5(v___x_802_, v_original_803_, v_b_804_);
lean_dec_ref(v_original_803_);
lean_dec(v___x_802_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6(lean_object* v___x_806_, lean_object* v_edited_807_, lean_object* v_b_808_){
_start:
{
lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_830_; 
v_fst_809_ = lean_ctor_get(v_b_808_, 0);
v_snd_810_ = lean_ctor_get(v_b_808_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_b_808_);
if (v_isSharedCheck_830_ == 0)
{
v___x_812_ = v_b_808_;
v_isShared_813_ = v_isSharedCheck_830_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_snd_810_);
lean_inc(v_fst_809_);
lean_dec(v_b_808_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_830_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_lt(v_snd_810_, v___x_806_);
if (v___x_814_ == 0)
{
lean_object* v___x_816_; 
if (v_isShared_813_ == 0)
{
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fst_809_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_snd_810_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
else
{
uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_819_ = 0;
v___x_820_ = lean_array_fget_borrowed(v_edited_807_, v_snd_810_);
v___x_821_ = lean_box(v___x_819_);
lean_inc(v___x_820_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_820_);
lean_ctor_set(v___x_812_, 0, v___x_821_);
v___x_823_ = v___x_812_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_820_);
v___x_823_ = v_reuseFailAlloc_829_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_824_ = lean_array_push(v_fst_809_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_snd_810_, v___x_825_);
lean_dec(v_snd_810_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6___boxed(lean_object* v___x_831_, lean_object* v_edited_832_, lean_object* v_b_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Diff_diff___redArg___lam__6(v___x_831_, v_edited_832_, v_b_833_);
lean_dec_ref(v_edited_832_);
lean_dec(v___x_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg(lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_original_847_, lean_object* v_edited_848_){
_start:
{
lean_object* v___x_849_; lean_object* v_i_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_849_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_i_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_array_get_size(v_original_847_);
v___x_852_ = lean_nat_dec_lt(v_i_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___f_853_; size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; 
lean_dec_ref(v_original_847_);
lean_dec(v_inst_846_);
lean_dec_ref(v_inst_845_);
lean_dec_ref(v_inst_844_);
v___f_853_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__0));
v_sz_854_ = lean_array_size(v_edited_848_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_849_, v___f_853_, v_sz_854_, v___x_855_, v_edited_848_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_edited_848_);
v___x_858_ = lean_nat_dec_lt(v_i_850_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___f_859_; size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v_edited_848_);
lean_dec(v_inst_846_);
lean_dec_ref(v_inst_845_);
lean_dec_ref(v_inst_844_);
v___f_859_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__1));
v_sz_860_ = lean_array_size(v_original_847_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_849_, v___f_859_, v_sz_860_, v___x_861_, v_original_847_);
return v___x_862_;
}
else
{
lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_ds_866_; lean_object* v___x_867_; size_t v_sz_868_; size_t v___x_869_; lean_object* v___x_870_; lean_object* v_snd_871_; lean_object* v_fst_872_; lean_object* v_fst_873_; lean_object* v_snd_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_895_; 
lean_inc_ref_n(v_edited_848_, 2);
lean_inc_ref(v_inst_844_);
lean_inc_ref_n(v_original_847_, 2);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__4), 10, 7);
lean_closure_set(v___f_863_, 0, v___x_851_);
lean_closure_set(v___f_863_, 1, v_inst_846_);
lean_closure_set(v___f_863_, 2, v_original_847_);
lean_closure_set(v___f_863_, 3, v_inst_844_);
lean_closure_set(v___f_863_, 4, v___x_849_);
lean_closure_set(v___f_863_, 5, v___x_857_);
lean_closure_set(v___f_863_, 6, v_edited_848_);
v___x_864_ = l_Array_toSubarray___redArg(v_original_847_, v_i_850_, v___x_851_);
v___x_865_ = l_Array_toSubarray___redArg(v_edited_848_, v_i_850_, v___x_857_);
v_ds_866_ = l_Lean_Diff_lcs___redArg(v_inst_844_, v_inst_845_, v___x_864_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__4));
v_sz_868_ = lean_array_size(v_ds_866_);
v___x_869_ = ((size_t)0ULL);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_849_, v_ds_866_, v___f_863_, v_sz_868_, v___x_869_, v___x_867_);
v_snd_871_ = lean_ctor_get(v___x_870_, 1);
lean_inc(v_snd_871_);
v_fst_872_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_fst_872_);
lean_dec(v___x_870_);
v_fst_873_ = lean_ctor_get(v_snd_871_, 0);
v_snd_874_ = lean_ctor_get(v_snd_871_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_snd_871_);
if (v_isSharedCheck_895_ == 0)
{
v___x_876_ = v_snd_871_;
v_isShared_877_ = v_isSharedCheck_895_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_snd_874_);
lean_inc(v_fst_873_);
lean_dec(v_snd_871_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_895_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___f_878_; lean_object* v___x_880_; 
v___f_878_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_878_, 0, v___x_851_);
lean_closure_set(v___f_878_, 1, v_original_847_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_fst_873_);
lean_ctor_set(v___x_876_, 0, v_fst_872_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fst_872_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_fst_873_);
v___x_880_ = v_reuseFailAlloc_894_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v_fst_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_892_; 
v___x_881_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_849_, v___f_878_, v___x_880_);
v_fst_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_881_, 1);
lean_dec(v_unused_893_);
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_fst_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___f_886_; lean_object* v___x_888_; 
v___f_886_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_886_, 0, v___x_857_);
lean_closure_set(v___f_886_, 1, v_edited_848_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v_snd_874_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_882_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_874_);
v___x_888_ = v_reuseFailAlloc_891_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v_fst_890_; 
v___x_889_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_849_, v___f_886_, v___x_888_);
v_fst_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_fst_890_);
lean_dec(v___x_889_);
return v_fst_890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object* v_00_u03b1_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_original_900_, lean_object* v_edited_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Diff_diff___redArg(v_inst_897_, v_inst_898_, v_inst_899_, v_original_900_, v_edited_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object* v_inst_904_, lean_object* v_out_905_, lean_object* v_a_906_, lean_object* v_x_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_fst_909_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_fst_909_);
v_snd_910_ = lean_ctor_get(v_a_906_, 1);
lean_inc(v_snd_910_);
lean_dec_ref(v_a_906_);
v___x_911_ = lean_apply_1(v_inst_904_, v_snd_910_);
v___x_912_ = lean_string_dec_eq(v___x_911_, v_out_905_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_913_ = lean_unbox(v_fst_909_);
lean_dec(v_fst_909_);
v___x_914_ = l_Lean_Diff_Action_linePrefix(v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
v___x_917_ = lean_string_append(v___x_916_, v___x_911_);
lean_dec_ref(v___x_911_);
v___x_918_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
v___x_920_ = lean_string_append(v___y_908_, v___x_919_);
lean_dec_ref(v___x_919_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
else
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v___x_911_);
v___x_922_ = lean_unbox(v_fst_909_);
lean_dec(v_fst_909_);
v___x_923_ = l_Lean_Diff_Action_linePrefix(v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
v___x_926_ = lean_string_append(v___y_908_, v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object* v_inst_928_, lean_object* v_out_929_, lean_object* v_a_930_, lean_object* v_x_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Diff_linesToString___redArg___lam__0(v_inst_928_, v_out_929_, v_a_930_, v_x_931_, v___y_932_);
lean_dec_ref(v_out_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object* v_inst_935_, lean_object* v_lines_936_){
_start:
{
lean_object* v___x_937_; lean_object* v_out_938_; lean_object* v___f_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v___x_937_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_out_938_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___closed__0));
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Diff_linesToString___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_939_, 0, v_inst_935_);
lean_closure_set(v___f_939_, 1, v_out_938_);
v_sz_940_ = lean_array_size(v_lines_936_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_937_, v_lines_936_, v___f_939_, v_sz_940_, v___x_941_, v_out_938_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object* v_00_u03b1_943_, lean_object* v_inst_944_, lean_object* v_lines_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Diff_linesToString___redArg(v_inst_944_, v_lines_945_);
return v___x_946_;
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
