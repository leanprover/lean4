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
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
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
uint8_t v_x_171__boxed_112_; lean_object* v_res_113_; 
v_x_171__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Lean_Diff_instReprAction_repr(v_x_171__boxed_112_, v_prec_111_);
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
uint8_t v_x_21__boxed_123_; uint8_t v_y_22__boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_x_21__boxed_123_ = lean_unbox(v_x_121_);
v_y_22__boxed_124_ = lean_unbox(v_y_122_);
v_res_125_ = l_Lean_Diff_instBEqAction_beq(v_x_21__boxed_123_, v_y_22__boxed_124_);
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
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
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
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_163_, v_inst_164_, v_histogram_165_, v_val_167_, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_196_; 
v_val_175_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_196_ == 0)
{
v___x_177_ = v___x_168_;
v_isShared_178_ = v_isSharedCheck_196_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_val_175_);
lean_dec(v___x_168_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_196_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_leftCount_179_; lean_object* v_rightCount_180_; lean_object* v_rightIndex_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_194_; 
v_leftCount_179_ = lean_ctor_get(v_val_175_, 0);
v_rightCount_180_ = lean_ctor_get(v_val_175_, 2);
v_rightIndex_181_ = lean_ctor_get(v_val_175_, 3);
v_isSharedCheck_194_ = !lean_is_exclusive(v_val_175_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_val_175_, 1);
lean_dec(v_unused_195_);
v___x_183_ = v_val_175_;
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_rightIndex_181_);
lean_inc(v_rightCount_180_);
lean_inc(v_leftCount_179_);
lean_dec(v_val_175_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_leftCount_179_, v___x_185_);
lean_dec(v_leftCount_179_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_index_166_);
v___x_188_ = v___x_177_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_index_166_);
v___x_188_ = v_reuseFailAlloc_193_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_188_);
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_rightCount_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_rightIndex_181_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_163_, v_inst_164_, v_histogram_165_, v_val_167_, v___x_190_);
return v___x_191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft(lean_object* v_00_u03b1_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_lsize_200_, lean_object* v_rsize_201_, lean_object* v_histogram_202_, lean_object* v_index_203_, lean_object* v_val_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_198_, v_inst_199_, v_histogram_202_, v_index_203_, v_val_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___boxed(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_lsize_209_, lean_object* v_rsize_210_, lean_object* v_histogram_211_, lean_object* v_index_212_, lean_object* v_val_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Diff_Histogram_addLeft(v_00_u03b1_206_, v_inst_207_, v_inst_208_, v_lsize_209_, v_rsize_210_, v_histogram_211_, v_index_212_, v_val_213_);
lean_dec(v_rsize_210_);
lean_dec(v_lsize_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___redArg(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_histogram_217_, lean_object* v_index_218_, lean_object* v_val_219_){
_start:
{
lean_object* v___x_220_; 
lean_inc(v_val_219_);
lean_inc_ref(v_inst_216_);
lean_inc_ref(v_inst_215_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_215_, v_inst_216_, v_histogram_217_, v_val_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_box(0);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_index_218_);
v___x_225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_225_, 0, v___x_221_);
lean_ctor_set(v___x_225_, 1, v___x_222_);
lean_ctor_set(v___x_225_, 2, v___x_223_);
lean_ctor_set(v___x_225_, 3, v___x_224_);
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_215_, v_inst_216_, v_histogram_217_, v_val_219_, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_248_; 
v_val_227_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_248_ == 0)
{
v___x_229_ = v___x_220_;
v_isShared_230_ = v_isSharedCheck_248_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_val_227_);
lean_dec(v___x_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_248_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_leftCount_231_; lean_object* v_leftIndex_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_245_; 
v_leftCount_231_ = lean_ctor_get(v_val_227_, 0);
v_leftIndex_232_ = lean_ctor_get(v_val_227_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_val_227_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; 
v_unused_246_ = lean_ctor_get(v_val_227_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_val_227_, 2);
lean_dec(v_unused_247_);
v___x_234_ = v_val_227_;
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_leftIndex_232_);
lean_inc(v_leftCount_231_);
lean_dec(v_val_227_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_leftCount_231_, v___x_236_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v_index_218_);
v___x_239_ = v___x_229_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_index_218_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 3, v___x_239_);
lean_ctor_set(v___x_234_, 2, v___x_237_);
v___x_241_ = v___x_234_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_leftCount_231_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_leftIndex_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v___x_239_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_215_, v_inst_216_, v_histogram_217_, v_val_219_, v___x_241_);
return v___x_242_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_lsize_252_, lean_object* v_rsize_253_, lean_object* v_histogram_254_, lean_object* v_index_255_, lean_object* v_val_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_250_, v_inst_251_, v_histogram_254_, v_index_255_, v_val_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___boxed(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_lsize_261_, lean_object* v_rsize_262_, lean_object* v_histogram_263_, lean_object* v_index_264_, lean_object* v_val_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Diff_Histogram_addRight(v_00_u03b1_258_, v_inst_259_, v_inst_260_, v_lsize_261_, v_rsize_262_, v_histogram_263_, v_index_264_, v_val_265_);
lean_dec(v_rsize_262_);
lean_dec(v_lsize_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(lean_object* v_inst_267_, lean_object* v_left_268_, lean_object* v_right_269_, lean_object* v_pref_270_){
_start:
{
lean_object* v_start_271_; lean_object* v_stop_272_; lean_object* v_start_273_; lean_object* v_stop_274_; lean_object* v_i_275_; uint8_t v___y_277_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_start_271_ = lean_ctor_get(v_left_268_, 1);
v_stop_272_ = lean_ctor_get(v_left_268_, 2);
v_start_273_ = lean_ctor_get(v_right_269_, 1);
v_stop_274_ = lean_ctor_get(v_right_269_, 2);
v_i_275_ = lean_array_get_size(v_pref_270_);
v___x_292_ = lean_nat_sub(v_stop_272_, v_start_271_);
v___x_293_ = lean_nat_dec_lt(v_i_275_, v___x_292_);
lean_dec(v___x_292_);
if (v___x_293_ == 0)
{
v___y_277_ = v___x_293_;
goto v___jp_276_;
}
else
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_nat_sub(v_stop_274_, v_start_273_);
v___x_295_ = lean_nat_dec_lt(v_i_275_, v___x_294_);
lean_dec(v___x_294_);
v___y_277_ = v___x_295_;
goto v___jp_276_;
}
v___jp_276_:
{
if (v___y_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v_inst_267_);
v___x_278_ = l_Subarray_drop___redArg(v_left_268_, v_i_275_);
v___x_279_ = l_Subarray_drop___redArg(v_right_269_, v_i_275_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_pref_270_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_282_ = l_Subarray_get___redArg(v_left_268_, v_i_275_);
v___x_283_ = l_Subarray_get___redArg(v_right_269_, v_i_275_);
lean_inc_ref(v_inst_267_);
lean_inc(v___x_282_);
v___x_284_ = lean_apply_2(v_inst_267_, v___x_282_, v___x_283_);
v___x_285_ = lean_unbox(v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v___x_282_);
lean_dec_ref(v_inst_267_);
v___x_286_ = l_Subarray_drop___redArg(v_left_268_, v_i_275_);
v___x_287_ = l_Subarray_drop___redArg(v_right_269_, v_i_275_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_pref_270_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_array_push(v_pref_270_, v___x_282_);
v_pref_270_ = v___x_290_;
goto _start;
}
}
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
lean_object* v_start_338_; lean_object* v_stop_339_; lean_object* v_start_340_; lean_object* v_stop_341_; lean_object* v___f_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; uint8_t v___y_347_; 
v_start_338_ = lean_ctor_get(v_left_335_, 1);
v_stop_339_ = lean_ctor_get(v_left_335_, 2);
v_start_340_ = lean_ctor_get(v_right_336_, 1);
v_stop_341_ = lean_ctor_get(v_right_336_, 2);
v___f_342_ = ((lean_object*)(l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0));
v___x_343_ = lean_nat_sub(v_stop_339_, v_start_338_);
v___x_344_ = lean_nat_dec_lt(v_i_337_, v___x_343_);
v___x_345_ = lean_nat_sub(v_stop_341_, v_start_340_);
if (v___x_344_ == 0)
{
v___y_347_ = v___x_344_;
goto v___jp_346_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_lt(v_i_337_, v___x_345_);
v___y_347_ = v___x_375_;
goto v___jp_346_;
}
v___jp_346_:
{
if (v___y_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec_ref(v_inst_334_);
v___x_348_ = lean_nat_sub(v___x_343_, v_i_337_);
lean_dec(v___x_343_);
lean_inc_ref(v_left_335_);
v___x_349_ = l_Subarray_take___redArg(v_left_335_, v___x_348_);
v___x_350_ = lean_nat_sub(v___x_345_, v_i_337_);
lean_dec(v_i_337_);
lean_dec(v___x_345_);
v___x_351_ = l_Subarray_take___redArg(v_right_336_, v___x_350_);
lean_dec(v___x_350_);
v___x_352_ = l_Subarray_drop___redArg(v_left_335_, v___x_348_);
lean_dec(v___x_348_);
v___x_353_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_354_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_342_, v___x_352_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_351_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_349_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_357_ = lean_nat_sub(v___x_343_, v_i_337_);
lean_dec(v___x_343_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_sub(v___x_357_, v___x_358_);
v___x_360_ = l_Subarray_get___redArg(v_left_335_, v___x_359_);
lean_dec(v___x_359_);
v___x_361_ = lean_nat_sub(v___x_345_, v_i_337_);
lean_dec(v___x_345_);
v___x_362_ = lean_nat_sub(v___x_361_, v___x_358_);
v___x_363_ = l_Subarray_get___redArg(v_right_336_, v___x_362_);
lean_dec(v___x_362_);
lean_inc_ref(v_inst_334_);
v___x_364_ = lean_apply_2(v_inst_334_, v___x_360_, v___x_363_);
v___x_365_ = lean_unbox(v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_i_337_);
lean_dec_ref(v_inst_334_);
lean_inc_ref(v_left_335_);
v___x_366_ = l_Subarray_take___redArg(v_left_335_, v___x_357_);
v___x_367_ = l_Subarray_take___redArg(v_right_336_, v___x_361_);
lean_dec(v___x_361_);
v___x_368_ = l_Subarray_drop___redArg(v_left_335_, v___x_357_);
lean_dec(v___x_357_);
v___x_369_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_370_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_342_, v___x_368_, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_367_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_366_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; 
lean_dec(v___x_361_);
lean_dec(v___x_357_);
v___x_373_ = lean_nat_add(v_i_337_, v___x_358_);
lean_dec(v_i_337_);
v_i_337_ = v___x_373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object* v_00_u03b1_376_, lean_object* v_inst_377_, lean_object* v_left_378_, lean_object* v_right_379_, lean_object* v_i_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_377_, v_left_378_, v_right_379_, v_i_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object* v_inst_382_, lean_object* v_left_383_, lean_object* v_right_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_382_, v_left_383_, v_right_384_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object* v_00_u03b1_387_, lean_object* v_inst_388_, lean_object* v_left_389_, lean_object* v_right_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Diff_matchSuffix___redArg(v_inst_388_, v_left_389_, v_right_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object* v___x_392_, lean_object* v_fst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_next_396_, lean_object* v_acc_397_, lean_object* v_h_398_, lean_object* v_G_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_lt(v_next_396_, v___x_392_);
if (v___x_400_ == 0)
{
lean_dec_ref(v_G_399_);
lean_dec(v_next_396_);
lean_dec_ref(v_inst_395_);
lean_dec_ref(v_inst_394_);
return v_acc_397_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_401_ = l_Subarray_get___redArg(v_fst_393_, v_next_396_);
lean_inc(v_next_396_);
v___x_402_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_394_, v_inst_395_, v_acc_397_, v_next_396_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_next_396_, v___x_403_);
lean_dec(v_next_396_);
v___x_405_ = lean_apply_4(v_G_399_, v___x_404_, v___x_402_, lean_box(0), lean_box(0));
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0___boxed(lean_object* v___x_406_, lean_object* v_fst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_next_410_, lean_object* v_acc_411_, lean_object* v_h_412_, lean_object* v_G_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Diff_lcs___redArg___lam__0(v___x_406_, v_fst_407_, v_inst_408_, v_inst_409_, v_next_410_, v_acc_411_, v_h_412_, v_G_413_);
lean_dec_ref(v_fst_407_);
lean_dec(v___x_406_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object* v___x_415_, lean_object* v_fst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_next_419_, lean_object* v_acc_420_, lean_object* v_h_421_, lean_object* v_G_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = lean_nat_dec_lt(v_next_419_, v___x_415_);
if (v___x_423_ == 0)
{
lean_dec_ref(v_G_422_);
lean_dec(v_next_419_);
lean_dec_ref(v_inst_418_);
lean_dec_ref(v_inst_417_);
return v_acc_420_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_424_ = l_Subarray_get___redArg(v_fst_416_, v_next_419_);
lean_inc(v_next_419_);
v___x_425_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_417_, v_inst_418_, v_acc_420_, v_next_419_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_next_419_, v___x_426_);
lean_dec(v_next_419_);
v___x_428_ = lean_apply_4(v_G_422_, v___x_427_, v___x_425_, lean_box(0), lean_box(0));
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1___boxed(lean_object* v___x_429_, lean_object* v_fst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_next_433_, lean_object* v_acc_434_, lean_object* v_h_435_, lean_object* v_G_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Diff_lcs___redArg___lam__1(v___x_429_, v_fst_430_, v_inst_431_, v_inst_432_, v_next_433_, v_acc_434_, v_h_435_, v_G_436_);
lean_dec_ref(v_fst_430_);
lean_dec(v___x_429_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object* v_a_438_, lean_object* v_x_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_snd_441_; lean_object* v_leftIndex_442_; 
v_snd_441_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_441_);
v_leftIndex_442_ = lean_ctor_get(v_snd_441_, 1);
lean_inc(v_leftIndex_442_);
if (lean_obj_tag(v_leftIndex_442_) == 1)
{
lean_object* v_rightIndex_443_; 
v_rightIndex_443_ = lean_ctor_get(v_snd_441_, 3);
lean_inc(v_rightIndex_443_);
if (lean_obj_tag(v_rightIndex_443_) == 1)
{
if (lean_obj_tag(v___y_440_) == 0)
{
lean_object* v_fst_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_472_; 
v_fst_444_ = lean_ctor_get(v_a_438_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_a_438_, 1);
lean_dec(v_unused_473_);
v___x_446_ = v_a_438_;
v_isShared_447_ = v_isSharedCheck_472_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_fst_444_);
lean_dec(v_a_438_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_472_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_leftCount_448_; lean_object* v_rightCount_449_; lean_object* v_val_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_471_; 
v_leftCount_448_ = lean_ctor_get(v_snd_441_, 0);
lean_inc(v_leftCount_448_);
v_rightCount_449_ = lean_ctor_get(v_snd_441_, 2);
lean_inc(v_rightCount_449_);
lean_dec(v_snd_441_);
v_val_450_ = lean_ctor_get(v_leftIndex_442_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_leftIndex_442_);
if (v_isSharedCheck_471_ == 0)
{
v___x_452_ = v_leftIndex_442_;
v_isShared_453_ = v_isSharedCheck_471_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_val_450_);
lean_dec(v_leftIndex_442_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_471_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_470_; 
v_val_454_ = lean_ctor_get(v_rightIndex_443_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_rightIndex_443_);
if (v_isSharedCheck_470_ == 0)
{
v___x_456_ = v_rightIndex_443_;
v_isShared_457_ = v_isSharedCheck_470_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v_rightIndex_443_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_470_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_nat_add(v_leftCount_448_, v_rightCount_449_);
lean_dec(v_rightCount_449_);
lean_dec(v_leftCount_448_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_val_454_);
lean_ctor_set(v___x_446_, 0, v_val_450_);
v___x_460_ = v___x_446_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_val_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_val_454_);
v___x_460_ = v_reuseFailAlloc_469_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_fst_444_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_458_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_462_);
v___x_464_ = v___x_456_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_464_);
v___x_466_ = v___x_452_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_474_; lean_object* v_fst_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_516_; 
v_val_474_ = lean_ctor_get(v___y_440_, 0);
lean_inc(v_val_474_);
v_fst_475_ = lean_ctor_get(v_a_438_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_a_438_, 1);
lean_dec(v_unused_517_);
v___x_477_ = v_a_438_;
v_isShared_478_ = v_isSharedCheck_516_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_fst_475_);
lean_dec(v_a_438_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_516_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_leftCount_479_; lean_object* v_rightCount_480_; lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_515_; 
v_leftCount_479_ = lean_ctor_get(v_snd_441_, 0);
lean_inc(v_leftCount_479_);
v_rightCount_480_ = lean_ctor_get(v_snd_441_, 2);
lean_inc(v_rightCount_480_);
lean_dec(v_snd_441_);
v_val_481_ = lean_ctor_get(v_leftIndex_442_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_leftIndex_442_);
if (v_isSharedCheck_515_ == 0)
{
v___x_483_ = v_leftIndex_442_;
v_isShared_484_ = v_isSharedCheck_515_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_leftIndex_442_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_515_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_val_485_; lean_object* v_fst_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_513_; 
v_val_485_ = lean_ctor_get(v_rightIndex_443_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v_rightIndex_443_, 1);
v_fst_486_ = lean_ctor_get(v_val_474_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_val_474_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v_val_474_, 1);
lean_dec(v_unused_514_);
v___x_488_ = v_val_474_;
v_isShared_489_ = v_isSharedCheck_513_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_fst_486_);
lean_dec(v_val_474_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_513_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_nat_add(v_leftCount_479_, v_rightCount_480_);
lean_dec(v_rightCount_480_);
lean_dec(v_leftCount_479_);
v___x_491_ = lean_nat_dec_lt(v___x_490_, v_fst_486_);
lean_dec(v_fst_486_);
if (v___x_491_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v___x_490_);
lean_del_object(v___x_488_);
lean_dec(v_val_485_);
lean_dec(v_val_481_);
lean_del_object(v___x_477_);
lean_dec(v_fst_475_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___y_440_);
v___x_493_ = v___x_483_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___y_440_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_511_; 
v_isSharedCheck_511_ = !lean_is_exclusive(v___y_440_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v___y_440_, 0);
lean_dec(v_unused_512_);
v___x_496_ = v___y_440_;
v_isShared_497_ = v_isSharedCheck_511_;
goto v_resetjp_495_;
}
else
{
lean_dec(v___y_440_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_511_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v_val_485_);
lean_ctor_set(v___x_488_, 0, v_val_481_);
v___x_499_ = v___x_488_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_val_481_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_val_485_);
v___x_499_ = v_reuseFailAlloc_510_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_499_);
v___x_501_ = v___x_477_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_fst_475_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_499_);
v___x_501_ = v_reuseFailAlloc_509_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_490_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_502_);
v___x_504_ = v___x_496_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_504_);
v___x_506_ = v___x_483_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
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
lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_rightIndex_443_);
lean_dec(v_snd_441_);
lean_dec_ref(v_a_438_);
v_isSharedCheck_524_ = !lean_is_exclusive(v_leftIndex_442_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_leftIndex_442_, 0);
lean_dec(v_unused_525_);
v___x_519_ = v_leftIndex_442_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_dec(v_leftIndex_442_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___y_440_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___y_440_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_526_; 
lean_dec(v_leftIndex_442_);
lean_dec(v_snd_441_);
lean_dec_ref(v_a_438_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___y_440_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object* v_a_527_, lean_object* v_b_528_, lean_object* v_d_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_527_);
lean_ctor_set(v___x_530_, 1, v_b_528_);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_d_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__4(lean_object* v___x_532_, lean_object* v___f_533_, lean_object* v_l_534_, lean_object* v_acc_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_532_, v___f_533_, v_acc_535_, v_l_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__10(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_unsigned_to_nat(16u);
v___x_558_ = lean_mk_array(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__11(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_hist_561_; 
v___x_559_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__10, &l_Lean_Diff_lcs___redArg___closed__10_once, _init_l_Lean_Diff_lcs___redArg___closed__10);
v___x_560_ = lean_unsigned_to_nat(0u);
v_hist_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_561_, 0, v___x_560_);
lean_ctor_set(v_hist_561_, 1, v___x_559_);
return v_hist_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_left_569_, lean_object* v_right_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_snd_573_; lean_object* v_fst_574_; lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_577_; lean_object* v_snd_578_; lean_object* v_fst_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v_start_582_; lean_object* v_stop_583_; lean_object* v_start_584_; lean_object* v_stop_585_; lean_object* v___x_586_; lean_object* v_hist_587_; lean_object* v___x_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v_buckets_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___y_598_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_571_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
lean_inc_ref_n(v_inst_567_, 4);
v___x_572_ = l_Lean_Diff_matchPrefix___redArg(v_inst_567_, v_left_569_, v_right_570_);
v_snd_573_ = lean_ctor_get(v___x_572_, 1);
lean_inc(v_snd_573_);
v_fst_574_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_fst_574_);
lean_dec_ref(v___x_572_);
v_fst_575_ = lean_ctor_get(v_snd_573_, 0);
lean_inc(v_fst_575_);
v_snd_576_ = lean_ctor_get(v_snd_573_, 1);
lean_inc(v_snd_576_);
lean_dec(v_snd_573_);
v___x_577_ = l_Lean_Diff_matchSuffix___redArg(v_inst_567_, v_fst_575_, v_snd_576_);
v_snd_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_snd_578_);
v_fst_579_ = lean_ctor_get(v___x_577_, 0);
lean_inc_n(v_fst_579_, 2);
lean_dec_ref(v___x_577_);
v_fst_580_ = lean_ctor_get(v_snd_578_, 0);
lean_inc_n(v_fst_580_, 2);
v_snd_581_ = lean_ctor_get(v_snd_578_, 1);
lean_inc(v_snd_581_);
lean_dec(v_snd_578_);
v_start_582_ = lean_ctor_get(v_fst_579_, 1);
v_stop_583_ = lean_ctor_get(v_fst_579_, 2);
v_start_584_ = lean_ctor_get(v_fst_580_, 1);
v_stop_585_ = lean_ctor_get(v_fst_580_, 2);
v___x_586_ = lean_unsigned_to_nat(0u);
v_hist_587_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__11, &l_Lean_Diff_lcs___redArg___closed__11_once, _init_l_Lean_Diff_lcs___redArg___closed__11);
v___x_588_ = lean_nat_sub(v_stop_583_, v_start_582_);
lean_inc_ref_n(v_inst_568_, 2);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_589_, 0, v___x_588_);
lean_closure_set(v___f_589_, 1, v_fst_579_);
lean_closure_set(v___f_589_, 2, v_inst_567_);
lean_closure_set(v___f_589_, 3, v_inst_568_);
v___x_590_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_589_, v___x_586_, v_hist_587_, lean_box(0));
v___x_591_ = lean_nat_sub(v_stop_585_, v_start_584_);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_592_, 0, v___x_591_);
lean_closure_set(v___f_592_, 1, v_fst_580_);
lean_closure_set(v___f_592_, 2, v_inst_567_);
lean_closure_set(v___f_592_, 3, v_inst_568_);
v___x_593_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_592_, v___x_586_, v___x_590_, lean_box(0));
v_buckets_594_ = lean_ctor_get(v___x_593_, 1);
lean_inc_ref(v_buckets_594_);
lean_dec(v___x_593_);
v___f_595_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__12));
v___x_596_ = lean_box(0);
v___x_624_ = lean_box(0);
v___x_625_ = lean_array_get_size(v_buckets_594_);
v___x_626_ = lean_nat_dec_lt(v___x_586_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec_ref(v_buckets_594_);
v___y_598_ = v___x_624_;
goto v___jp_597_;
}
else
{
lean_object* v___f_627_; size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___f_627_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__14));
v___x_628_ = lean_usize_of_nat(v___x_625_);
v___x_629_ = ((size_t)0ULL);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_571_, v___f_627_, v_buckets_594_, v___x_628_, v___x_629_, v___x_624_);
v___y_598_ = v___x_630_;
goto v___jp_597_;
}
v___jp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = l_List_forIn_x27_loop___redArg(v___x_571_, v___f_595_, v___y_598_, v___x_596_);
lean_dec(v___y_598_);
if (lean_obj_tag(v___x_599_) == 1)
{
lean_object* v_val_600_; lean_object* v_snd_601_; lean_object* v_snd_602_; lean_object* v_fst_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_val_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v___x_599_, 1);
v_snd_601_ = lean_ctor_get(v_val_600_, 1);
lean_inc(v_snd_601_);
lean_dec(v_val_600_);
v_snd_602_ = lean_ctor_get(v_snd_601_, 1);
lean_inc(v_snd_602_);
v_fst_603_ = lean_ctor_get(v_snd_601_, 0);
lean_inc(v_fst_603_);
lean_dec(v_snd_601_);
v_fst_604_ = lean_ctor_get(v_snd_602_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v_snd_602_, 1);
lean_inc(v_snd_605_);
lean_dec(v_snd_602_);
v___x_606_ = l_Subarray_split___redArg(v_fst_579_, v_fst_604_);
lean_dec(v_fst_604_);
v_fst_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_fst_607_);
v_snd_608_ = lean_ctor_get(v___x_606_, 1);
lean_inc(v_snd_608_);
lean_dec_ref(v___x_606_);
v___x_609_ = l_Subarray_split___redArg(v_fst_580_, v_snd_605_);
lean_dec(v_snd_605_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_fst_610_);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_snd_611_);
lean_dec_ref(v___x_609_);
lean_inc_ref(v_inst_568_);
lean_inc_ref(v_inst_567_);
v___x_612_ = l_Lean_Diff_lcs___redArg(v_inst_567_, v_inst_568_, v_fst_607_, v_fst_610_);
v___x_613_ = l_Array_append___redArg(v_fst_574_, v___x_612_);
lean_dec_ref(v___x_612_);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_array_push(v___x_615_, v_fst_603_);
v___x_617_ = l_Array_append___redArg(v___x_613_, v___x_616_);
lean_dec_ref(v___x_616_);
v___x_618_ = l_Subarray_drop___redArg(v_snd_608_, v___x_614_);
v___x_619_ = l_Subarray_drop___redArg(v_snd_611_, v___x_614_);
v___x_620_ = l_Lean_Diff_lcs___redArg(v_inst_567_, v_inst_568_, v___x_618_, v___x_619_);
v___x_621_ = l_Array_append___redArg(v___x_617_, v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = l_Array_append___redArg(v___x_621_, v_snd_581_);
lean_dec(v_snd_581_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; 
lean_dec(v___x_599_);
lean_dec(v_fst_580_);
lean_dec(v_fst_579_);
lean_dec_ref(v_inst_568_);
lean_dec_ref(v_inst_567_);
v___x_623_ = l_Array_append___redArg(v_fst_574_, v_snd_581_);
lean_dec(v_snd_581_);
return v___x_623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object* v_00_u03b1_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_left_634_, lean_object* v_right_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Diff_lcs___redArg(v_inst_632_, v_inst_633_, v_left_634_, v_right_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object* v_x_637_){
_start:
{
uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = 0;
v___x_639_ = lean_box(v___x_638_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_x_637_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object* v_x_641_){
_start:
{
uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = 1;
v___x_643_ = lean_box(v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_x_641_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object* v___x_645_, lean_object* v_inst_646_, lean_object* v_original_647_, lean_object* v_inst_648_, lean_object* v_a_649_, lean_object* v_b_650_){
_start:
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_673_; 
v_fst_651_ = lean_ctor_get(v_b_650_, 0);
v_snd_652_ = lean_ctor_get(v_b_650_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_b_650_);
if (v_isSharedCheck_673_ == 0)
{
v___x_654_ = v_b_650_;
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
lean_dec(v_b_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v___x_661_; 
v___x_661_ = lean_nat_dec_lt(v_snd_652_, v___x_645_);
if (v___x_661_ == 0)
{
lean_dec(v_a_649_);
lean_dec_ref(v_inst_648_);
goto v___jp_656_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_array_get_borrowed(v_inst_646_, v_original_647_, v_snd_652_);
lean_inc(v___x_662_);
v___x_663_ = lean_apply_2(v_inst_648_, v___x_662_, v_a_649_);
v___x_664_ = lean_unbox(v___x_663_);
if (v___x_664_ == 0)
{
uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_del_object(v___x_654_);
v___x_665_ = 1;
v___x_666_ = lean_box(v___x_665_);
lean_inc(v___x_662_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_662_);
v___x_668_ = lean_array_push(v_fst_651_, v___x_667_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_snd_652_, v___x_669_);
lean_dec(v_snd_652_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_668_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
else
{
goto v___jp_656_;
}
}
v___jp_656_:
{
lean_object* v___x_658_; 
if (v_isShared_655_ == 0)
{
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_fst_651_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_snd_652_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object* v___x_674_, lean_object* v_inst_675_, lean_object* v_original_676_, lean_object* v_inst_677_, lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Diff_diff___redArg___lam__2(v___x_674_, v_inst_675_, v_original_676_, v_inst_677_, v_a_678_, v_b_679_);
lean_dec_ref(v_original_676_);
lean_dec(v_inst_675_);
lean_dec(v___x_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object* v___x_681_, lean_object* v_inst_682_, lean_object* v_edited_683_, lean_object* v_inst_684_, lean_object* v_a_685_, lean_object* v_b_686_){
_start:
{
lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_709_; 
v_fst_687_ = lean_ctor_get(v_b_686_, 0);
v_snd_688_ = lean_ctor_get(v_b_686_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_b_686_);
if (v_isSharedCheck_709_ == 0)
{
v___x_690_ = v_b_686_;
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
lean_dec(v_b_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_lt(v_snd_688_, v___x_681_);
if (v___x_697_ == 0)
{
lean_dec(v_a_685_);
lean_dec_ref(v_inst_684_);
goto v___jp_692_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_array_get_borrowed(v_inst_682_, v_edited_683_, v_snd_688_);
lean_inc(v___x_698_);
v___x_699_ = lean_apply_2(v_inst_684_, v___x_698_, v_a_685_);
v___x_700_ = lean_unbox(v___x_699_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_del_object(v___x_690_);
v___x_701_ = 0;
v___x_702_ = lean_box(v___x_701_);
lean_inc(v___x_698_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_698_);
v___x_704_ = lean_array_push(v_fst_687_, v___x_703_);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_snd_688_, v___x_705_);
lean_dec(v_snd_688_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
else
{
goto v___jp_692_;
}
}
v___jp_692_:
{
lean_object* v___x_694_; 
if (v_isShared_691_ == 0)
{
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_snd_688_);
v___x_694_ = v_reuseFailAlloc_696_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object* v___x_710_, lean_object* v_inst_711_, lean_object* v_edited_712_, lean_object* v_inst_713_, lean_object* v_a_714_, lean_object* v_b_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Diff_diff___redArg___lam__3(v___x_710_, v_inst_711_, v_edited_712_, v_inst_713_, v_a_714_, v_b_715_);
lean_dec_ref(v_edited_712_);
lean_dec(v_inst_711_);
lean_dec(v___x_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object* v___x_717_, lean_object* v_inst_718_, lean_object* v_original_719_, lean_object* v_inst_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_edited_723_, lean_object* v_a_724_, lean_object* v_x_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_snd_727_; lean_object* v_fst_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_774_; 
v_snd_727_ = lean_ctor_get(v___y_726_, 1);
v_fst_728_ = lean_ctor_get(v___y_726_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___y_726_);
if (v_isSharedCheck_774_ == 0)
{
v___x_730_ = v___y_726_;
v_isShared_731_ = v_isSharedCheck_774_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_728_);
lean_dec(v___y_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_774_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_773_; 
v_fst_732_ = lean_ctor_get(v_snd_727_, 0);
v_snd_733_ = lean_ctor_get(v_snd_727_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_snd_727_);
if (v_isSharedCheck_773_ == 0)
{
v___x_735_ = v_snd_727_;
v_isShared_736_ = v_isSharedCheck_773_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v_snd_727_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_773_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___f_737_; lean_object* v___x_739_; 
lean_inc(v_a_724_);
lean_inc_ref(v_inst_720_);
lean_inc(v_inst_718_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_737_, 0, v___x_717_);
lean_closure_set(v___f_737_, 1, v_inst_718_);
lean_closure_set(v___f_737_, 2, v_original_719_);
lean_closure_set(v___f_737_, 3, v_inst_720_);
lean_closure_set(v___f_737_, 4, v_a_724_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v_fst_732_);
lean_ctor_set(v___x_735_, 0, v_fst_728_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_728_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_fst_732_);
v___x_739_ = v_reuseFailAlloc_772_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; lean_object* v_fst_741_; lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_771_; 
lean_inc_ref(v___x_721_);
v___x_740_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_721_, v___f_737_, v___x_739_);
v_fst_741_ = lean_ctor_get(v___x_740_, 0);
v_snd_742_ = lean_ctor_get(v___x_740_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_771_ == 0)
{
v___x_744_ = v___x_740_;
v_isShared_745_ = v_isSharedCheck_771_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_inc(v_fst_741_);
lean_dec(v___x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_771_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___f_746_; lean_object* v___x_748_; 
lean_inc(v_a_724_);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_746_, 0, v___x_722_);
lean_closure_set(v___f_746_, 1, v_inst_718_);
lean_closure_set(v___f_746_, 2, v_edited_723_);
lean_closure_set(v___f_746_, 3, v_inst_720_);
lean_closure_set(v___f_746_, 4, v_a_724_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v_snd_733_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_fst_741_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_snd_733_);
v___x_748_ = v_reuseFailAlloc_770_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v_fst_750_; lean_object* v_snd_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_769_; 
v___x_749_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_721_, v___f_746_, v___x_748_);
v_fst_750_ = lean_ctor_get(v___x_749_, 0);
v_snd_751_ = lean_ctor_get(v___x_749_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_769_ == 0)
{
v___x_753_ = v___x_749_;
v_isShared_754_ = v_isSharedCheck_769_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_snd_751_);
lean_inc(v_fst_750_);
lean_dec(v___x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_769_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = 2;
v___x_756_ = lean_box(v___x_755_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v_a_724_);
lean_ctor_set(v___x_753_, 0, v___x_756_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_724_);
v___x_758_ = v_reuseFailAlloc_768_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_759_ = lean_array_push(v_fst_750_, v___x_758_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_snd_742_, v___x_760_);
lean_dec(v_snd_742_);
v___x_762_ = lean_nat_add(v_snd_751_, v___x_760_);
lean_dec(v_snd_751_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_762_);
lean_ctor_set(v___x_730_, 0, v___x_761_);
v___x_764_ = v___x_730_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_767_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_759_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5(lean_object* v___x_775_, lean_object* v_original_776_, lean_object* v_b_777_){
_start:
{
lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_799_; 
v_fst_778_ = lean_ctor_get(v_b_777_, 0);
v_snd_779_ = lean_ctor_get(v_b_777_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_b_777_);
if (v_isSharedCheck_799_ == 0)
{
v___x_781_ = v_b_777_;
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_snd_779_);
lean_inc(v_fst_778_);
lean_dec(v_b_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_lt(v_snd_779_, v___x_775_);
if (v___x_783_ == 0)
{
lean_object* v___x_785_; 
if (v_isShared_782_ == 0)
{
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_fst_778_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_snd_779_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
else
{
uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_788_ = 1;
v___x_789_ = lean_array_fget_borrowed(v_original_776_, v_snd_779_);
v___x_790_ = lean_box(v___x_788_);
lean_inc(v___x_789_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_789_);
lean_ctor_set(v___x_781_, 0, v___x_790_);
v___x_792_ = v___x_781_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_789_);
v___x_792_ = v_reuseFailAlloc_798_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_793_ = lean_array_push(v_fst_778_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_add(v_snd_779_, v___x_794_);
lean_dec(v_snd_779_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_793_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5___boxed(lean_object* v___x_800_, lean_object* v_original_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Diff_diff___redArg___lam__5(v___x_800_, v_original_801_, v_b_802_);
lean_dec_ref(v_original_801_);
lean_dec(v___x_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6(lean_object* v___x_804_, lean_object* v_edited_805_, lean_object* v_b_806_){
_start:
{
lean_object* v_fst_807_; lean_object* v_snd_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_828_; 
v_fst_807_ = lean_ctor_get(v_b_806_, 0);
v_snd_808_ = lean_ctor_get(v_b_806_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_b_806_);
if (v_isSharedCheck_828_ == 0)
{
v___x_810_ = v_b_806_;
v_isShared_811_ = v_isSharedCheck_828_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snd_808_);
lean_inc(v_fst_807_);
lean_dec(v_b_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_828_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = lean_nat_dec_lt(v_snd_808_, v___x_804_);
if (v___x_812_ == 0)
{
lean_object* v___x_814_; 
if (v_isShared_811_ == 0)
{
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_fst_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_snd_808_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
else
{
uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_817_ = 0;
v___x_818_ = lean_array_fget_borrowed(v_edited_805_, v_snd_808_);
v___x_819_ = lean_box(v___x_817_);
lean_inc(v___x_818_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v___x_818_);
lean_ctor_set(v___x_810_, 0, v___x_819_);
v___x_821_ = v___x_810_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_818_);
v___x_821_ = v_reuseFailAlloc_827_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_822_ = lean_array_push(v_fst_807_, v___x_821_);
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_snd_808_, v___x_823_);
lean_dec(v_snd_808_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_822_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6___boxed(lean_object* v___x_829_, lean_object* v_edited_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Diff_diff___redArg___lam__6(v___x_829_, v_edited_830_, v_b_831_);
lean_dec_ref(v_edited_830_);
lean_dec(v___x_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg(lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_original_845_, lean_object* v_edited_846_){
_start:
{
lean_object* v___x_847_; lean_object* v_i_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_847_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_i_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get_size(v_original_845_);
v___x_850_ = lean_nat_dec_lt(v_i_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___f_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
lean_dec_ref(v_original_845_);
lean_dec(v_inst_844_);
lean_dec_ref(v_inst_843_);
lean_dec_ref(v_inst_842_);
v___f_851_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__0));
v_sz_852_ = lean_array_size(v_edited_846_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_847_, v___f_851_, v_sz_852_, v___x_853_, v_edited_846_);
return v___x_854_;
}
else
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = lean_array_get_size(v_edited_846_);
v___x_856_ = lean_nat_dec_lt(v_i_848_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___f_857_; size_t v_sz_858_; size_t v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v_edited_846_);
lean_dec(v_inst_844_);
lean_dec_ref(v_inst_843_);
lean_dec_ref(v_inst_842_);
v___f_857_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__1));
v_sz_858_ = lean_array_size(v_original_845_);
v___x_859_ = ((size_t)0ULL);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_847_, v___f_857_, v_sz_858_, v___x_859_, v_original_845_);
return v___x_860_;
}
else
{
lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_ds_864_; lean_object* v___x_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; lean_object* v_snd_869_; lean_object* v_fst_870_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_893_; 
lean_inc_ref_n(v_edited_846_, 2);
lean_inc_ref(v_inst_842_);
lean_inc_ref_n(v_original_845_, 2);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__4), 10, 7);
lean_closure_set(v___f_861_, 0, v___x_849_);
lean_closure_set(v___f_861_, 1, v_inst_844_);
lean_closure_set(v___f_861_, 2, v_original_845_);
lean_closure_set(v___f_861_, 3, v_inst_842_);
lean_closure_set(v___f_861_, 4, v___x_847_);
lean_closure_set(v___f_861_, 5, v___x_855_);
lean_closure_set(v___f_861_, 6, v_edited_846_);
v___x_862_ = l_Array_toSubarray___redArg(v_original_845_, v_i_848_, v___x_849_);
v___x_863_ = l_Array_toSubarray___redArg(v_edited_846_, v_i_848_, v___x_855_);
v_ds_864_ = l_Lean_Diff_lcs___redArg(v_inst_842_, v_inst_843_, v___x_862_, v___x_863_);
v___x_865_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__4));
v_sz_866_ = lean_array_size(v_ds_864_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_847_, v_ds_864_, v___f_861_, v_sz_866_, v___x_867_, v___x_865_);
v_snd_869_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_snd_869_);
v_fst_870_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_fst_870_);
lean_dec(v___x_868_);
v_fst_871_ = lean_ctor_get(v_snd_869_, 0);
v_snd_872_ = lean_ctor_get(v_snd_869_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_snd_869_);
if (v_isSharedCheck_893_ == 0)
{
v___x_874_ = v_snd_869_;
v_isShared_875_ = v_isSharedCheck_893_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
lean_dec(v_snd_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_893_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___f_876_; lean_object* v___x_878_; 
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_876_, 0, v___x_849_);
lean_closure_set(v___f_876_, 1, v_original_845_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v_fst_871_);
lean_ctor_set(v___x_874_, 0, v_fst_870_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_fst_871_);
v___x_878_ = v_reuseFailAlloc_892_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v_fst_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_890_; 
v___x_879_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_847_, v___f_876_, v___x_878_);
v_fst_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_879_, 1);
lean_dec(v_unused_891_);
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_fst_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___f_884_; lean_object* v___x_886_; 
v___f_884_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_884_, 0, v___x_855_);
lean_closure_set(v___f_884_, 1, v_edited_846_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_snd_872_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_880_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_snd_872_);
v___x_886_ = v_reuseFailAlloc_889_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v_fst_888_; 
v___x_887_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_847_, v___f_884_, v___x_886_);
v_fst_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_fst_888_);
lean_dec(v___x_887_);
return v_fst_888_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object* v_00_u03b1_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_original_898_, lean_object* v_edited_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Diff_diff___redArg(v_inst_895_, v_inst_896_, v_inst_897_, v_original_898_, v_edited_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object* v_inst_902_, lean_object* v_out_903_, lean_object* v_a_904_, lean_object* v_x_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_fst_907_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_fst_907_);
v_snd_908_ = lean_ctor_get(v_a_904_, 1);
lean_inc(v_snd_908_);
lean_dec_ref(v_a_904_);
v___x_909_ = lean_apply_1(v_inst_902_, v_snd_908_);
v___x_910_ = lean_string_dec_eq(v___x_909_, v_out_903_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_911_ = lean_unbox(v_fst_907_);
lean_dec(v_fst_907_);
v___x_912_ = l_Lean_Diff_Action_linePrefix(v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
v___x_915_ = lean_string_append(v___x_914_, v___x_909_);
lean_dec_ref(v___x_909_);
v___x_916_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
v___x_918_ = lean_string_append(v___y_906_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
else
{
uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v___x_909_);
v___x_920_ = lean_unbox(v_fst_907_);
lean_dec(v_fst_907_);
v___x_921_ = l_Lean_Diff_Action_linePrefix(v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
v___x_924_ = lean_string_append(v___y_906_, v___x_923_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object* v_inst_926_, lean_object* v_out_927_, lean_object* v_a_928_, lean_object* v_x_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Diff_linesToString___redArg___lam__0(v_inst_926_, v_out_927_, v_a_928_, v_x_929_, v___y_930_);
lean_dec_ref(v_out_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object* v_inst_933_, lean_object* v_lines_934_){
_start:
{
lean_object* v___x_935_; lean_object* v_out_936_; lean_object* v___f_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; 
v___x_935_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_out_936_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___closed__0));
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Diff_linesToString___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_937_, 0, v_inst_933_);
lean_closure_set(v___f_937_, 1, v_out_936_);
v_sz_938_ = lean_array_size(v_lines_934_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_935_, v_lines_934_, v___f_937_, v_sz_938_, v___x_939_, v_out_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object* v_00_u03b1_941_, lean_object* v_inst_942_, lean_object* v_lines_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Diff_linesToString___redArg(v_inst_942_, v_lines_943_);
return v___x_944_;
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
