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
lean_object* v_start_271_; lean_object* v_stop_272_; lean_object* v_i_273_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_start_271_ = lean_ctor_get(v_left_268_, 1);
v_stop_272_ = lean_ctor_get(v_left_268_, 2);
v_i_273_ = lean_array_get_size(v_pref_270_);
v___x_279_ = lean_nat_sub(v_stop_272_, v_start_271_);
v___x_280_ = lean_nat_dec_lt(v_i_273_, v___x_279_);
lean_dec(v___x_279_);
if (v___x_280_ == 0)
{
lean_dec_ref(v_inst_267_);
goto v___jp_274_;
}
else
{
lean_object* v_start_281_; lean_object* v_stop_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_start_281_ = lean_ctor_get(v_right_269_, 1);
v_stop_282_ = lean_ctor_get(v_right_269_, 2);
v___x_283_ = lean_nat_sub(v_stop_282_, v_start_281_);
v___x_284_ = lean_nat_dec_lt(v_i_273_, v___x_283_);
lean_dec(v___x_283_);
if (v___x_284_ == 0)
{
lean_dec_ref(v_inst_267_);
goto v___jp_274_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_285_ = l_Subarray_get___redArg(v_left_268_, v_i_273_);
v___x_286_ = l_Subarray_get___redArg(v_right_269_, v_i_273_);
lean_inc_ref(v_inst_267_);
lean_inc(v___x_285_);
v___x_287_ = lean_apply_2(v_inst_267_, v___x_285_, v___x_286_);
v___x_288_ = lean_unbox(v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v___x_285_);
lean_dec_ref(v_inst_267_);
v___x_289_ = l_Subarray_drop___redArg(v_left_268_, v_i_273_);
v___x_290_ = l_Subarray_drop___redArg(v_right_269_, v_i_273_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_pref_270_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_array_push(v_pref_270_, v___x_285_);
v_pref_270_ = v___x_293_;
goto _start;
}
}
}
v___jp_274_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = l_Subarray_drop___redArg(v_left_268_, v_i_273_);
v___x_276_ = l_Subarray_drop___redArg(v_right_269_, v_i_273_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_pref_270_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(lean_object* v_00_u03b1_295_, lean_object* v_inst_296_, lean_object* v_left_297_, lean_object* v_right_298_, lean_object* v_pref_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_296_, v_left_297_, v_right_298_, v_pref_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___redArg(lean_object* v_inst_303_, lean_object* v_left_304_, lean_object* v_right_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_307_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_303_, v_left_304_, v_right_305_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix(lean_object* v_00_u03b1_308_, lean_object* v_inst_309_, lean_object* v_left_310_, lean_object* v_right_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Diff_matchPrefix___redArg(v_inst_309_, v_left_310_, v_right_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(lean_object* v_it_313_, lean_object* v_acc_314_, lean_object* v_recur_315_){
_start:
{
lean_object* v_array_316_; lean_object* v_start_317_; lean_object* v_stop_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_331_; 
v_array_316_ = lean_ctor_get(v_it_313_, 0);
v_start_317_ = lean_ctor_get(v_it_313_, 1);
v_stop_318_ = lean_ctor_get(v_it_313_, 2);
v_isSharedCheck_331_ = !lean_is_exclusive(v_it_313_);
if (v_isSharedCheck_331_ == 0)
{
v___x_320_ = v_it_313_;
v_isShared_321_ = v_isSharedCheck_331_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_stop_318_);
lean_inc(v_start_317_);
lean_inc(v_array_316_);
lean_dec(v_it_313_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_331_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_lt(v_start_317_, v_stop_318_);
if (v___x_322_ == 0)
{
lean_del_object(v___x_320_);
lean_dec(v_stop_318_);
lean_dec(v_start_317_);
lean_dec_ref(v_array_316_);
lean_dec_ref(v_recur_315_);
return v_acc_314_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_add(v_start_317_, v___x_323_);
lean_inc_ref(v_array_316_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_324_);
v___x_326_ = v___x_320_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_array_316_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_stop_318_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_array_fget(v_array_316_, v_start_317_);
lean_dec(v_start_317_);
lean_dec_ref(v_array_316_);
v___x_328_ = lean_array_push(v_acc_314_, v___x_327_);
v___x_329_ = lean_apply_3(v_recur_315_, v___x_326_, v___x_328_, lean_box(0));
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(lean_object* v_inst_333_, lean_object* v_left_334_, lean_object* v_right_335_, lean_object* v_i_336_){
_start:
{
lean_object* v_start_337_; lean_object* v_stop_338_; lean_object* v___f_339_; lean_object* v___x_340_; uint8_t v___x_354_; 
v_start_337_ = lean_ctor_get(v_left_334_, 1);
v_stop_338_ = lean_ctor_get(v_left_334_, 2);
v___f_339_ = ((lean_object*)(l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0));
v___x_340_ = lean_nat_sub(v_stop_338_, v_start_337_);
v___x_354_ = lean_nat_dec_lt(v_i_336_, v___x_340_);
if (v___x_354_ == 0)
{
lean_dec_ref(v_inst_333_);
goto v___jp_341_;
}
else
{
lean_object* v_start_355_; lean_object* v_stop_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_start_355_ = lean_ctor_get(v_right_335_, 1);
v_stop_356_ = lean_ctor_get(v_right_335_, 2);
v___x_357_ = lean_nat_sub(v_stop_356_, v_start_355_);
v___x_358_ = lean_nat_dec_lt(v_i_336_, v___x_357_);
if (v___x_358_ == 0)
{
lean_dec(v___x_357_);
lean_dec_ref(v_inst_333_);
goto v___jp_341_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_359_ = lean_nat_sub(v___x_340_, v_i_336_);
lean_dec(v___x_340_);
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_sub(v___x_359_, v___x_360_);
v___x_362_ = l_Subarray_get___redArg(v_left_334_, v___x_361_);
lean_dec(v___x_361_);
v___x_363_ = lean_nat_sub(v___x_357_, v_i_336_);
lean_dec(v___x_357_);
v___x_364_ = lean_nat_sub(v___x_363_, v___x_360_);
v___x_365_ = l_Subarray_get___redArg(v_right_335_, v___x_364_);
lean_dec(v___x_364_);
lean_inc_ref(v_inst_333_);
v___x_366_ = lean_apply_2(v_inst_333_, v___x_362_, v___x_365_);
v___x_367_ = lean_unbox(v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_i_336_);
lean_dec_ref(v_inst_333_);
lean_inc_ref(v_left_334_);
v___x_368_ = l_Subarray_take___redArg(v_left_334_, v___x_359_);
v___x_369_ = l_Subarray_take___redArg(v_right_335_, v___x_363_);
lean_dec(v___x_363_);
v___x_370_ = l_Subarray_drop___redArg(v_left_334_, v___x_359_);
lean_dec(v___x_359_);
v___x_371_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_372_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_339_, v___x_370_, v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_369_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_368_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
lean_dec(v___x_363_);
lean_dec(v___x_359_);
v___x_375_ = lean_nat_add(v_i_336_, v___x_360_);
lean_dec(v_i_336_);
v_i_336_ = v___x_375_;
goto _start;
}
}
}
v___jp_341_:
{
lean_object* v_start_342_; lean_object* v_stop_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_start_342_ = lean_ctor_get(v_right_335_, 1);
v_stop_343_ = lean_ctor_get(v_right_335_, 2);
v___x_344_ = lean_nat_sub(v___x_340_, v_i_336_);
lean_dec(v___x_340_);
lean_inc_ref(v_left_334_);
v___x_345_ = l_Subarray_take___redArg(v_left_334_, v___x_344_);
v___x_346_ = lean_nat_sub(v_stop_343_, v_start_342_);
v___x_347_ = lean_nat_sub(v___x_346_, v_i_336_);
lean_dec(v_i_336_);
lean_dec(v___x_346_);
v___x_348_ = l_Subarray_take___redArg(v_right_335_, v___x_347_);
lean_dec(v___x_347_);
v___x_349_ = l_Subarray_drop___redArg(v_left_334_, v___x_344_);
lean_dec(v___x_344_);
v___x_350_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_351_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_339_, v___x_349_, v___x_350_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_348_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_345_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_left_379_, lean_object* v_right_380_, lean_object* v_i_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_378_, v_left_379_, v_right_380_, v_i_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object* v_inst_383_, lean_object* v_left_384_, lean_object* v_right_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_383_, v_left_384_, v_right_385_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_left_390_, lean_object* v_right_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Diff_matchSuffix___redArg(v_inst_389_, v_left_390_, v_right_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object* v___x_393_, lean_object* v_fst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_next_397_, lean_object* v_acc_398_, lean_object* v_h_399_, lean_object* v_G_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = lean_nat_dec_lt(v_next_397_, v___x_393_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_G_400_);
lean_dec(v_next_397_);
lean_dec_ref(v_inst_396_);
lean_dec_ref(v_inst_395_);
return v_acc_398_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_402_ = l_Subarray_get___redArg(v_fst_394_, v_next_397_);
lean_inc(v_next_397_);
v___x_403_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_395_, v_inst_396_, v_acc_398_, v_next_397_, v___x_402_);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_next_397_, v___x_404_);
lean_dec(v_next_397_);
v___x_406_ = lean_apply_4(v_G_400_, v___x_405_, v___x_403_, lean_box(0), lean_box(0));
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0___boxed(lean_object* v___x_407_, lean_object* v_fst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_next_411_, lean_object* v_acc_412_, lean_object* v_h_413_, lean_object* v_G_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Diff_lcs___redArg___lam__0(v___x_407_, v_fst_408_, v_inst_409_, v_inst_410_, v_next_411_, v_acc_412_, v_h_413_, v_G_414_);
lean_dec_ref(v_fst_408_);
lean_dec(v___x_407_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object* v___x_416_, lean_object* v_fst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_next_420_, lean_object* v_acc_421_, lean_object* v_h_422_, lean_object* v_G_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_lt(v_next_420_, v___x_416_);
if (v___x_424_ == 0)
{
lean_dec_ref(v_G_423_);
lean_dec(v_next_420_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
return v_acc_421_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_425_ = l_Subarray_get___redArg(v_fst_417_, v_next_420_);
lean_inc(v_next_420_);
v___x_426_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_418_, v_inst_419_, v_acc_421_, v_next_420_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_next_420_, v___x_427_);
lean_dec(v_next_420_);
v___x_429_ = lean_apply_4(v_G_423_, v___x_428_, v___x_426_, lean_box(0), lean_box(0));
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1___boxed(lean_object* v___x_430_, lean_object* v_fst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_next_434_, lean_object* v_acc_435_, lean_object* v_h_436_, lean_object* v_G_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Diff_lcs___redArg___lam__1(v___x_430_, v_fst_431_, v_inst_432_, v_inst_433_, v_next_434_, v_acc_435_, v_h_436_, v_G_437_);
lean_dec_ref(v_fst_431_);
lean_dec(v___x_430_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object* v_a_439_, lean_object* v_x_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_snd_442_; lean_object* v_leftIndex_443_; 
v_snd_442_ = lean_ctor_get(v_a_439_, 1);
lean_inc(v_snd_442_);
v_leftIndex_443_ = lean_ctor_get(v_snd_442_, 1);
lean_inc(v_leftIndex_443_);
if (lean_obj_tag(v_leftIndex_443_) == 1)
{
lean_object* v_rightIndex_444_; 
v_rightIndex_444_ = lean_ctor_get(v_snd_442_, 3);
lean_inc(v_rightIndex_444_);
if (lean_obj_tag(v_rightIndex_444_) == 1)
{
if (lean_obj_tag(v___y_441_) == 0)
{
lean_object* v_fst_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_473_; 
v_fst_445_ = lean_ctor_get(v_a_439_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v_a_439_, 1);
lean_dec(v_unused_474_);
v___x_447_ = v_a_439_;
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_fst_445_);
lean_dec(v_a_439_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_leftCount_449_; lean_object* v_rightCount_450_; lean_object* v_val_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_472_; 
v_leftCount_449_ = lean_ctor_get(v_snd_442_, 0);
lean_inc(v_leftCount_449_);
v_rightCount_450_ = lean_ctor_get(v_snd_442_, 2);
lean_inc(v_rightCount_450_);
lean_dec(v_snd_442_);
v_val_451_ = lean_ctor_get(v_leftIndex_443_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_leftIndex_443_);
if (v_isSharedCheck_472_ == 0)
{
v___x_453_ = v_leftIndex_443_;
v_isShared_454_ = v_isSharedCheck_472_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_val_451_);
lean_dec(v_leftIndex_443_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_472_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_471_; 
v_val_455_ = lean_ctor_get(v_rightIndex_444_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_rightIndex_444_);
if (v_isSharedCheck_471_ == 0)
{
v___x_457_ = v_rightIndex_444_;
v_isShared_458_ = v_isSharedCheck_471_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_rightIndex_444_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_471_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_nat_add(v_leftCount_449_, v_rightCount_450_);
lean_dec(v_rightCount_450_);
lean_dec(v_leftCount_449_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_val_455_);
lean_ctor_set(v___x_447_, 0, v_val_451_);
v___x_461_ = v___x_447_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_val_451_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_val_455_);
v___x_461_ = v_reuseFailAlloc_470_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_fst_445_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_459_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_463_);
v___x_465_ = v___x_457_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_465_);
v___x_467_ = v___x_453_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_475_; lean_object* v_fst_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_517_; 
v_val_475_ = lean_ctor_get(v___y_441_, 0);
lean_inc(v_val_475_);
v_fst_476_ = lean_ctor_get(v_a_439_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_a_439_, 1);
lean_dec(v_unused_518_);
v___x_478_ = v_a_439_;
v_isShared_479_ = v_isSharedCheck_517_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_fst_476_);
lean_dec(v_a_439_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_517_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_leftCount_480_; lean_object* v_rightCount_481_; lean_object* v_val_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_516_; 
v_leftCount_480_ = lean_ctor_get(v_snd_442_, 0);
lean_inc(v_leftCount_480_);
v_rightCount_481_ = lean_ctor_get(v_snd_442_, 2);
lean_inc(v_rightCount_481_);
lean_dec(v_snd_442_);
v_val_482_ = lean_ctor_get(v_leftIndex_443_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_leftIndex_443_);
if (v_isSharedCheck_516_ == 0)
{
v___x_484_ = v_leftIndex_443_;
v_isShared_485_ = v_isSharedCheck_516_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_val_482_);
lean_dec(v_leftIndex_443_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_516_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_val_486_; lean_object* v_fst_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_514_; 
v_val_486_ = lean_ctor_get(v_rightIndex_444_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_rightIndex_444_, 1);
v_fst_487_ = lean_ctor_get(v_val_475_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_val_475_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_val_475_, 1);
lean_dec(v_unused_515_);
v___x_489_ = v_val_475_;
v_isShared_490_ = v_isSharedCheck_514_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_fst_487_);
lean_dec(v_val_475_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_514_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_nat_add(v_leftCount_480_, v_rightCount_481_);
lean_dec(v_rightCount_481_);
lean_dec(v_leftCount_480_);
v___x_492_ = lean_nat_dec_lt(v___x_491_, v_fst_487_);
lean_dec(v_fst_487_);
if (v___x_492_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v___x_491_);
lean_del_object(v___x_489_);
lean_dec(v_val_486_);
lean_dec(v_val_482_);
lean_del_object(v___x_478_);
lean_dec(v_fst_476_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___y_441_);
v___x_494_ = v___x_484_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___y_441_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_512_; 
v_isSharedCheck_512_ = !lean_is_exclusive(v___y_441_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___y_441_, 0);
lean_dec(v_unused_513_);
v___x_497_ = v___y_441_;
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
else
{
lean_dec(v___y_441_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_val_486_);
lean_ctor_set(v___x_489_, 0, v_val_482_);
v___x_500_ = v___x_489_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_val_482_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_val_486_);
v___x_500_ = v_reuseFailAlloc_511_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_500_);
v___x_502_ = v___x_478_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_476_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_510_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_491_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_503_);
v___x_505_ = v___x_497_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_505_);
v___x_507_ = v___x_484_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
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
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_rightIndex_444_);
lean_dec(v_snd_442_);
lean_dec_ref(v_a_439_);
v_isSharedCheck_525_ = !lean_is_exclusive(v_leftIndex_443_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_leftIndex_443_, 0);
lean_dec(v_unused_526_);
v___x_520_ = v_leftIndex_443_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_leftIndex_443_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___y_441_);
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___y_441_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v___x_527_; 
lean_dec(v_leftIndex_443_);
lean_dec(v_snd_442_);
lean_dec_ref(v_a_439_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___y_441_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object* v_a_528_, lean_object* v_b_529_, lean_object* v_d_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_a_528_);
lean_ctor_set(v___x_531_, 1, v_b_529_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_d_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__4(lean_object* v___x_533_, lean_object* v___f_534_, lean_object* v_l_535_, lean_object* v_acc_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_533_, v___f_534_, v_acc_536_, v_l_535_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__10(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_unsigned_to_nat(16u);
v___x_559_ = lean_mk_array(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__11(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_hist_562_; 
v___x_560_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__10, &l_Lean_Diff_lcs___redArg___closed__10_once, _init_l_Lean_Diff_lcs___redArg___closed__10);
v___x_561_ = lean_unsigned_to_nat(0u);
v_hist_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_562_, 0, v___x_561_);
lean_ctor_set(v_hist_562_, 1, v___x_560_);
return v_hist_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_left_570_, lean_object* v_right_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_snd_574_; lean_object* v_fst_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; lean_object* v_snd_579_; lean_object* v_fst_580_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v_start_583_; lean_object* v_stop_584_; lean_object* v_start_585_; lean_object* v_stop_586_; lean_object* v___x_587_; lean_object* v_hist_588_; lean_object* v___x_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v_buckets_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___y_599_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_572_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
lean_inc_ref_n(v_inst_568_, 4);
v___x_573_ = l_Lean_Diff_matchPrefix___redArg(v_inst_568_, v_left_570_, v_right_571_);
v_snd_574_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_snd_574_);
v_fst_575_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_fst_575_);
lean_dec_ref(v___x_573_);
v_fst_576_ = lean_ctor_get(v_snd_574_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_snd_574_, 1);
lean_inc(v_snd_577_);
lean_dec(v_snd_574_);
v___x_578_ = l_Lean_Diff_matchSuffix___redArg(v_inst_568_, v_fst_576_, v_snd_577_);
v_snd_579_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_snd_579_);
v_fst_580_ = lean_ctor_get(v___x_578_, 0);
lean_inc_n(v_fst_580_, 2);
lean_dec_ref(v___x_578_);
v_fst_581_ = lean_ctor_get(v_snd_579_, 0);
lean_inc_n(v_fst_581_, 2);
v_snd_582_ = lean_ctor_get(v_snd_579_, 1);
lean_inc(v_snd_582_);
lean_dec(v_snd_579_);
v_start_583_ = lean_ctor_get(v_fst_580_, 1);
v_stop_584_ = lean_ctor_get(v_fst_580_, 2);
v_start_585_ = lean_ctor_get(v_fst_581_, 1);
v_stop_586_ = lean_ctor_get(v_fst_581_, 2);
v___x_587_ = lean_unsigned_to_nat(0u);
v_hist_588_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__11, &l_Lean_Diff_lcs___redArg___closed__11_once, _init_l_Lean_Diff_lcs___redArg___closed__11);
v___x_589_ = lean_nat_sub(v_stop_584_, v_start_583_);
lean_inc_ref_n(v_inst_569_, 2);
v___f_590_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_590_, 0, v___x_589_);
lean_closure_set(v___f_590_, 1, v_fst_580_);
lean_closure_set(v___f_590_, 2, v_inst_568_);
lean_closure_set(v___f_590_, 3, v_inst_569_);
v___x_591_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_590_, v___x_587_, v_hist_588_, lean_box(0));
v___x_592_ = lean_nat_sub(v_stop_586_, v_start_585_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_593_, 0, v___x_592_);
lean_closure_set(v___f_593_, 1, v_fst_581_);
lean_closure_set(v___f_593_, 2, v_inst_568_);
lean_closure_set(v___f_593_, 3, v_inst_569_);
v___x_594_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_593_, v___x_587_, v___x_591_, lean_box(0));
v_buckets_595_ = lean_ctor_get(v___x_594_, 1);
lean_inc_ref(v_buckets_595_);
lean_dec(v___x_594_);
v___f_596_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__12));
v___x_597_ = lean_box(0);
v___x_625_ = lean_box(0);
v___x_626_ = lean_array_get_size(v_buckets_595_);
v___x_627_ = lean_nat_dec_lt(v___x_587_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec_ref(v_buckets_595_);
v___y_599_ = v___x_625_;
goto v___jp_598_;
}
else
{
lean_object* v___f_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___f_628_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__14));
v___x_629_ = lean_usize_of_nat(v___x_626_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_572_, v___f_628_, v_buckets_595_, v___x_629_, v___x_630_, v___x_625_);
v___y_599_ = v___x_631_;
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = l_List_forIn_x27_loop___redArg(v___x_572_, v___f_596_, v___y_599_, v___x_597_);
lean_dec(v___y_599_);
if (lean_obj_tag(v___x_600_) == 1)
{
lean_object* v_val_601_; lean_object* v_snd_602_; lean_object* v_snd_603_; lean_object* v_fst_604_; lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_607_; lean_object* v_fst_608_; lean_object* v_snd_609_; lean_object* v___x_610_; lean_object* v_fst_611_; lean_object* v_snd_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_val_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v___x_600_, 1);
v_snd_602_ = lean_ctor_get(v_val_601_, 1);
lean_inc(v_snd_602_);
lean_dec(v_val_601_);
v_snd_603_ = lean_ctor_get(v_snd_602_, 1);
lean_inc(v_snd_603_);
v_fst_604_ = lean_ctor_get(v_snd_602_, 0);
lean_inc(v_fst_604_);
lean_dec(v_snd_602_);
v_fst_605_ = lean_ctor_get(v_snd_603_, 0);
lean_inc(v_fst_605_);
v_snd_606_ = lean_ctor_get(v_snd_603_, 1);
lean_inc(v_snd_606_);
lean_dec(v_snd_603_);
v___x_607_ = l_Subarray_split___redArg(v_fst_580_, v_fst_605_);
lean_dec(v_fst_605_);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_fst_608_);
v_snd_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_snd_609_);
lean_dec_ref(v___x_607_);
v___x_610_ = l_Subarray_split___redArg(v_fst_581_, v_snd_606_);
lean_dec(v_snd_606_);
v_fst_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_fst_611_);
v_snd_612_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_snd_612_);
lean_dec_ref(v___x_610_);
lean_inc_ref(v_inst_569_);
lean_inc_ref(v_inst_568_);
v___x_613_ = l_Lean_Diff_lcs___redArg(v_inst_568_, v_inst_569_, v_fst_608_, v_fst_611_);
v___x_614_ = l_Array_append___redArg(v_fst_575_, v___x_613_);
lean_dec_ref(v___x_613_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_array_push(v___x_616_, v_fst_604_);
v___x_618_ = l_Array_append___redArg(v___x_614_, v___x_617_);
lean_dec_ref(v___x_617_);
v___x_619_ = l_Subarray_drop___redArg(v_snd_609_, v___x_615_);
v___x_620_ = l_Subarray_drop___redArg(v_snd_612_, v___x_615_);
v___x_621_ = l_Lean_Diff_lcs___redArg(v_inst_568_, v_inst_569_, v___x_619_, v___x_620_);
v___x_622_ = l_Array_append___redArg(v___x_618_, v___x_621_);
lean_dec_ref(v___x_621_);
v___x_623_ = l_Array_append___redArg(v___x_622_, v_snd_582_);
lean_dec(v_snd_582_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v___x_600_);
lean_dec(v_fst_581_);
lean_dec(v_fst_580_);
lean_dec_ref(v_inst_569_);
lean_dec_ref(v_inst_568_);
v___x_624_ = l_Array_append___redArg(v_fst_575_, v_snd_582_);
lean_dec(v_snd_582_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object* v_00_u03b1_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_left_635_, lean_object* v_right_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Diff_lcs___redArg(v_inst_633_, v_inst_634_, v_left_635_, v_right_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object* v_x_638_){
_start:
{
uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = 0;
v___x_640_ = lean_box(v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_x_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object* v_x_642_){
_start:
{
uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = 1;
v___x_644_ = lean_box(v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_x_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object* v_inst_646_, lean_object* v_original_647_, lean_object* v___x_648_, lean_object* v_inst_649_, lean_object* v_a_650_, lean_object* v_b_651_){
_start:
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_677_; 
v_fst_652_ = lean_ctor_get(v_b_651_, 0);
v_snd_653_ = lean_ctor_get(v_b_651_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_b_651_);
if (v_isSharedCheck_677_ == 0)
{
v___x_655_ = v_b_651_;
v_isShared_656_ = v_isSharedCheck_677_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec(v_b_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_677_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
uint8_t v___y_663_; uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_snd_653_, v___x_648_);
if (v___x_673_ == 0)
{
lean_dec(v_a_650_);
lean_dec_ref(v_inst_649_);
v___y_663_ = v___x_673_;
goto v___jp_662_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_array_get_borrowed(v_inst_646_, v_original_647_, v_snd_653_);
lean_inc(v___x_674_);
v___x_675_ = lean_apply_2(v_inst_649_, v___x_674_, v_a_650_);
v___x_676_ = lean_unbox(v___x_675_);
if (v___x_676_ == 0)
{
v___y_663_ = v___x_673_;
goto v___jp_662_;
}
else
{
goto v___jp_657_;
}
}
v___jp_657_:
{
lean_object* v___x_659_; 
if (v_isShared_656_ == 0)
{
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_snd_653_);
v___x_659_ = v_reuseFailAlloc_661_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
goto v___jp_657_;
}
else
{
uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_del_object(v___x_655_);
v___x_664_ = 1;
v___x_665_ = lean_array_get_borrowed(v_inst_646_, v_original_647_, v_snd_653_);
v___x_666_ = lean_box(v___x_664_);
lean_inc(v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
v___x_668_ = lean_array_push(v_fst_652_, v___x_667_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_snd_653_, v___x_669_);
lean_dec(v_snd_653_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_668_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object* v_inst_678_, lean_object* v_original_679_, lean_object* v___x_680_, lean_object* v_inst_681_, lean_object* v_a_682_, lean_object* v_b_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Diff_diff___redArg___lam__2(v_inst_678_, v_original_679_, v___x_680_, v_inst_681_, v_a_682_, v_b_683_);
lean_dec(v___x_680_);
lean_dec_ref(v_original_679_);
lean_dec(v_inst_678_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object* v_inst_685_, lean_object* v_edited_686_, lean_object* v___x_687_, lean_object* v_inst_688_, lean_object* v_a_689_, lean_object* v_b_690_){
_start:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_716_; 
v_fst_691_ = lean_ctor_get(v_b_690_, 0);
v_snd_692_ = lean_ctor_get(v_b_690_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_b_690_);
if (v_isSharedCheck_716_ == 0)
{
v___x_694_ = v_b_690_;
v_isShared_695_ = v_isSharedCheck_716_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snd_692_);
lean_inc(v_fst_691_);
lean_dec(v_b_690_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_716_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
uint8_t v___y_702_; uint8_t v___x_712_; 
v___x_712_ = lean_nat_dec_lt(v_snd_692_, v___x_687_);
if (v___x_712_ == 0)
{
lean_dec(v_a_689_);
lean_dec_ref(v_inst_688_);
v___y_702_ = v___x_712_;
goto v___jp_701_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_array_get_borrowed(v_inst_685_, v_edited_686_, v_snd_692_);
lean_inc(v___x_713_);
v___x_714_ = lean_apply_2(v_inst_688_, v___x_713_, v_a_689_);
v___x_715_ = lean_unbox(v___x_714_);
if (v___x_715_ == 0)
{
v___y_702_ = v___x_712_;
goto v___jp_701_;
}
else
{
goto v___jp_696_;
}
}
v___jp_696_:
{
lean_object* v___x_698_; 
if (v_isShared_695_ == 0)
{
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_692_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
v___jp_701_:
{
if (v___y_702_ == 0)
{
goto v___jp_696_;
}
else
{
uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_del_object(v___x_694_);
v___x_703_ = 0;
v___x_704_ = lean_array_get_borrowed(v_inst_685_, v_edited_686_, v_snd_692_);
v___x_705_ = lean_box(v___x_703_);
lean_inc(v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
v___x_707_ = lean_array_push(v_fst_691_, v___x_706_);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_snd_692_, v___x_708_);
lean_dec(v_snd_692_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_707_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object* v_inst_717_, lean_object* v_edited_718_, lean_object* v___x_719_, lean_object* v_inst_720_, lean_object* v_a_721_, lean_object* v_b_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Diff_diff___redArg___lam__3(v_inst_717_, v_edited_718_, v___x_719_, v_inst_720_, v_a_721_, v_b_722_);
lean_dec(v___x_719_);
lean_dec_ref(v_edited_718_);
lean_dec(v_inst_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object* v_inst_724_, lean_object* v_original_725_, lean_object* v___x_726_, lean_object* v_inst_727_, lean_object* v___x_728_, lean_object* v_edited_729_, lean_object* v___x_730_, lean_object* v_a_731_, lean_object* v_x_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_snd_734_; lean_object* v_fst_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_781_; 
v_snd_734_ = lean_ctor_get(v___y_733_, 1);
v_fst_735_ = lean_ctor_get(v___y_733_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___y_733_);
if (v_isSharedCheck_781_ == 0)
{
v___x_737_ = v___y_733_;
v_isShared_738_ = v_isSharedCheck_781_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_735_);
lean_dec(v___y_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_781_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_fst_739_; lean_object* v_snd_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_780_; 
v_fst_739_ = lean_ctor_get(v_snd_734_, 0);
v_snd_740_ = lean_ctor_get(v_snd_734_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_snd_734_);
if (v_isSharedCheck_780_ == 0)
{
v___x_742_ = v_snd_734_;
v_isShared_743_ = v_isSharedCheck_780_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snd_740_);
lean_inc(v_fst_739_);
lean_dec(v_snd_734_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_780_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___f_744_; lean_object* v___x_746_; 
lean_inc(v_a_731_);
lean_inc_ref(v_inst_727_);
lean_inc(v_inst_724_);
v___f_744_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_744_, 0, v_inst_724_);
lean_closure_set(v___f_744_, 1, v_original_725_);
lean_closure_set(v___f_744_, 2, v___x_726_);
lean_closure_set(v___f_744_, 3, v_inst_727_);
lean_closure_set(v___f_744_, 4, v_a_731_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v_fst_739_);
lean_ctor_set(v___x_742_, 0, v_fst_735_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_fst_735_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_fst_739_);
v___x_746_ = v_reuseFailAlloc_779_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_778_; 
lean_inc_ref(v___x_728_);
v___x_747_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_728_, v___f_744_, v___x_746_);
v_fst_748_ = lean_ctor_get(v___x_747_, 0);
v_snd_749_ = lean_ctor_get(v___x_747_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_778_ == 0)
{
v___x_751_ = v___x_747_;
v_isShared_752_ = v_isSharedCheck_778_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snd_749_);
lean_inc(v_fst_748_);
lean_dec(v___x_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_778_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___f_753_; lean_object* v___x_755_; 
lean_inc(v_a_731_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_753_, 0, v_inst_724_);
lean_closure_set(v___f_753_, 1, v_edited_729_);
lean_closure_set(v___f_753_, 2, v___x_730_);
lean_closure_set(v___f_753_, 3, v_inst_727_);
lean_closure_set(v___f_753_, 4, v_a_731_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v_snd_740_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_fst_748_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_snd_740_);
v___x_755_ = v_reuseFailAlloc_777_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_776_; 
v___x_756_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_728_, v___f_753_, v___x_755_);
v_fst_757_ = lean_ctor_get(v___x_756_, 0);
v_snd_758_ = lean_ctor_get(v___x_756_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_776_ == 0)
{
v___x_760_ = v___x_756_;
v_isShared_761_ = v_isSharedCheck_776_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_dec(v___x_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_776_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_762_ = 2;
v___x_763_ = lean_box(v___x_762_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_a_731_);
lean_ctor_set(v___x_760_, 0, v___x_763_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_731_);
v___x_765_ = v_reuseFailAlloc_775_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_766_ = lean_array_push(v_fst_757_, v___x_765_);
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_snd_749_, v___x_767_);
lean_dec(v_snd_749_);
v___x_769_ = lean_nat_add(v_snd_758_, v___x_767_);
lean_dec(v_snd_758_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_769_);
lean_ctor_set(v___x_737_, 0, v___x_768_);
v___x_771_ = v___x_737_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_774_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_766_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5(lean_object* v___x_782_, lean_object* v_original_783_, lean_object* v_b_784_){
_start:
{
lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_806_; 
v_fst_785_ = lean_ctor_get(v_b_784_, 0);
v_snd_786_ = lean_ctor_get(v_b_784_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_b_784_);
if (v_isSharedCheck_806_ == 0)
{
v___x_788_ = v_b_784_;
v_isShared_789_ = v_isSharedCheck_806_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_inc(v_fst_785_);
lean_dec(v_b_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_806_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_lt(v_snd_786_, v___x_782_);
if (v___x_790_ == 0)
{
lean_object* v___x_792_; 
if (v_isShared_789_ == 0)
{
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_fst_785_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_786_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
else
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_795_ = 1;
v___x_796_ = lean_array_fget_borrowed(v_original_783_, v_snd_786_);
v___x_797_ = lean_box(v___x_795_);
lean_inc(v___x_796_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_796_);
lean_ctor_set(v___x_788_, 0, v___x_797_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_796_);
v___x_799_ = v_reuseFailAlloc_805_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_800_ = lean_array_push(v_fst_785_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_snd_786_, v___x_801_);
lean_dec(v_snd_786_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__5___boxed(lean_object* v___x_807_, lean_object* v_original_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Diff_diff___redArg___lam__5(v___x_807_, v_original_808_, v_b_809_);
lean_dec_ref(v_original_808_);
lean_dec(v___x_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6(lean_object* v___x_811_, lean_object* v_edited_812_, lean_object* v_b_813_){
_start:
{
lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_835_; 
v_fst_814_ = lean_ctor_get(v_b_813_, 0);
v_snd_815_ = lean_ctor_get(v_b_813_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_b_813_);
if (v_isSharedCheck_835_ == 0)
{
v___x_817_ = v_b_813_;
v_isShared_818_ = v_isSharedCheck_835_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v_b_813_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_835_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v___x_819_; 
v___x_819_ = lean_nat_dec_lt(v_snd_815_, v___x_811_);
if (v___x_819_ == 0)
{
lean_object* v___x_821_; 
if (v_isShared_818_ == 0)
{
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_fst_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_snd_815_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
else
{
uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_824_ = 0;
v___x_825_ = lean_array_fget_borrowed(v_edited_812_, v_snd_815_);
v___x_826_ = lean_box(v___x_824_);
lean_inc(v___x_825_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_825_);
lean_ctor_set(v___x_817_, 0, v___x_826_);
v___x_828_ = v___x_817_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_825_);
v___x_828_ = v_reuseFailAlloc_834_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_829_ = lean_array_push(v_fst_814_, v___x_828_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_snd_815_, v___x_830_);
lean_dec(v_snd_815_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_829_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__6___boxed(lean_object* v___x_836_, lean_object* v_edited_837_, lean_object* v_b_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Diff_diff___redArg___lam__6(v___x_836_, v_edited_837_, v_b_838_);
lean_dec_ref(v_edited_837_);
lean_dec(v___x_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg(lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_original_852_, lean_object* v_edited_853_){
_start:
{
lean_object* v_i_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_i_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_array_get_size(v_original_852_);
v___x_856_ = lean_nat_dec_lt(v_i_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___f_857_; lean_object* v___x_858_; size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_original_852_);
lean_dec(v_inst_851_);
lean_dec_ref(v_inst_850_);
lean_dec_ref(v_inst_849_);
v___f_857_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__0));
v___x_858_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_sz_859_ = lean_array_size(v_edited_853_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_858_, v___f_857_, v_sz_859_, v___x_860_, v_edited_853_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_array_get_size(v_edited_853_);
v___x_863_ = lean_nat_dec_lt(v_i_854_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___f_864_; lean_object* v___x_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v_edited_853_);
lean_dec(v_inst_851_);
lean_dec_ref(v_inst_850_);
lean_dec_ref(v_inst_849_);
v___f_864_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__1));
v___x_865_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_sz_866_ = lean_array_size(v_original_852_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_865_, v___f_864_, v_sz_866_, v___x_867_, v_original_852_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_ds_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; size_t v_sz_875_; size_t v___x_876_; lean_object* v___x_877_; lean_object* v_snd_878_; lean_object* v_fst_879_; lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_902_; 
lean_inc_ref_n(v_original_852_, 2);
v___x_869_ = l_Array_toSubarray___redArg(v_original_852_, v_i_854_, v___x_855_);
lean_inc_ref_n(v_edited_853_, 2);
v___x_870_ = l_Array_toSubarray___redArg(v_edited_853_, v_i_854_, v___x_862_);
lean_inc_ref(v_inst_849_);
v_ds_871_ = l_Lean_Diff_lcs___redArg(v_inst_849_, v_inst_850_, v___x_869_, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__4), 10, 7);
lean_closure_set(v___f_873_, 0, v_inst_851_);
lean_closure_set(v___f_873_, 1, v_original_852_);
lean_closure_set(v___f_873_, 2, v___x_855_);
lean_closure_set(v___f_873_, 3, v_inst_849_);
lean_closure_set(v___f_873_, 4, v___x_872_);
lean_closure_set(v___f_873_, 5, v_edited_853_);
lean_closure_set(v___f_873_, 6, v___x_862_);
v___x_874_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__4));
v_sz_875_ = lean_array_size(v_ds_871_);
v___x_876_ = ((size_t)0ULL);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_872_, v_ds_871_, v___f_873_, v_sz_875_, v___x_876_, v___x_874_);
v_snd_878_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_snd_878_);
v_fst_879_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_fst_879_);
lean_dec(v___x_877_);
v_fst_880_ = lean_ctor_get(v_snd_878_, 0);
v_snd_881_ = lean_ctor_get(v_snd_878_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_snd_878_);
if (v_isSharedCheck_902_ == 0)
{
v___x_883_ = v_snd_878_;
v_isShared_884_ = v_isSharedCheck_902_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snd_881_);
lean_inc(v_fst_880_);
lean_dec(v_snd_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_902_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___f_885_; lean_object* v___x_887_; 
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_885_, 0, v___x_855_);
lean_closure_set(v___f_885_, 1, v_original_852_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_fst_880_);
lean_ctor_set(v___x_883_, 0, v_fst_879_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_fst_879_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_fst_880_);
v___x_887_ = v_reuseFailAlloc_901_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v_fst_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v___x_888_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_872_, v___f_885_, v___x_887_);
v_fst_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_888_, 1);
lean_dec(v_unused_900_);
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_fst_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___f_893_; lean_object* v___x_895_; 
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_893_, 0, v___x_862_);
lean_closure_set(v___f_893_, 1, v_edited_853_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_snd_881_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_889_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_881_);
v___x_895_ = v_reuseFailAlloc_898_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v_fst_897_; 
v___x_896_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_872_, v___f_893_, v___x_895_);
v_fst_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_fst_897_);
lean_dec(v___x_896_);
return v_fst_897_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object* v_00_u03b1_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_original_907_, lean_object* v_edited_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Diff_diff___redArg(v_inst_904_, v_inst_905_, v_inst_906_, v_original_907_, v_edited_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object* v_inst_911_, lean_object* v_out_912_, lean_object* v_a_913_, lean_object* v_x_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_fst_916_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_fst_916_);
v_snd_917_ = lean_ctor_get(v_a_913_, 1);
lean_inc(v_snd_917_);
lean_dec_ref(v_a_913_);
v___x_918_ = lean_apply_1(v_inst_911_, v_snd_917_);
v___x_919_ = lean_string_dec_eq(v___x_918_, v_out_912_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_920_ = lean_unbox(v_fst_916_);
lean_dec(v_fst_916_);
v___x_921_ = l_Lean_Diff_Action_linePrefix(v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
v___x_924_ = lean_string_append(v___x_923_, v___x_918_);
lean_dec_ref(v___x_918_);
v___x_925_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
v___x_927_ = lean_string_append(v___y_915_, v___x_926_);
lean_dec_ref(v___x_926_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v___x_918_);
v___x_929_ = lean_unbox(v_fst_916_);
lean_dec(v_fst_916_);
v___x_930_ = l_Lean_Diff_Action_linePrefix(v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = lean_string_append(v___y_915_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object* v_inst_935_, lean_object* v_out_936_, lean_object* v_a_937_, lean_object* v_x_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Diff_linesToString___redArg___lam__0(v_inst_935_, v_out_936_, v_a_937_, v_x_938_, v___y_939_);
lean_dec_ref(v_out_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object* v_inst_942_, lean_object* v_lines_943_){
_start:
{
lean_object* v___x_944_; lean_object* v_out_945_; lean_object* v___f_946_; size_t v_sz_947_; size_t v___x_948_; lean_object* v___x_949_; 
v___x_944_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_out_945_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___closed__0));
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Diff_linesToString___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_946_, 0, v_inst_942_);
lean_closure_set(v___f_946_, 1, v_out_945_);
v_sz_947_ = lean_array_size(v_lines_943_);
v___x_948_ = ((size_t)0ULL);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_944_, v_lines_943_, v___f_946_, v_sz_947_, v___x_948_, v_out_945_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_, lean_object* v_lines_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Diff_linesToString___redArg(v_inst_951_, v_lines_952_);
return v___x_953_;
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
