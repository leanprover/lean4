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
LEAN_EXPORT lean_object* l_Lean_Diff_Action_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Action_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Diff_Action_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Diff_Action_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Diff_Action_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Diff_Action_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Diff_Action_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg(lean_object* v_insert_28_){
_start:
{
lean_inc(v_insert_28_);
return v_insert_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___redArg___boxed(lean_object* v_insert_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Diff_Action_insert_elim___redArg(v_insert_29_);
lean_dec(v_insert_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_insert_34_){
_start:
{
lean_inc(v_insert_34_);
return v_insert_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_insert_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_insert_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Diff_Action_insert_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_insert_38_);
lean_dec(v_insert_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg(lean_object* v_delete_41_){
_start:
{
lean_inc(v_delete_41_);
return v_delete_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___redArg___boxed(lean_object* v_delete_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Diff_Action_delete_elim___redArg(v_delete_42_);
lean_dec(v_delete_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_delete_47_){
_start:
{
lean_inc(v_delete_47_);
return v_delete_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_delete_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_delete_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Diff_Action_delete_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_delete_51_);
lean_dec(v_delete_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg(lean_object* v_skip_54_){
_start:
{
lean_inc(v_skip_54_);
return v_skip_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___redArg___boxed(lean_object* v_skip_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Diff_Action_skip_elim___redArg(v_skip_55_);
lean_dec(v_skip_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_skip_60_){
_start:
{
lean_inc(v_skip_60_);
return v_skip_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_skip_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_skip_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Diff_Action_skip_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_skip_64_);
lean_dec(v_skip_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Diff_instReprAction_repr___closed__7(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr(uint8_t v_x_80_, lean_object* v_prec_81_){
_start:
{
lean_object* v___y_83_; lean_object* v___y_90_; lean_object* v___y_97_; 
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_81_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_83_ = v___x_105_;
goto v___jp_82_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_83_ = v___x_106_;
goto v___jp_82_;
}
}
case 1:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_81_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_90_ = v___x_109_;
goto v___jp_89_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_90_ = v___x_110_;
goto v___jp_89_;
}
}
default: 
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1024u);
v___x_112_ = lean_nat_dec_le(v___x_111_, v_prec_81_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__6, &l_Lean_Diff_instReprAction_repr___closed__6_once, _init_l_Lean_Diff_instReprAction_repr___closed__6);
v___y_97_ = v___x_113_;
goto v___jp_96_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Diff_instReprAction_repr___closed__7, &l_Lean_Diff_instReprAction_repr___closed__7_once, _init_l_Lean_Diff_instReprAction_repr___closed__7);
v___y_97_ = v___x_114_;
goto v___jp_96_;
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__1));
lean_inc(v___y_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___y_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = 0;
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = l_Repr_addAppParen(v___x_87_, v_prec_81_);
return v___x_88_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__3));
lean_inc(v___y_90_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___y_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
v___x_95_ = l_Repr_addAppParen(v___x_94_, v_prec_81_);
return v___x_95_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = ((lean_object*)(l_Lean_Diff_instReprAction_repr___closed__5));
lean_inc(v___y_97_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_100_);
v___x_102_ = l_Repr_addAppParen(v___x_101_, v_prec_81_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instReprAction_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_177__boxed_117_; lean_object* v_res_118_; 
v_x_177__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lean_Diff_instReprAction_repr(v_x_177__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t v_x_121_, uint8_t v_y_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = l_Lean_Diff_Action_ctorIdx(v_x_121_);
v___x_124_ = l_Lean_Diff_Action_ctorIdx(v_y_122_);
v___x_125_ = lean_nat_dec_eq(v___x_123_, v___x_124_);
lean_dec(v___x_124_);
lean_dec(v___x_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instBEqAction_beq___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
uint8_t v_x_17__boxed_128_; uint8_t v_y_18__boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_x_17__boxed_128_ = lean_unbox(v_x_126_);
v_y_18__boxed_129_ = lean_unbox(v_y_127_);
v_res_130_ = l_Lean_Diff_instBEqAction_beq(v_x_17__boxed_128_, v_y_18__boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint64_t l_Lean_Diff_instHashableAction_hash(uint8_t v_x_134_){
_start:
{
switch(v_x_134_)
{
case 0:
{
uint64_t v___x_135_; 
v___x_135_ = 0ULL;
return v___x_135_;
}
case 1:
{
uint64_t v___x_136_; 
v___x_136_ = 1ULL;
return v___x_136_;
}
default: 
{
uint64_t v___x_137_; 
v___x_137_ = 2ULL;
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instHashableAction_hash___boxed(lean_object* v_x_138_){
_start:
{
uint8_t v_x_40__boxed_139_; uint64_t v_res_140_; lean_object* v_r_141_; 
v_x_40__boxed_139_ = lean_unbox(v_x_138_);
v_res_140_ = l_Lean_Diff_instHashableAction_hash(v_x_40__boxed_139_);
v_r_141_ = lean_box_uint64(v_res_140_);
return v_r_141_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction_default(void){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
static uint8_t _init_l_Lean_Diff_instInhabitedAction(void){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0(uint8_t v_x_149_){
_start:
{
switch(v_x_149_)
{
case 0:
{
lean_object* v___x_150_; 
v___x_150_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__0));
return v___x_150_;
}
case 1:
{
lean_object* v___x_151_; 
v___x_151_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__1));
return v___x_151_;
}
default: 
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Lean_Diff_instToStringAction___lam__0___closed__2));
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_instToStringAction___lam__0___boxed(lean_object* v_x_153_){
_start:
{
uint8_t v_x_36__boxed_154_; lean_object* v_res_155_; 
v_x_36__boxed_154_ = lean_unbox(v_x_153_);
v_res_155_ = l_Lean_Diff_instToStringAction___lam__0(v_x_36__boxed_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix(uint8_t v_x_161_){
_start:
{
switch(v_x_161_)
{
case 0:
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__0));
return v___x_162_;
}
case 1:
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__1));
return v___x_163_;
}
default: 
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Action_linePrefix___boxed(lean_object* v_x_165_){
_start:
{
uint8_t v_x_31__boxed_166_; lean_object* v_res_167_; 
v_x_31__boxed_166_ = lean_unbox(v_x_165_);
v_res_167_ = l_Lean_Diff_Action_linePrefix(v_x_31__boxed_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___redArg(lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_histogram_170_, lean_object* v_index_171_, lean_object* v_val_172_){
_start:
{
lean_object* v___x_173_; 
lean_inc(v_val_172_);
lean_inc_ref(v_inst_169_);
lean_inc_ref(v_inst_168_);
v___x_173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_168_, v_inst_169_, v_histogram_170_, v_val_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v_index_171_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_178_, 0, v___x_174_);
lean_ctor_set(v___x_178_, 1, v___x_175_);
lean_ctor_set(v___x_178_, 2, v___x_176_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_168_, v_inst_169_, v_histogram_170_, v_val_172_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_201_; 
v_val_180_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_201_ == 0)
{
v___x_182_ = v___x_173_;
v_isShared_183_ = v_isSharedCheck_201_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v___x_173_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_201_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_leftCount_184_; lean_object* v_rightCount_185_; lean_object* v_rightIndex_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_199_; 
v_leftCount_184_ = lean_ctor_get(v_val_180_, 0);
v_rightCount_185_ = lean_ctor_get(v_val_180_, 2);
v_rightIndex_186_ = lean_ctor_get(v_val_180_, 3);
v_isSharedCheck_199_ = !lean_is_exclusive(v_val_180_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_val_180_, 1);
lean_dec(v_unused_200_);
v___x_188_ = v_val_180_;
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_rightIndex_186_);
lean_inc(v_rightCount_185_);
lean_inc(v_leftCount_184_);
lean_dec(v_val_180_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_leftCount_184_, v___x_190_);
lean_dec(v_leftCount_184_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v_index_171_);
v___x_193_ = v___x_182_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_index_171_);
v___x_193_ = v_reuseFailAlloc_198_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_193_);
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_195_ = v___x_188_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_rightCount_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_rightIndex_186_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_168_, v_inst_169_, v_histogram_170_, v_val_172_, v___x_195_);
return v___x_196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_lsize_205_, lean_object* v_rsize_206_, lean_object* v_histogram_207_, lean_object* v_index_208_, lean_object* v_val_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_203_, v_inst_204_, v_histogram_207_, v_index_208_, v_val_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___boxed(lean_object* v_00_u03b1_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_lsize_214_, lean_object* v_rsize_215_, lean_object* v_histogram_216_, lean_object* v_index_217_, lean_object* v_val_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Diff_Histogram_addLeft(v_00_u03b1_211_, v_inst_212_, v_inst_213_, v_lsize_214_, v_rsize_215_, v_histogram_216_, v_index_217_, v_val_218_);
lean_dec(v_rsize_215_);
lean_dec(v_lsize_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___redArg(lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_histogram_222_, lean_object* v_index_223_, lean_object* v_val_224_){
_start:
{
lean_object* v___x_225_; 
lean_inc(v_val_224_);
lean_inc_ref(v_inst_221_);
lean_inc_ref(v_inst_220_);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_220_, v_inst_221_, v_histogram_222_, v_val_224_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_box(0);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_index_223_);
v___x_230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_230_, 0, v___x_226_);
lean_ctor_set(v___x_230_, 1, v___x_227_);
lean_ctor_set(v___x_230_, 2, v___x_228_);
lean_ctor_set(v___x_230_, 3, v___x_229_);
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_220_, v_inst_221_, v_histogram_222_, v_val_224_, v___x_230_);
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_253_; 
v_val_232_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_253_ == 0)
{
v___x_234_ = v___x_225_;
v_isShared_235_ = v_isSharedCheck_253_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v___x_225_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_253_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_leftCount_236_; lean_object* v_leftIndex_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_250_; 
v_leftCount_236_ = lean_ctor_get(v_val_232_, 0);
v_leftIndex_237_ = lean_ctor_get(v_val_232_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_val_232_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; lean_object* v_unused_252_; 
v_unused_251_ = lean_ctor_get(v_val_232_, 3);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_val_232_, 2);
lean_dec(v_unused_252_);
v___x_239_ = v_val_232_;
v_isShared_240_ = v_isSharedCheck_250_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_leftIndex_237_);
lean_inc(v_leftCount_236_);
lean_dec(v_val_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_250_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_leftCount_236_, v___x_241_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_index_223_);
v___x_244_ = v___x_234_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_index_223_);
v___x_244_ = v_reuseFailAlloc_249_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 3, v___x_244_);
lean_ctor_set(v___x_239_, 2, v___x_242_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_leftCount_236_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_leftIndex_237_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v___x_244_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_220_, v_inst_221_, v_histogram_222_, v_val_224_, v___x_246_);
return v___x_247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_lsize_257_, lean_object* v_rsize_258_, lean_object* v_histogram_259_, lean_object* v_index_260_, lean_object* v_val_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_255_, v_inst_256_, v_histogram_259_, v_index_260_, v_val_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___boxed(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_lsize_266_, lean_object* v_rsize_267_, lean_object* v_histogram_268_, lean_object* v_index_269_, lean_object* v_val_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Diff_Histogram_addRight(v_00_u03b1_263_, v_inst_264_, v_inst_265_, v_lsize_266_, v_rsize_267_, v_histogram_268_, v_index_269_, v_val_270_);
lean_dec(v_rsize_267_);
lean_dec(v_lsize_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(lean_object* v_inst_272_, lean_object* v_left_273_, lean_object* v_right_274_, lean_object* v_pref_275_){
_start:
{
lean_object* v_start_276_; lean_object* v_stop_277_; lean_object* v_i_278_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_start_276_ = lean_ctor_get(v_left_273_, 1);
v_stop_277_ = lean_ctor_get(v_left_273_, 2);
v_i_278_ = lean_array_get_size(v_pref_275_);
v___x_284_ = lean_nat_sub(v_stop_277_, v_start_276_);
v___x_285_ = lean_nat_dec_lt(v_i_278_, v___x_284_);
lean_dec(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v_inst_272_);
goto v___jp_279_;
}
else
{
lean_object* v_start_286_; lean_object* v_stop_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_start_286_ = lean_ctor_get(v_right_274_, 1);
v_stop_287_ = lean_ctor_get(v_right_274_, 2);
v___x_288_ = lean_nat_sub(v_stop_287_, v_start_286_);
v___x_289_ = lean_nat_dec_lt(v_i_278_, v___x_288_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
lean_dec_ref(v_inst_272_);
goto v___jp_279_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_290_ = l_Subarray_get___redArg(v_left_273_, v_i_278_);
v___x_291_ = l_Subarray_get___redArg(v_right_274_, v_i_278_);
lean_inc_ref(v_inst_272_);
lean_inc(v___x_290_);
v___x_292_ = lean_apply_2(v_inst_272_, v___x_290_, v___x_291_);
v___x_293_ = lean_unbox(v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v___x_290_);
lean_dec_ref(v_inst_272_);
v___x_294_ = l_Subarray_drop___redArg(v_left_273_, v_i_278_);
v___x_295_ = l_Subarray_drop___redArg(v_right_274_, v_i_278_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_pref_275_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_array_push(v_pref_275_, v___x_290_);
v_pref_275_ = v___x_298_;
goto _start;
}
}
}
v___jp_279_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = l_Subarray_drop___redArg(v_left_273_, v_i_278_);
v___x_281_ = l_Subarray_drop___redArg(v_right_274_, v_i_278_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_pref_275_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_left_302_, lean_object* v_right_303_, lean_object* v_pref_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_301_, v_left_302_, v_right_303_, v_pref_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___redArg(lean_object* v_inst_308_, lean_object* v_left_309_, lean_object* v_right_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_312_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(v_inst_308_, v_left_309_, v_right_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix(lean_object* v_00_u03b1_313_, lean_object* v_inst_314_, lean_object* v_left_315_, lean_object* v_right_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Diff_matchPrefix___redArg(v_inst_314_, v_left_315_, v_right_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(lean_object* v_it_318_, lean_object* v_acc_319_, lean_object* v_recur_320_){
_start:
{
lean_object* v_array_321_; lean_object* v_start_322_; lean_object* v_stop_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_336_; 
v_array_321_ = lean_ctor_get(v_it_318_, 0);
v_start_322_ = lean_ctor_get(v_it_318_, 1);
v_stop_323_ = lean_ctor_get(v_it_318_, 2);
v_isSharedCheck_336_ = !lean_is_exclusive(v_it_318_);
if (v_isSharedCheck_336_ == 0)
{
v___x_325_ = v_it_318_;
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_stop_323_);
lean_inc(v_start_322_);
lean_inc(v_array_321_);
lean_dec(v_it_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_lt(v_start_322_, v_stop_323_);
if (v___x_327_ == 0)
{
lean_del_object(v___x_325_);
lean_dec(v_stop_323_);
lean_dec(v_start_322_);
lean_dec_ref(v_array_321_);
lean_dec_ref(v_recur_320_);
return v_acc_319_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_start_322_, v___x_328_);
lean_inc_ref(v_array_321_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_329_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_array_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_stop_323_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_array_fget(v_array_321_, v_start_322_);
lean_dec(v_start_322_);
lean_dec_ref(v_array_321_);
v___x_333_ = lean_array_push(v_acc_319_, v___x_332_);
v___x_334_ = lean_apply_3(v_recur_320_, v___x_331_, v___x_333_, lean_box(0));
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(lean_object* v_inst_338_, lean_object* v_left_339_, lean_object* v_right_340_, lean_object* v_i_341_){
_start:
{
lean_object* v_start_342_; lean_object* v_stop_343_; lean_object* v___f_344_; lean_object* v___x_345_; uint8_t v___x_359_; 
v_start_342_ = lean_ctor_get(v_left_339_, 1);
v_stop_343_ = lean_ctor_get(v_left_339_, 2);
v___f_344_ = ((lean_object*)(l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0));
v___x_345_ = lean_nat_sub(v_stop_343_, v_start_342_);
v___x_359_ = lean_nat_dec_lt(v_i_341_, v___x_345_);
if (v___x_359_ == 0)
{
lean_dec_ref(v_inst_338_);
goto v___jp_346_;
}
else
{
lean_object* v_start_360_; lean_object* v_stop_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_start_360_ = lean_ctor_get(v_right_340_, 1);
v_stop_361_ = lean_ctor_get(v_right_340_, 2);
v___x_362_ = lean_nat_sub(v_stop_361_, v_start_360_);
v___x_363_ = lean_nat_dec_lt(v_i_341_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v___x_362_);
lean_dec_ref(v_inst_338_);
goto v___jp_346_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_364_ = lean_nat_sub(v___x_345_, v_i_341_);
lean_dec(v___x_345_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_sub(v___x_364_, v___x_365_);
v___x_367_ = l_Subarray_get___redArg(v_left_339_, v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = lean_nat_sub(v___x_362_, v_i_341_);
lean_dec(v___x_362_);
v___x_369_ = lean_nat_sub(v___x_368_, v___x_365_);
v___x_370_ = l_Subarray_get___redArg(v_right_340_, v___x_369_);
lean_dec(v___x_369_);
lean_inc_ref(v_inst_338_);
v___x_371_ = lean_apply_2(v_inst_338_, v___x_367_, v___x_370_);
v___x_372_ = lean_unbox(v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_i_341_);
lean_dec_ref(v_inst_338_);
lean_inc_ref(v_left_339_);
v___x_373_ = l_Subarray_take___redArg(v_left_339_, v___x_364_);
v___x_374_ = l_Subarray_take___redArg(v_right_340_, v___x_368_);
lean_dec(v___x_368_);
v___x_375_ = l_Subarray_drop___redArg(v_left_339_, v___x_364_);
lean_dec(v___x_364_);
v___x_376_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_377_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_344_, v___x_375_, v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_374_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_373_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
lean_dec(v___x_368_);
lean_dec(v___x_364_);
v___x_380_ = lean_nat_add(v_i_341_, v___x_365_);
lean_dec(v_i_341_);
v_i_341_ = v___x_380_;
goto _start;
}
}
}
v___jp_346_:
{
lean_object* v_start_347_; lean_object* v_stop_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_start_347_ = lean_ctor_get(v_right_340_, 1);
v_stop_348_ = lean_ctor_get(v_right_340_, 2);
v___x_349_ = lean_nat_sub(v___x_345_, v_i_341_);
lean_dec(v___x_345_);
lean_inc_ref(v_left_339_);
v___x_350_ = l_Subarray_take___redArg(v_left_339_, v___x_349_);
v___x_351_ = lean_nat_sub(v_stop_348_, v_start_347_);
v___x_352_ = lean_nat_sub(v___x_351_, v_i_341_);
lean_dec(v_i_341_);
lean_dec(v___x_351_);
v___x_353_ = l_Subarray_take___redArg(v_right_340_, v___x_352_);
lean_dec(v___x_352_);
v___x_354_ = l_Subarray_drop___redArg(v_left_339_, v___x_349_);
lean_dec(v___x_349_);
v___x_355_ = ((lean_object*)(l_Lean_Diff_matchPrefix___redArg___closed__0));
v___x_356_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_344_, v___x_354_, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_350_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_left_384_, lean_object* v_right_385_, lean_object* v_i_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_383_, v_left_384_, v_right_385_, v_i_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___redArg(lean_object* v_inst_388_, lean_object* v_left_389_, lean_object* v_right_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(v_inst_388_, v_left_389_, v_right_390_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_left_395_, lean_object* v_right_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Diff_matchSuffix___redArg(v_inst_394_, v_left_395_, v_right_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0(lean_object* v___x_398_, lean_object* v_fst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_next_402_, lean_object* v_acc_403_, lean_object* v_h_404_, lean_object* v_G_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_lt(v_next_402_, v___x_398_);
if (v___x_406_ == 0)
{
lean_dec_ref(v_G_405_);
lean_dec(v_next_402_);
lean_dec_ref(v_inst_401_);
lean_dec_ref(v_inst_400_);
return v_acc_403_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = l_Subarray_get___redArg(v_fst_399_, v_next_402_);
lean_inc(v_next_402_);
v___x_408_ = l_Lean_Diff_Histogram_addLeft___redArg(v_inst_400_, v_inst_401_, v_acc_403_, v_next_402_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_next_402_, v___x_409_);
lean_dec(v_next_402_);
v___x_411_ = lean_apply_4(v_G_405_, v___x_410_, v___x_408_, lean_box(0), lean_box(0));
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__0___boxed(lean_object* v___x_412_, lean_object* v_fst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_next_416_, lean_object* v_acc_417_, lean_object* v_h_418_, lean_object* v_G_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Diff_lcs___redArg___lam__0(v___x_412_, v_fst_413_, v_inst_414_, v_inst_415_, v_next_416_, v_acc_417_, v_h_418_, v_G_419_);
lean_dec_ref(v_fst_413_);
lean_dec(v___x_412_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1(lean_object* v___x_421_, lean_object* v_fst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_next_425_, lean_object* v_acc_426_, lean_object* v_h_427_, lean_object* v_G_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_lt(v_next_425_, v___x_421_);
if (v___x_429_ == 0)
{
lean_dec_ref(v_G_428_);
lean_dec(v_next_425_);
lean_dec_ref(v_inst_424_);
lean_dec_ref(v_inst_423_);
return v_acc_426_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_430_ = l_Subarray_get___redArg(v_fst_422_, v_next_425_);
lean_inc(v_next_425_);
v___x_431_ = l_Lean_Diff_Histogram_addRight___redArg(v_inst_423_, v_inst_424_, v_acc_426_, v_next_425_, v___x_430_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_next_425_, v___x_432_);
lean_dec(v_next_425_);
v___x_434_ = lean_apply_4(v_G_428_, v___x_433_, v___x_431_, lean_box(0), lean_box(0));
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__1___boxed(lean_object* v___x_435_, lean_object* v_fst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_next_439_, lean_object* v_acc_440_, lean_object* v_h_441_, lean_object* v_G_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Diff_lcs___redArg___lam__1(v___x_435_, v_fst_436_, v_inst_437_, v_inst_438_, v_next_439_, v_acc_440_, v_h_441_, v_G_442_);
lean_dec_ref(v_fst_436_);
lean_dec(v___x_435_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__2(lean_object* v_a_444_, lean_object* v_x_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_snd_447_; lean_object* v_leftIndex_448_; 
v_snd_447_ = lean_ctor_get(v_a_444_, 1);
lean_inc(v_snd_447_);
v_leftIndex_448_ = lean_ctor_get(v_snd_447_, 1);
lean_inc(v_leftIndex_448_);
if (lean_obj_tag(v_leftIndex_448_) == 1)
{
lean_object* v_rightIndex_449_; 
v_rightIndex_449_ = lean_ctor_get(v_snd_447_, 3);
lean_inc(v_rightIndex_449_);
if (lean_obj_tag(v_rightIndex_449_) == 1)
{
if (lean_obj_tag(v___y_446_) == 0)
{
lean_object* v_fst_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_478_; 
v_fst_450_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_a_444_, 1);
lean_dec(v_unused_479_);
v___x_452_ = v_a_444_;
v_isShared_453_ = v_isSharedCheck_478_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_fst_450_);
lean_dec(v_a_444_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_478_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_leftCount_454_; lean_object* v_rightCount_455_; lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_477_; 
v_leftCount_454_ = lean_ctor_get(v_snd_447_, 0);
lean_inc(v_leftCount_454_);
v_rightCount_455_ = lean_ctor_get(v_snd_447_, 2);
lean_inc(v_rightCount_455_);
lean_dec(v_snd_447_);
v_val_456_ = lean_ctor_get(v_leftIndex_448_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_leftIndex_448_);
if (v_isSharedCheck_477_ == 0)
{
v___x_458_ = v_leftIndex_448_;
v_isShared_459_ = v_isSharedCheck_477_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v_leftIndex_448_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_477_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_476_; 
v_val_460_ = lean_ctor_get(v_rightIndex_449_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_rightIndex_449_);
if (v_isSharedCheck_476_ == 0)
{
v___x_462_ = v_rightIndex_449_;
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v_rightIndex_449_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_nat_add(v_leftCount_454_, v_rightCount_455_);
lean_dec(v_rightCount_455_);
lean_dec(v_leftCount_454_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v_val_460_);
lean_ctor_set(v___x_452_, 0, v_val_456_);
v___x_466_ = v___x_452_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_val_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_val_460_);
v___x_466_ = v_reuseFailAlloc_475_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_fst_450_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_464_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_468_);
v___x_470_ = v___x_462_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_474_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_470_);
v___x_472_ = v___x_458_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_480_; lean_object* v_fst_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_522_; 
v_val_480_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_val_480_);
v_fst_481_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_a_444_, 1);
lean_dec(v_unused_523_);
v___x_483_ = v_a_444_;
v_isShared_484_ = v_isSharedCheck_522_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_fst_481_);
lean_dec(v_a_444_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_522_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_leftCount_485_; lean_object* v_rightCount_486_; lean_object* v_val_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_521_; 
v_leftCount_485_ = lean_ctor_get(v_snd_447_, 0);
lean_inc(v_leftCount_485_);
v_rightCount_486_ = lean_ctor_get(v_snd_447_, 2);
lean_inc(v_rightCount_486_);
lean_dec(v_snd_447_);
v_val_487_ = lean_ctor_get(v_leftIndex_448_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_leftIndex_448_);
if (v_isSharedCheck_521_ == 0)
{
v___x_489_ = v_leftIndex_448_;
v_isShared_490_ = v_isSharedCheck_521_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_val_487_);
lean_dec(v_leftIndex_448_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_521_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_val_491_; lean_object* v_fst_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_519_; 
v_val_491_ = lean_ctor_get(v_rightIndex_449_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v_rightIndex_449_, 1);
v_fst_492_ = lean_ctor_get(v_val_480_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_val_480_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_val_480_, 1);
lean_dec(v_unused_520_);
v___x_494_ = v_val_480_;
v_isShared_495_ = v_isSharedCheck_519_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_fst_492_);
lean_dec(v_val_480_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_519_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_nat_add(v_leftCount_485_, v_rightCount_486_);
lean_dec(v_rightCount_486_);
lean_dec(v_leftCount_485_);
v___x_497_ = lean_nat_dec_lt(v___x_496_, v_fst_492_);
lean_dec(v_fst_492_);
if (v___x_497_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v___x_496_);
lean_del_object(v___x_494_);
lean_dec(v_val_491_);
lean_dec(v_val_487_);
lean_del_object(v___x_483_);
lean_dec(v_fst_481_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___y_446_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___y_446_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v___y_446_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___y_446_, 0);
lean_dec(v_unused_518_);
v___x_502_ = v___y_446_;
v_isShared_503_ = v_isSharedCheck_517_;
goto v_resetjp_501_;
}
else
{
lean_dec(v___y_446_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_517_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v_val_491_);
lean_ctor_set(v___x_494_, 0, v_val_487_);
v___x_505_ = v___x_494_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_val_487_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_val_491_);
v___x_505_ = v_reuseFailAlloc_516_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_505_);
v___x_507_ = v___x_483_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_481_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_515_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_496_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_508_);
v___x_510_ = v___x_502_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_510_);
v___x_512_ = v___x_489_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
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
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_rightIndex_449_);
lean_dec(v_snd_447_);
lean_dec_ref(v_a_444_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_leftIndex_448_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_leftIndex_448_, 0);
lean_dec(v_unused_531_);
v___x_525_ = v_leftIndex_448_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_leftIndex_448_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___y_446_);
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___y_446_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v___x_532_; 
lean_dec(v_leftIndex_448_);
lean_dec(v_snd_447_);
lean_dec_ref(v_a_444_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___y_446_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__3(lean_object* v_a_533_, lean_object* v_b_534_, lean_object* v_d_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_533_);
lean_ctor_set(v___x_536_, 1, v_b_534_);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_d_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg___lam__4(lean_object* v___x_538_, lean_object* v___f_539_, lean_object* v_l_540_, lean_object* v_acc_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_538_, v___f_539_, v_acc_541_, v_l_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__10(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_unsigned_to_nat(16u);
v___x_564_ = lean_mk_array(v___x_563_, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___redArg___closed__11(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_hist_567_; 
v___x_565_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__10, &l_Lean_Diff_lcs___redArg___closed__10_once, _init_l_Lean_Diff_lcs___redArg___closed__10);
v___x_566_ = lean_unsigned_to_nat(0u);
v_hist_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_567_, 0, v___x_566_);
lean_ctor_set(v_hist_567_, 1, v___x_565_);
return v_hist_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___redArg(lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_left_575_, lean_object* v_right_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_snd_579_; lean_object* v_fst_580_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; lean_object* v_snd_584_; lean_object* v_fst_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; lean_object* v_start_588_; lean_object* v_stop_589_; lean_object* v_start_590_; lean_object* v_stop_591_; lean_object* v___x_592_; lean_object* v_hist_593_; lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v_buckets_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___y_604_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_577_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
lean_inc_ref_n(v_inst_573_, 4);
v___x_578_ = l_Lean_Diff_matchPrefix___redArg(v_inst_573_, v_left_575_, v_right_576_);
v_snd_579_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_snd_579_);
v_fst_580_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_fst_580_);
lean_dec_ref(v___x_578_);
v_fst_581_ = lean_ctor_get(v_snd_579_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v_snd_579_, 1);
lean_inc(v_snd_582_);
lean_dec(v_snd_579_);
v___x_583_ = l_Lean_Diff_matchSuffix___redArg(v_inst_573_, v_fst_581_, v_snd_582_);
v_snd_584_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_584_);
v_fst_585_ = lean_ctor_get(v___x_583_, 0);
lean_inc_n(v_fst_585_, 2);
lean_dec_ref(v___x_583_);
v_fst_586_ = lean_ctor_get(v_snd_584_, 0);
lean_inc_n(v_fst_586_, 2);
v_snd_587_ = lean_ctor_get(v_snd_584_, 1);
lean_inc(v_snd_587_);
lean_dec(v_snd_584_);
v_start_588_ = lean_ctor_get(v_fst_585_, 1);
v_stop_589_ = lean_ctor_get(v_fst_585_, 2);
v_start_590_ = lean_ctor_get(v_fst_586_, 1);
v_stop_591_ = lean_ctor_get(v_fst_586_, 2);
v___x_592_ = lean_unsigned_to_nat(0u);
v_hist_593_ = lean_obj_once(&l_Lean_Diff_lcs___redArg___closed__11, &l_Lean_Diff_lcs___redArg___closed__11_once, _init_l_Lean_Diff_lcs___redArg___closed__11);
v___x_594_ = lean_nat_sub(v_stop_589_, v_start_588_);
lean_inc_ref_n(v_inst_574_, 2);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_595_, 0, v___x_594_);
lean_closure_set(v___f_595_, 1, v_fst_585_);
lean_closure_set(v___f_595_, 2, v_inst_573_);
lean_closure_set(v___f_595_, 3, v_inst_574_);
v___x_596_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_595_, v___x_592_, v_hist_593_, lean_box(0));
v___x_597_ = lean_nat_sub(v_stop_591_, v_start_590_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Diff_lcs___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_598_, 0, v___x_597_);
lean_closure_set(v___f_598_, 1, v_fst_586_);
lean_closure_set(v___f_598_, 2, v_inst_573_);
lean_closure_set(v___f_598_, 3, v_inst_574_);
v___x_599_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_598_, v___x_592_, v___x_596_, lean_box(0));
v_buckets_600_ = lean_ctor_get(v___x_599_, 1);
lean_inc_ref(v_buckets_600_);
lean_dec(v___x_599_);
v___f_601_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__12));
v___x_602_ = lean_box(0);
v___x_630_ = lean_box(0);
v___x_631_ = lean_array_get_size(v_buckets_600_);
v___x_632_ = lean_nat_dec_lt(v___x_592_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec_ref(v_buckets_600_);
v___y_604_ = v___x_630_;
goto v___jp_603_;
}
else
{
lean_object* v___f_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
v___f_633_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__14));
v___x_634_ = lean_usize_of_nat(v___x_631_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_577_, v___f_633_, v_buckets_600_, v___x_634_, v___x_635_, v___x_630_);
v___y_604_ = v___x_636_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_List_forIn_x27_loop___redArg(v___x_577_, v___f_601_, v___y_604_, v___x_602_);
lean_dec(v___y_604_);
if (lean_obj_tag(v___x_605_) == 1)
{
lean_object* v_val_606_; lean_object* v_snd_607_; lean_object* v_snd_608_; lean_object* v_fst_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_615_; lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_605_, 1);
v_snd_607_ = lean_ctor_get(v_val_606_, 1);
lean_inc(v_snd_607_);
lean_dec(v_val_606_);
v_snd_608_ = lean_ctor_get(v_snd_607_, 1);
lean_inc(v_snd_608_);
v_fst_609_ = lean_ctor_get(v_snd_607_, 0);
lean_inc(v_fst_609_);
lean_dec(v_snd_607_);
v_fst_610_ = lean_ctor_get(v_snd_608_, 0);
lean_inc(v_fst_610_);
v_snd_611_ = lean_ctor_get(v_snd_608_, 1);
lean_inc(v_snd_611_);
lean_dec(v_snd_608_);
v___x_612_ = l_Subarray_split___redArg(v_fst_585_, v_fst_610_);
lean_dec(v_fst_610_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_fst_613_);
v_snd_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_snd_614_);
lean_dec_ref(v___x_612_);
v___x_615_ = l_Subarray_split___redArg(v_fst_586_, v_snd_611_);
lean_dec(v_snd_611_);
v_fst_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_fst_616_);
v_snd_617_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_snd_617_);
lean_dec_ref(v___x_615_);
lean_inc_ref(v_inst_574_);
lean_inc_ref(v_inst_573_);
v___x_618_ = l_Lean_Diff_lcs___redArg(v_inst_573_, v_inst_574_, v_fst_613_, v_fst_616_);
v___x_619_ = l_Array_append___redArg(v_fst_580_, v___x_618_);
lean_dec_ref(v___x_618_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_mk_empty_array_with_capacity(v___x_620_);
v___x_622_ = lean_array_push(v___x_621_, v_fst_609_);
v___x_623_ = l_Array_append___redArg(v___x_619_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = l_Subarray_drop___redArg(v_snd_614_, v___x_620_);
v___x_625_ = l_Subarray_drop___redArg(v_snd_617_, v___x_620_);
v___x_626_ = l_Lean_Diff_lcs___redArg(v_inst_573_, v_inst_574_, v___x_624_, v___x_625_);
v___x_627_ = l_Array_append___redArg(v___x_623_, v___x_626_);
lean_dec_ref(v___x_626_);
v___x_628_ = l_Array_append___redArg(v___x_627_, v_snd_587_);
lean_dec(v_snd_587_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
lean_dec(v___x_605_);
lean_dec(v_fst_586_);
lean_dec(v_fst_585_);
lean_dec_ref(v_inst_574_);
lean_dec_ref(v_inst_573_);
v___x_629_ = l_Array_append___redArg(v_fst_580_, v_snd_587_);
lean_dec(v_snd_587_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs(lean_object* v_00_u03b1_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_left_640_, lean_object* v_right_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Diff_lcs___redArg(v_inst_638_, v_inst_639_, v_left_640_, v_right_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__0(lean_object* v_x_643_){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = 0;
v___x_645_ = lean_box(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_x_643_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__1(lean_object* v_x_647_){
_start:
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = 1;
v___x_649_ = lean_box(v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_x_647_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2(lean_object* v_inst_651_, lean_object* v_original_652_, lean_object* v___x_653_, lean_object* v_inst_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_682_; 
v_fst_657_ = lean_ctor_get(v_b_656_, 0);
v_snd_658_ = lean_ctor_get(v_b_656_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_b_656_);
if (v_isSharedCheck_682_ == 0)
{
v___x_660_ = v_b_656_;
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v_b_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
uint8_t v___y_668_; uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_lt(v_snd_658_, v___x_653_);
if (v___x_678_ == 0)
{
lean_dec(v_a_655_);
lean_dec_ref(v_inst_654_);
v___y_668_ = v___x_678_;
goto v___jp_667_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = lean_array_get_borrowed(v_inst_651_, v_original_652_, v_snd_658_);
lean_inc(v___x_679_);
v___x_680_ = lean_apply_2(v_inst_654_, v___x_679_, v_a_655_);
v___x_681_ = lean_unbox(v___x_680_);
if (v___x_681_ == 0)
{
v___y_668_ = v___x_678_;
goto v___jp_667_;
}
else
{
goto v___jp_662_;
}
}
v___jp_662_:
{
lean_object* v___x_664_; 
if (v_isShared_661_ == 0)
{
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_fst_657_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_snd_658_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
goto v___jp_662_;
}
else
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_del_object(v___x_660_);
v___x_669_ = 1;
v___x_670_ = lean_array_get_borrowed(v_inst_651_, v_original_652_, v_snd_658_);
v___x_671_ = lean_box(v___x_669_);
lean_inc(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
v___x_673_ = lean_array_push(v_fst_657_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_snd_658_, v___x_674_);
lean_dec(v_snd_658_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__2___boxed(lean_object* v_inst_683_, lean_object* v_original_684_, lean_object* v___x_685_, lean_object* v_inst_686_, lean_object* v_a_687_, lean_object* v_b_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Diff_diff___redArg___lam__2(v_inst_683_, v_original_684_, v___x_685_, v_inst_686_, v_a_687_, v_b_688_);
lean_dec(v___x_685_);
lean_dec_ref(v_original_684_);
lean_dec(v_inst_683_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3(lean_object* v_inst_690_, lean_object* v_edited_691_, lean_object* v___x_692_, lean_object* v_inst_693_, lean_object* v_a_694_, lean_object* v_b_695_){
_start:
{
lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_721_; 
v_fst_696_ = lean_ctor_get(v_b_695_, 0);
v_snd_697_ = lean_ctor_get(v_b_695_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_b_695_);
if (v_isSharedCheck_721_ == 0)
{
v___x_699_ = v_b_695_;
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snd_697_);
lean_inc(v_fst_696_);
lean_dec(v_b_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint8_t v___y_707_; uint8_t v___x_717_; 
v___x_717_ = lean_nat_dec_lt(v_snd_697_, v___x_692_);
if (v___x_717_ == 0)
{
lean_dec(v_a_694_);
lean_dec_ref(v_inst_693_);
v___y_707_ = v___x_717_;
goto v___jp_706_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_array_get_borrowed(v_inst_690_, v_edited_691_, v_snd_697_);
lean_inc(v___x_718_);
v___x_719_ = lean_apply_2(v_inst_693_, v___x_718_, v_a_694_);
v___x_720_ = lean_unbox(v___x_719_);
if (v___x_720_ == 0)
{
v___y_707_ = v___x_717_;
goto v___jp_706_;
}
else
{
goto v___jp_701_;
}
}
v___jp_701_:
{
lean_object* v___x_703_; 
if (v_isShared_700_ == 0)
{
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fst_696_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_snd_697_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
v___jp_706_:
{
if (v___y_707_ == 0)
{
goto v___jp_701_;
}
else
{
uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_del_object(v___x_699_);
v___x_708_ = 0;
v___x_709_ = lean_array_get_borrowed(v_inst_690_, v_edited_691_, v_snd_697_);
v___x_710_ = lean_box(v___x_708_);
lean_inc(v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
v___x_712_ = lean_array_push(v_fst_696_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_nat_add(v_snd_697_, v___x_713_);
lean_dec(v_snd_697_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__3___boxed(lean_object* v_inst_722_, lean_object* v_edited_723_, lean_object* v___x_724_, lean_object* v_inst_725_, lean_object* v_a_726_, lean_object* v_b_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Diff_diff___redArg___lam__3(v_inst_722_, v_edited_723_, v___x_724_, v_inst_725_, v_a_726_, v_b_727_);
lean_dec(v___x_724_);
lean_dec_ref(v_edited_723_);
lean_dec(v_inst_722_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___redArg___lam__4(lean_object* v_inst_729_, lean_object* v_original_730_, lean_object* v___x_731_, lean_object* v_inst_732_, lean_object* v___x_733_, lean_object* v_edited_734_, lean_object* v___x_735_, lean_object* v_a_736_, lean_object* v_x_737_, lean_object* v___y_738_){
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
lean_inc(v_inst_729_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_749_, 0, v_inst_729_);
lean_closure_set(v___f_749_, 1, v_original_730_);
lean_closure_set(v___f_749_, 2, v___x_731_);
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
lean_closure_set(v___f_758_, 0, v_inst_729_);
lean_closure_set(v___f_758_, 1, v_edited_734_);
lean_closure_set(v___f_758_, 2, v___x_735_);
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
lean_object* v_i_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_i_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_original_857_);
v___x_861_ = lean_nat_dec_lt(v_i_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___f_862_; lean_object* v___x_863_; size_t v_sz_864_; size_t v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_original_857_);
lean_dec(v_inst_856_);
lean_dec_ref(v_inst_855_);
lean_dec_ref(v_inst_854_);
v___f_862_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__0));
v___x_863_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_sz_864_ = lean_array_size(v_edited_858_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_863_, v___f_862_, v_sz_864_, v___x_865_, v_edited_858_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_array_get_size(v_edited_858_);
v___x_868_ = lean_nat_dec_lt(v_i_859_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___f_869_; lean_object* v___x_870_; size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_edited_858_);
lean_dec(v_inst_856_);
lean_dec_ref(v_inst_855_);
lean_dec_ref(v_inst_854_);
v___f_869_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__1));
v___x_870_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_sz_871_ = lean_array_size(v_original_857_);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_870_, v___f_869_, v_sz_871_, v___x_872_, v_original_857_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_ds_876_; lean_object* v___x_877_; lean_object* v___f_878_; lean_object* v___x_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v_snd_883_; lean_object* v_fst_884_; lean_object* v_fst_885_; lean_object* v_snd_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_907_; 
lean_inc_ref_n(v_original_857_, 2);
v___x_874_ = l_Array_toSubarray___redArg(v_original_857_, v_i_859_, v___x_860_);
lean_inc_ref_n(v_edited_858_, 2);
v___x_875_ = l_Array_toSubarray___redArg(v_edited_858_, v_i_859_, v___x_867_);
lean_inc_ref(v_inst_854_);
v_ds_876_ = l_Lean_Diff_lcs___redArg(v_inst_854_, v_inst_855_, v___x_874_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v___f_878_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__4), 10, 7);
lean_closure_set(v___f_878_, 0, v_inst_856_);
lean_closure_set(v___f_878_, 1, v_original_857_);
lean_closure_set(v___f_878_, 2, v___x_860_);
lean_closure_set(v___f_878_, 3, v_inst_854_);
lean_closure_set(v___f_878_, 4, v___x_877_);
lean_closure_set(v___f_878_, 5, v_edited_858_);
lean_closure_set(v___f_878_, 6, v___x_867_);
v___x_879_ = ((lean_object*)(l_Lean_Diff_diff___redArg___closed__4));
v_sz_880_ = lean_array_size(v_ds_876_);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_877_, v_ds_876_, v___f_878_, v_sz_880_, v___x_881_, v___x_879_);
v_snd_883_ = lean_ctor_get(v___x_882_, 1);
lean_inc(v_snd_883_);
v_fst_884_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_fst_884_);
lean_dec(v___x_882_);
v_fst_885_ = lean_ctor_get(v_snd_883_, 0);
v_snd_886_ = lean_ctor_get(v_snd_883_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_snd_883_);
if (v_isSharedCheck_907_ == 0)
{
v___x_888_ = v_snd_883_;
v_isShared_889_ = v_isSharedCheck_907_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_snd_886_);
lean_inc(v_fst_885_);
lean_dec(v_snd_883_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_907_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___f_890_; lean_object* v___x_892_; 
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_890_, 0, v___x_860_);
lean_closure_set(v___f_890_, 1, v_original_857_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_fst_885_);
lean_ctor_set(v___x_888_, 0, v_fst_884_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fst_884_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_fst_885_);
v___x_892_ = v_reuseFailAlloc_906_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v_fst_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v___x_893_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_877_, v___f_890_, v___x_892_);
v_fst_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_893_, 1);
lean_dec(v_unused_905_);
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_fst_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___f_898_; lean_object* v___x_900_; 
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Diff_diff___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_898_, 0, v___x_867_);
lean_closure_set(v___f_898_, 1, v_edited_858_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v_snd_886_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_fst_894_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_snd_886_);
v___x_900_ = v_reuseFailAlloc_903_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v_fst_902_; 
v___x_901_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_877_, v___f_898_, v___x_900_);
v_fst_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_fst_902_);
lean_dec(v___x_901_);
return v_fst_902_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_original_912_, lean_object* v_edited_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Diff_diff___redArg(v_inst_909_, v_inst_910_, v_inst_911_, v_original_912_, v_edited_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0(lean_object* v_inst_916_, lean_object* v_out_917_, lean_object* v_a_918_, lean_object* v_x_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_fst_921_ = lean_ctor_get(v_a_918_, 0);
lean_inc(v_fst_921_);
v_snd_922_ = lean_ctor_get(v_a_918_, 1);
lean_inc(v_snd_922_);
lean_dec_ref(v_a_918_);
v___x_923_ = lean_apply_1(v_inst_916_, v_snd_922_);
v___x_924_ = lean_string_dec_eq(v___x_923_, v_out_917_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_925_ = lean_unbox(v_fst_921_);
lean_dec(v_fst_921_);
v___x_926_ = l_Lean_Diff_Action_linePrefix(v___x_925_);
v___x_927_ = ((lean_object*)(l_Lean_Diff_Action_linePrefix___closed__2));
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
v___x_929_ = lean_string_append(v___x_928_, v___x_923_);
lean_dec_ref(v___x_923_);
v___x_930_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_931_ = lean_string_append(v___x_929_, v___x_930_);
v___x_932_ = lean_string_append(v___y_920_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
else
{
uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v___x_923_);
v___x_934_ = lean_unbox(v_fst_921_);
lean_dec(v_fst_921_);
v___x_935_ = l_Lean_Diff_Action_linePrefix(v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___lam__0___closed__0));
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
v___x_938_ = lean_string_append(v___y_920_, v___x_937_);
lean_dec_ref(v___x_937_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg___lam__0___boxed(lean_object* v_inst_940_, lean_object* v_out_941_, lean_object* v_a_942_, lean_object* v_x_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Diff_linesToString___redArg___lam__0(v_inst_940_, v_out_941_, v_a_942_, v_x_943_, v___y_944_);
lean_dec_ref(v_out_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___redArg(lean_object* v_inst_947_, lean_object* v_lines_948_){
_start:
{
lean_object* v___x_949_; lean_object* v_out_950_; lean_object* v___f_951_; size_t v_sz_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_949_ = ((lean_object*)(l_Lean_Diff_lcs___redArg___closed__9));
v_out_950_ = ((lean_object*)(l_Lean_Diff_linesToString___redArg___closed__0));
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Diff_linesToString___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_951_, 0, v_inst_947_);
lean_closure_set(v___f_951_, 1, v_out_950_);
v_sz_952_ = lean_array_size(v_lines_948_);
v___x_953_ = ((size_t)0ULL);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_949_, v_lines_948_, v___f_951_, v_sz_952_, v___x_953_, v_out_950_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_lines_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Diff_linesToString___redArg(v_inst_956_, v_lines_957_);
return v___x_958_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Diff(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
