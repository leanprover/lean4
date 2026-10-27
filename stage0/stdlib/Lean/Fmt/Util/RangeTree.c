// Lean compiler output
// Module: Lean.Fmt.Util.RangeTree
// Imports: public import Lean.Syntax public import Init.While public import Init.Data.Array.QSort.Basic
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Fmt.Util.RangeTree"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Fmt.binSearchRightmost"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Fmt.binSearchLeftmost"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedRangeTree_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedRangeTree_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "roots"};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_compareRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_compareRanges___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11_value)} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2));
v___x_8_ = lean_unsigned_to_nat(8u);
v___x_9_ = lean_unsigned_to_nat(31u);
v___x_10_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1));
v___x_11_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0));
v___x_12_ = l_mkPanicMessageWithDecl(v___x_11_, v___x_10_, v___x_9_, v___x_8_, v___x_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(lean_object* v_xs_13_, lean_object* v_key_14_, lean_object* v_lt_15_, lean_object* v_query_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_54_; 
v_fst_18_ = lean_ctor_get(v_a_17_, 0);
v_snd_19_ = lean_ctor_get(v_a_17_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_17_);
if (v_isSharedCheck_54_ == 0)
{
v___x_21_ = v_a_17_;
v_isShared_22_ = v_isSharedCheck_54_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snd_19_);
lean_inc(v_fst_18_);
lean_dec(v_a_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_54_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_lt(v_fst_18_, v_snd_19_);
if (v___x_23_ == 0)
{
lean_object* v___x_25_; 
lean_dec(v_query_16_);
lean_dec_ref(v_lt_15_);
lean_dec(v_key_14_);
if (v_isShared_22_ == 0)
{
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_fst_18_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_snd_19_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_28_ = lean_nat_sub(v_snd_19_, v_fst_18_);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_shiftr(v___x_28_, v___x_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_nat_add(v_fst_18_, v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_array_get_size(v_xs_13_);
v___x_33_ = lean_nat_dec_lt(v___x_31_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v___x_31_);
v___x_34_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3);
v___x_35_ = l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(v___x_34_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_36_; 
lean_del_object(v___x_21_);
lean_dec(v_snd_19_);
lean_dec(v_fst_18_);
lean_dec(v_query_16_);
lean_dec_ref(v_lt_15_);
lean_dec(v_key_14_);
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v___x_38_; 
lean_dec_ref_known(v___x_35_, 1);
if (v_isShared_22_ == 0)
{
v___x_38_ = v___x_21_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_fst_18_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_snd_19_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
v_a_17_ = v___x_38_;
goto _start;
}
}
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = lean_array_fget_borrowed(v_xs_13_, v___x_31_);
lean_inc(v_key_14_);
lean_inc(v___x_41_);
v___x_42_ = lean_apply_1(v_key_14_, v___x_41_);
lean_inc_ref(v_lt_15_);
lean_inc(v_query_16_);
v___x_43_ = lean_apply_2(v_lt_15_, v_query_16_, v___x_42_);
v___x_44_ = lean_unbox(v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_47_; 
lean_dec(v_fst_18_);
v___x_45_ = lean_nat_add(v___x_31_, v___x_29_);
lean_dec(v___x_31_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_45_);
v___x_47_ = v___x_21_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_snd_19_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
v_a_17_ = v___x_47_;
goto _start;
}
}
else
{
lean_object* v___x_51_; 
lean_dec(v_snd_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v___x_31_);
v___x_51_ = v___x_21_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_fst_18_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_31_);
v___x_51_ = v_reuseFailAlloc_53_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_a_17_ = v___x_51_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___boxed(lean_object* v_xs_55_, lean_object* v_key_56_, lean_object* v_lt_57_, lean_object* v_query_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(v_xs_55_, v_key_56_, v_lt_57_, v_query_58_, v_a_59_);
lean_dec_ref(v_xs_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object* v_xs_61_, lean_object* v_query_62_, lean_object* v_key_63_, lean_object* v_lt_64_){
_start:
{
lean_object* v_l_65_; lean_object* v_r_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_l_65_ = lean_unsigned_to_nat(0u);
v_r_66_ = lean_array_get_size(v_xs_61_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_l_65_);
lean_ctor_set(v___x_67_, 1, v_r_66_);
lean_inc(v_query_62_);
lean_inc_ref(v_lt_64_);
lean_inc(v_key_63_);
v___x_68_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(v_xs_61_, v_key_63_, v_lt_64_, v_query_62_, v___x_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v___x_69_; 
lean_dec_ref(v_lt_64_);
lean_dec(v_key_63_);
lean_dec(v_query_62_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_95_; 
v_val_70_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_95_ == 0)
{
v___x_72_ = v___x_68_;
v_isShared_73_ = v_isSharedCheck_95_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_val_70_);
lean_dec(v___x_68_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_95_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_snd_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_93_; 
v_snd_74_ = lean_ctor_get(v_val_70_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_val_70_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_val_70_, 0);
lean_dec(v_unused_94_);
v___x_76_ = v_val_70_;
v_isShared_77_ = v_isSharedCheck_93_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snd_74_);
lean_dec(v_val_70_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_93_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_sub(v_snd_74_, v___x_78_);
lean_dec(v_snd_74_);
v___x_80_ = lean_nat_dec_lt(v___x_79_, v_r_66_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec(v___x_79_);
lean_del_object(v___x_76_);
lean_del_object(v___x_72_);
lean_dec_ref(v_lt_64_);
lean_dec(v_key_63_);
lean_dec(v_query_62_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_82_ = lean_array_fget_borrowed(v_xs_61_, v___x_79_);
lean_inc(v___x_82_);
v___x_83_ = lean_apply_1(v_key_63_, v___x_82_);
v___x_84_ = lean_apply_2(v_lt_64_, v_query_62_, v___x_83_);
v___x_85_ = lean_unbox(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_87_; 
lean_inc(v___x_82_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_82_);
lean_ctor_set(v___x_76_, 0, v___x_79_);
v___x_87_ = v___x_76_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_82_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_89_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_87_);
v___x_89_ = v___x_72_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v___x_79_);
lean_del_object(v___x_76_);
lean_del_object(v___x_72_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg___boxed(lean_object* v_xs_96_, lean_object* v_query_97_, lean_object* v_key_98_, lean_object* v_lt_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Fmt_binSearchRightmost___redArg(v_xs_96_, v_query_97_, v_key_98_, v_lt_99_);
lean_dec_ref(v_xs_96_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_xs_103_, lean_object* v_query_104_, lean_object* v_key_105_, lean_object* v_lt_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Fmt_binSearchRightmost___redArg(v_xs_103_, v_query_104_, v_key_105_, v_lt_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___boxed(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_xs_110_, lean_object* v_query_111_, lean_object* v_key_112_, lean_object* v_lt_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Fmt_binSearchRightmost(v_00_u03b1_108_, v_00_u03b2_109_, v_xs_110_, v_query_111_, v_key_112_, v_lt_113_);
lean_dec_ref(v_xs_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1(lean_object* v_00_u03b1_115_, lean_object* v_xs_116_, lean_object* v_00_u03b2_117_, lean_object* v_key_118_, lean_object* v_lt_119_, lean_object* v_query_120_, lean_object* v_inst_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(v_xs_116_, v_key_118_, v_lt_119_, v_query_120_, v_a_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___boxed(lean_object* v_00_u03b1_124_, lean_object* v_xs_125_, lean_object* v_00_u03b2_126_, lean_object* v_key_127_, lean_object* v_lt_128_, lean_object* v_query_129_, lean_object* v_inst_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1(v_00_u03b1_124_, v_xs_125_, v_00_u03b2_126_, v_key_127_, v_lt_128_, v_query_129_, v_inst_130_, v_a_131_);
lean_dec_ref(v_xs_125_);
return v_res_132_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_134_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2));
v___x_135_ = lean_unsigned_to_nat(8u);
v___x_136_ = lean_unsigned_to_nat(56u);
v___x_137_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0));
v___x_138_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0));
v___x_139_ = l_mkPanicMessageWithDecl(v___x_138_, v___x_137_, v___x_136_, v___x_135_, v___x_134_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(lean_object* v_xs_140_, lean_object* v_key_141_, lean_object* v_lt_142_, lean_object* v_query_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_fst_145_; lean_object* v_snd_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_181_; 
v_fst_145_ = lean_ctor_get(v_a_144_, 0);
v_snd_146_ = lean_ctor_get(v_a_144_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_144_);
if (v_isSharedCheck_181_ == 0)
{
v___x_148_ = v_a_144_;
v_isShared_149_ = v_isSharedCheck_181_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snd_146_);
lean_inc(v_fst_145_);
lean_dec(v_a_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_181_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_lt(v_fst_145_, v_snd_146_);
if (v___x_150_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_query_143_);
lean_dec_ref(v_lt_142_);
lean_dec(v_key_141_);
if (v_isShared_149_ == 0)
{
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_snd_146_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_155_ = lean_nat_sub(v_snd_146_, v_fst_145_);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_shiftr(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_nat_add(v_fst_145_, v___x_157_);
lean_dec(v___x_157_);
v___x_159_ = lean_array_get_size(v_xs_140_);
v___x_160_ = lean_nat_dec_lt(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_158_);
v___x_161_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1);
v___x_162_ = l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(v___x_161_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_163_; 
lean_del_object(v___x_148_);
lean_dec(v_snd_146_);
lean_dec(v_fst_145_);
lean_dec(v_query_143_);
lean_dec_ref(v_lt_142_);
lean_dec(v_key_141_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_165_; 
lean_dec_ref_known(v___x_162_, 1);
if (v_isShared_149_ == 0)
{
v___x_165_ = v___x_148_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_snd_146_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v_a_144_ = v___x_165_;
goto _start;
}
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_168_ = lean_array_fget_borrowed(v_xs_140_, v___x_158_);
lean_inc(v_key_141_);
lean_inc(v___x_168_);
v___x_169_ = lean_apply_1(v_key_141_, v___x_168_);
lean_inc_ref(v_lt_142_);
lean_inc(v_query_143_);
v___x_170_ = lean_apply_2(v_lt_142_, v___x_169_, v_query_143_);
v___x_171_ = lean_unbox(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_173_; 
lean_dec(v_snd_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_158_);
v___x_173_ = v___x_148_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_158_);
v___x_173_ = v_reuseFailAlloc_175_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
v_a_144_ = v___x_173_;
goto _start;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_178_; 
lean_dec(v_fst_145_);
v___x_176_ = lean_nat_add(v___x_158_, v___x_156_);
lean_dec(v___x_158_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_176_);
v___x_178_ = v___x_148_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_snd_146_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v_a_144_ = v___x_178_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___boxed(lean_object* v_xs_182_, lean_object* v_key_183_, lean_object* v_lt_184_, lean_object* v_query_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(v_xs_182_, v_key_183_, v_lt_184_, v_query_185_, v_a_186_);
lean_dec_ref(v_xs_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg(lean_object* v_xs_188_, lean_object* v_query_189_, lean_object* v_key_190_, lean_object* v_lt_191_){
_start:
{
lean_object* v_l_192_; lean_object* v_r_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_l_192_ = lean_unsigned_to_nat(0u);
v_r_193_ = lean_array_get_size(v_xs_188_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v_l_192_);
lean_ctor_set(v___x_194_, 1, v_r_193_);
lean_inc(v_query_189_);
lean_inc_ref(v_lt_191_);
lean_inc(v_key_190_);
v___x_195_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(v_xs_188_, v_key_190_, v_lt_191_, v_query_189_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v___x_196_; 
lean_dec_ref(v_lt_191_);
lean_dec(v_key_190_);
lean_dec(v_query_189_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v_val_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_220_; 
v_val_197_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_220_ == 0)
{
v___x_199_ = v___x_195_;
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_val_197_);
lean_dec(v___x_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_fst_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_218_; 
v_fst_201_ = lean_ctor_get(v_val_197_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_val_197_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_val_197_, 1);
lean_dec(v_unused_219_);
v___x_203_ = v_val_197_;
v_isShared_204_ = v_isSharedCheck_218_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_fst_201_);
lean_dec(v_val_197_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_218_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_lt(v_fst_201_, v_r_193_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_del_object(v___x_203_);
lean_dec(v_fst_201_);
lean_del_object(v___x_199_);
lean_dec_ref(v_lt_191_);
lean_dec(v_key_190_);
lean_dec(v_query_189_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_207_ = lean_array_fget_borrowed(v_xs_188_, v_fst_201_);
lean_inc(v___x_207_);
v___x_208_ = lean_apply_1(v_key_190_, v___x_207_);
v___x_209_ = lean_apply_2(v_lt_191_, v___x_208_, v_query_189_);
v___x_210_ = lean_unbox(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_212_; 
lean_inc(v___x_207_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_207_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_fst_201_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_207_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_212_);
v___x_214_ = v___x_199_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v___x_217_; 
lean_del_object(v___x_203_);
lean_dec(v_fst_201_);
lean_del_object(v___x_199_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg___boxed(lean_object* v_xs_221_, lean_object* v_query_222_, lean_object* v_key_223_, lean_object* v_lt_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Fmt_binSearchLeftmost___redArg(v_xs_221_, v_query_222_, v_key_223_, v_lt_224_);
lean_dec_ref(v_xs_221_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_xs_228_, lean_object* v_query_229_, lean_object* v_key_230_, lean_object* v_lt_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Fmt_binSearchLeftmost___redArg(v_xs_228_, v_query_229_, v_key_230_, v_lt_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___boxed(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_xs_235_, lean_object* v_query_236_, lean_object* v_key_237_, lean_object* v_lt_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Fmt_binSearchLeftmost(v_00_u03b1_233_, v_00_u03b2_234_, v_xs_235_, v_query_236_, v_key_237_, v_lt_238_);
lean_dec_ref(v_xs_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0(lean_object* v_00_u03b1_240_, lean_object* v_xs_241_, lean_object* v_00_u03b2_242_, lean_object* v_key_243_, lean_object* v_lt_244_, lean_object* v_query_245_, lean_object* v_inst_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(v_xs_241_, v_key_243_, v_lt_244_, v_query_245_, v_a_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___boxed(lean_object* v_00_u03b1_249_, lean_object* v_xs_250_, lean_object* v_00_u03b2_251_, lean_object* v_key_252_, lean_object* v_lt_253_, lean_object* v_query_254_, lean_object* v_inst_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0(v_00_u03b1_249_, v_xs_250_, v_00_u03b2_251_, v_key_252_, v_lt_253_, v_query_254_, v_inst_255_, v_a_256_);
lean_dec_ref(v_xs_250_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(lean_object* v_inst_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_262_ = ((lean_object*)(l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0));
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v_inst_260_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default(lean_object* v_00_u03b1_264_, lean_object* v_inst_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(v_inst_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode___redArg(lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(v_inst_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode(lean_object* v_a_269_, lean_object* v_inst_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(v_inst_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(9u);
v___x_286_ = lean_nat_to_int(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(12u);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0));
v___x_300_ = lean_string_length(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___boxed(lean_object* v_inst_307_, lean_object* v_x_308_, lean_object* v_prec_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(v_inst_307_, v_x_308_, v_prec_309_);
lean_dec(v_prec_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(lean_object* v_inst_311_, lean_object* v_x_312_, lean_object* v_prec_313_){
_start:
{
lean_object* v_range_314_; lean_object* v_value_315_; lean_object* v_children_316_; lean_object* v_localinst_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_range_314_ = lean_ctor_get(v_x_312_, 0);
lean_inc_ref(v_range_314_);
v_value_315_ = lean_ctor_get(v_x_312_, 1);
lean_inc(v_value_315_);
v_children_316_ = lean_ctor_get(v_x_312_, 2);
lean_inc_ref(v_children_316_);
lean_dec_ref(v_x_312_);
lean_inc_ref(v_inst_311_);
v_localinst_317_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_317_, 0, v_inst_311_);
v___x_318_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5));
v___x_319_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6));
v___x_320_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Lean_Syntax_instReprRange_repr___redArg(v_range_314_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = 0;
v___x_325_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*1, v___x_324_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_319_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9));
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_box(1);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11));
v___x_332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_318_);
v___x_334_ = lean_apply_2(v_inst_311_, v_value_315_, v___x_321_);
v___x_335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_320_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*1, v___x_324_);
v___x_337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_333_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_327_);
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_329_);
v___x_340_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13));
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_318_);
v___x_343_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14);
v___x_344_ = l_Array_repr___redArg(v_localinst_317_, v_children_316_);
v___x_345_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*1, v___x_324_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_342_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17);
v___x_349_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18));
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_347_);
v___x_351_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19));
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_348_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_324_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr(lean_object* v_00_u03b1_355_, lean_object* v_inst_356_, lean_object* v_x_357_, lean_object* v_prec_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(v_inst_356_, v_x_357_, v_prec_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___boxed(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_x_362_, lean_object* v_prec_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Fmt_instReprRangeTreeNode_repr(v_00_u03b1_360_, v_inst_361_, v_x_362_, v_prec_363_);
lean_dec(v_prec_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode___redArg(lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___boxed), 4, 2);
lean_closure_set(v___x_366_, 0, lean_box(0));
lean_closure_set(v___x_366_, 1, v_inst_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode(lean_object* v_00_u03b1_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___boxed), 4, 2);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, v_inst_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default___redArg(){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = ((lean_object*)(l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default___redArg___boxed(lean_object* v___dummy_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Fmt_instInhabitedRangeTree_default___redArg();
return v_res_373_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedRangeTree_default___closed__0(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Fmt_instInhabitedRangeTree_default___redArg();
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default(lean_object* v_00_u03b1_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lean_Fmt_instInhabitedRangeTree_default___closed__0, &l_Lean_Fmt_instInhabitedRangeTree_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedRangeTree_default___closed__0);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree___redArg(){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lean_Fmt_instInhabitedRangeTree_default___closed__0, &l_Lean_Fmt_instInhabitedRangeTree_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedRangeTree_default___closed__0);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree___redArg___boxed(lean_object* v___dummy_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Fmt_instInhabitedRangeTree___redArg();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree(lean_object* v_a_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_obj_once(&l_Lean_Fmt_instInhabitedRangeTree_default___closed__0, &l_Lean_Fmt_instInhabitedRangeTree_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedRangeTree_default___closed__0);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg(lean_object* v_inst_392_, lean_object* v_x_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_394_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3));
v___x_395_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7);
v___x_396_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___boxed), 4, 2);
lean_closure_set(v___x_396_, 0, lean_box(0));
lean_closure_set(v___x_396_, 1, v_inst_392_);
v___x_397_ = l_Array_repr___redArg(v___x_396_, v_x_393_);
v___x_398_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_395_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = 0;
v___x_400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_399_);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_394_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17);
v___x_403_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18));
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_401_);
v___x_405_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19));
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*1, v___x_399_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_x_411_, lean_object* v_prec_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Fmt_instReprRangeTree_repr___redArg(v_inst_410_, v_x_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___boxed(lean_object* v_00_u03b1_414_, lean_object* v_inst_415_, lean_object* v_x_416_, lean_object* v_prec_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Fmt_instReprRangeTree_repr(v_00_u03b1_414_, v_inst_415_, v_x_416_, v_prec_417_);
lean_dec(v_prec_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree___redArg(lean_object* v_inst_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTree_repr___boxed), 4, 2);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, v_inst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree(lean_object* v_00_u03b1_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTree_repr___boxed), 4, 2);
lean_closure_set(v___x_423_, 0, lean_box(0));
lean_closure_set(v___x_423_, 1, v_inst_422_);
return v___x_423_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_compareRanges(lean_object* v_a_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_start_426_; lean_object* v_stop_427_; lean_object* v_start_428_; lean_object* v_stop_429_; uint8_t v___x_430_; 
v_start_426_ = lean_ctor_get(v_a_424_, 0);
v_stop_427_ = lean_ctor_get(v_a_424_, 1);
v_start_428_ = lean_ctor_get(v_b_425_, 0);
v_stop_429_ = lean_ctor_get(v_b_425_, 1);
v___x_430_ = lean_nat_dec_lt(v_start_426_, v_start_428_);
if (v___x_430_ == 0)
{
uint8_t v___x_431_; 
v___x_431_ = lean_nat_dec_eq(v_start_426_, v_start_428_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = 2;
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_lt(v_stop_429_, v_stop_427_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = lean_nat_dec_eq(v_stop_429_, v_stop_427_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = 2;
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 1;
return v___x_436_;
}
}
else
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
}
}
else
{
uint8_t v___x_438_; 
v___x_438_ = 0;
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_compareRanges___boxed(lean_object* v_a_439_, lean_object* v_b_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Lean_Fmt_compareRanges(v_a_439_, v_b_440_);
lean_dec_ref(v_b_440_);
lean_dec_ref(v_a_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(lean_object* v_entries_445_, lean_object* v_fst_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_494_; 
v_fst_448_ = lean_ctor_get(v_a_447_, 0);
v_snd_449_ = lean_ctor_get(v_a_447_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_494_ == 0)
{
v___x_451_ = v_a_447_;
v_isShared_452_ = v_isSharedCheck_494_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v_a_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_494_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_entries_445_);
v___x_454_ = lean_nat_dec_lt(v_snd_449_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_456_; 
if (v_isShared_452_ == 0)
{
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_448_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_snd_449_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_458_; lean_object* v_fst_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_492_; 
lean_del_object(v___x_451_);
v___x_458_ = lean_array_fget(v_entries_445_, v_snd_449_);
v_fst_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v___x_458_, 1);
lean_dec(v_unused_493_);
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_492_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_fst_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_492_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 0;
v___x_464_ = l_Lean_Syntax_Range_includes(v_fst_446_, v_fst_459_, v___x_463_, v___x_463_);
lean_dec(v_fst_459_);
if (v___x_464_ == 0)
{
lean_object* v___x_466_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_snd_449_);
lean_ctor_set(v___x_461_, 0, v_fst_448_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_fst_448_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_snd_449_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v___x_468_; lean_object* v_snd_469_; 
lean_del_object(v___x_461_);
v___x_468_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v_entries_445_, v_snd_449_);
v_snd_469_ = lean_ctor_get(v___x_468_, 1);
if (lean_obj_tag(v_snd_469_) == 1)
{
lean_object* v_fst_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_480_; 
lean_inc_ref(v_snd_469_);
v_fst_470_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v___x_468_, 1);
lean_dec(v_unused_481_);
v___x_472_ = v___x_468_;
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_fst_470_);
lean_dec(v___x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_val_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v_val_474_ = lean_ctor_get(v_snd_469_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_snd_469_, 1);
v___x_475_ = lean_array_push(v_fst_448_, v_val_474_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_fst_470_);
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_fst_470_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v_a_447_ = v___x_477_;
goto _start;
}
}
}
else
{
lean_object* v_fst_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_fst_482_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v___x_468_, 1);
lean_dec(v_unused_491_);
v___x_484_ = v___x_468_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_fst_482_);
lean_dec(v___x_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v_fst_482_);
lean_ctor_set(v___x_484_, 0, v_fst_448_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_fst_448_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_fst_482_);
v___x_487_ = v_reuseFailAlloc_489_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v_a_447_ = v___x_487_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(lean_object* v_entries_495_, lean_object* v_i_496_){
_start:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_array_get_size(v_entries_495_);
v___x_498_ = lean_nat_dec_lt(v_i_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_i_496_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_525_; 
v___x_501_ = lean_array_fget(v_entries_495_, v_i_496_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
v_snd_503_ = lean_ctor_get(v___x_501_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_525_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_525_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snd_503_);
lean_inc(v_fst_502_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_525_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_children_507_; lean_object* v___x_508_; lean_object* v_i_509_; lean_object* v___x_511_; 
v_children_507_ = ((lean_object*)(l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0));
v___x_508_ = lean_unsigned_to_nat(1u);
v_i_509_ = lean_nat_add(v_i_496_, v___x_508_);
lean_dec(v_i_496_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_i_509_);
lean_ctor_set(v___x_505_, 0, v_children_507_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_children_507_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_i_509_);
v___x_511_ = v_reuseFailAlloc_524_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_523_; 
v___x_512_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(v_entries_495_, v_fst_502_, v___x_511_);
v_fst_513_ = lean_ctor_get(v___x_512_, 0);
v_snd_514_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_523_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_inc(v_fst_513_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v_fst_502_);
lean_ctor_set(v___x_518_, 1, v_snd_503_);
lean_ctor_set(v___x_518_, 2, v_fst_513_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_519_);
lean_ctor_set(v___x_516_, 0, v_snd_514_);
v___x_521_ = v___x_516_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_snd_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___boxed(lean_object* v_entries_526_, lean_object* v_i_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v_entries_526_, v_i_527_);
lean_dec_ref(v_entries_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg___boxed(lean_object* v_entries_529_, lean_object* v_fst_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(v_entries_529_, v_fst_530_, v_a_531_);
lean_dec_ref(v_fst_530_);
lean_dec_ref(v_entries_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go(lean_object* v_00_u03b1_533_, lean_object* v_entries_534_, lean_object* v_i_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v_entries_534_, v_i_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___boxed(lean_object* v_00_u03b1_537_, lean_object* v_entries_538_, lean_object* v_i_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go(v_00_u03b1_537_, v_entries_538_, v_i_539_);
lean_dec_ref(v_entries_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0(lean_object* v_00_u03b1_541_, lean_object* v_entries_542_, lean_object* v_fst_543_, lean_object* v_inst_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(v_entries_542_, v_fst_543_, v_a_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___boxed(lean_object* v_00_u03b1_547_, lean_object* v_entries_548_, lean_object* v_fst_549_, lean_object* v_inst_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0(v_00_u03b1_547_, v_entries_548_, v_fst_549_, v_inst_550_, v_a_551_);
lean_dec_ref(v_fst_549_);
lean_dec_ref(v_entries_548_);
return v_res_552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_fst_555_; lean_object* v_fst_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_fst_555_ = lean_ctor_get(v_x_553_, 0);
v_fst_556_ = lean_ctor_get(v_x_554_, 0);
v___x_557_ = l_Lean_Fmt_compareRanges(v_fst_555_, v_fst_556_);
v___x_558_ = lean_box(v___x_557_);
v___x_559_ = lean_obj_tag_nat(v___x_558_);
lean_dec(v___x_558_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_nat_dec_eq(v___x_559_, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0___boxed(lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0(v_x_562_, v_x_563_);
lean_dec_ref(v_x_563_);
lean_dec_ref(v_x_562_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1(lean_object* v___y_566_, lean_object* v_b_567_){
_start:
{
lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_570_; lean_object* v_snd_571_; 
v_fst_568_ = lean_ctor_get(v_b_567_, 0);
lean_inc(v_fst_568_);
v_snd_569_ = lean_ctor_get(v_b_567_, 1);
lean_inc_n(v_snd_569_, 2);
lean_dec_ref(v_b_567_);
v___x_570_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v___y_566_, v_snd_569_);
v_snd_571_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_571_);
if (lean_obj_tag(v_snd_571_) == 1)
{
lean_object* v_fst_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_snd_569_);
v_fst_572_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v___x_570_, 1);
lean_dec(v_unused_589_);
v___x_574_ = v___x_570_;
v_isShared_575_ = v_isSharedCheck_588_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_fst_572_);
lean_dec(v___x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_588_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_587_; 
v_val_576_ = lean_ctor_get(v_snd_571_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_587_ == 0)
{
v___x_578_ = v_snd_571_;
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_snd_571_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = lean_array_push(v_fst_568_, v_val_576_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v_fst_572_);
lean_ctor_set(v___x_574_, 0, v___x_580_);
v___x_582_ = v___x_574_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_fst_572_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 0);
lean_ctor_set(v___x_578_, 0, v___x_582_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
else
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_snd_571_);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_598_ = lean_ctor_get(v___x_570_, 1);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v___x_570_, 0);
lean_dec(v_unused_599_);
v___x_591_ = v___x_570_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_dec(v___x_570_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v_snd_569_);
lean_ctor_set(v___x_591_, 0, v_fst_568_);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_fst_568_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_snd_569_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1___boxed(lean_object* v___y_600_, lean_object* v_b_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1(v___y_600_, v_b_601_);
lean_dec_ref(v___y_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__2(lean_object* v_x1_603_, lean_object* v_x2_604_, lean_object* v_x3_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_x2_604_);
lean_ctor_set(v___x_606_, 1, v_x3_605_);
v___x_607_ = lean_array_push(v_x1_603_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__3(lean_object* v___x_608_, lean_object* v___f_609_, lean_object* v_acc_610_, lean_object* v_l_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_608_, v___f_609_, v_acc_610_, v_l_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg(lean_object* v_entries_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v_size_647_; lean_object* v_buckets_648_; lean_object* v___f_649_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_665_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_638_ = ((lean_object*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9));
v_size_647_ = lean_ctor_get(v_entries_637_, 0);
lean_inc(v_size_647_);
v_buckets_648_ = lean_ctor_get(v_entries_637_, 1);
lean_inc_ref(v_buckets_648_);
lean_dec_ref(v_entries_637_);
v___f_649_ = ((lean_object*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10));
v___x_672_ = lean_mk_empty_array_with_capacity(v_size_647_);
lean_dec(v_size_647_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_array_get_size(v_buckets_648_);
v___x_675_ = lean_nat_dec_lt(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec_ref(v_buckets_648_);
v___y_665_ = v___x_672_;
goto v___jp_664_;
}
else
{
lean_object* v___f_676_; size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___f_676_ = ((lean_object*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12));
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_674_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_638_, v___f_676_, v_buckets_648_, v___x_677_, v___x_678_, v___x_672_);
v___y_665_ = v___x_679_;
goto v___jp_664_;
}
v___jp_639_:
{
lean_object* v___f_642_; lean_object* v_roots_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_fst_646_; 
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_642_, 0, v___y_641_);
v_roots_643_ = lean_mk_empty_array_with_capacity(v___y_640_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_roots_643_);
lean_ctor_set(v___x_644_, 1, v___y_640_);
v___x_645_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_638_, v___f_642_, v___x_644_);
v_fst_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_646_);
lean_dec(v___x_645_);
return v_fst_646_;
}
v___jp_650_:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_649_, v___y_651_, v___y_654_, v___y_653_, v___y_655_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_655_);
lean_dec(v___y_651_);
v___y_640_ = v___y_652_;
v___y_641_ = v___x_656_;
goto v___jp_639_;
}
v___jp_657_:
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_le(v___y_662_, v___y_661_);
if (v___x_663_ == 0)
{
lean_dec(v___y_661_);
lean_inc(v___y_662_);
v___y_651_ = v___y_658_;
v___y_652_ = v___y_659_;
v___y_653_ = v___y_662_;
v___y_654_ = v___y_660_;
v___y_655_ = v___y_662_;
goto v___jp_650_;
}
else
{
v___y_651_ = v___y_658_;
v___y_652_ = v___y_659_;
v___y_653_ = v___y_662_;
v___y_654_ = v___y_660_;
v___y_655_ = v___y_661_;
goto v___jp_650_;
}
}
v___jp_664_:
{
lean_object* v_i_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_i_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v___y_665_);
v___x_668_ = lean_nat_dec_eq(v___x_667_, v_i_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_sub(v___x_667_, v___x_669_);
v___x_671_ = lean_nat_dec_le(v_i_666_, v___x_670_);
if (v___x_671_ == 0)
{
lean_inc(v___x_670_);
v___y_658_ = v___x_667_;
v___y_659_ = v_i_666_;
v___y_660_ = v___y_665_;
v___y_661_ = v___x_670_;
v___y_662_ = v___x_670_;
goto v___jp_657_;
}
else
{
v___y_658_ = v___x_667_;
v___y_659_ = v_i_666_;
v___y_660_ = v___y_665_;
v___y_661_ = v___x_670_;
v___y_662_ = v_i_666_;
goto v___jp_657_;
}
}
else
{
v___y_640_ = v_i_666_;
v___y_641_ = v___y_665_;
goto v___jp_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_, lean_object* v_entries_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Fmt_RangeTree_ofHashMap___redArg(v_entries_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___boxed(lean_object* v_00_u03b1_684_, lean_object* v_inst_685_, lean_object* v_entries_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Fmt_RangeTree_ofHashMap(v_00_u03b1_684_, v_inst_685_, v_entries_686_);
lean_dec(v_inst_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0(lean_object* v_x_688_){
_start:
{
lean_object* v_range_689_; 
v_range_689_ = lean_ctor_get(v_x_688_, 0);
lean_inc_ref(v_range_689_);
return v_range_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0___boxed(lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0(v_x_690_);
lean_dec_ref(v_x_690_);
return v_res_691_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1(lean_object* v_x1_692_, lean_object* v_x2_693_){
_start:
{
lean_object* v_start_694_; lean_object* v_start_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_start_694_ = lean_ctor_get(v_x1_692_, 0);
v_start_695_ = lean_ctor_get(v_x2_693_, 0);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v_start_694_, v___x_696_);
v___x_698_ = lean_nat_dec_le(v___x_697_, v_start_695_);
lean_dec(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1___boxed(lean_object* v_x1_699_, lean_object* v_x2_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1(v_x1_699_, v_x2_700_);
lean_dec_ref(v_x2_700_);
lean_dec_ref(v_x1_699_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(lean_object* v_children_705_, lean_object* v_range_706_){
_start:
{
lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v___f_707_ = ((lean_object*)(l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0));
v___f_708_ = ((lean_object*)(l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1));
v___x_709_ = l_Lean_Fmt_binSearchRightmost___redArg(v_children_705_, v_range_706_, v___f_707_, v___f_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_val_711_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_719_ == 0)
{
v___x_713_ = v___x_709_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_val_711_);
lean_dec(v___x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_snd_715_; lean_object* v___x_717_; 
v_snd_715_ = lean_ctor_get(v_val_711_, 1);
lean_inc(v_snd_715_);
lean_dec(v_val_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v_snd_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_snd_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___boxed(lean_object* v_children_720_, lean_object* v_range_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_children_720_, v_range_721_);
lean_dec_ref(v_children_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining(lean_object* v_00_u03b1_723_, lean_object* v_children_724_, lean_object* v_range_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_children_724_, v_range_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___boxed(lean_object* v_00_u03b1_727_, lean_object* v_children_728_, lean_object* v_range_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining(v_00_u03b1_727_, v_children_728_, v_range_729_);
lean_dec_ref(v_children_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(lean_object* v_range_731_, lean_object* v_t_732_){
_start:
{
lean_object* v_range_733_; lean_object* v_value_734_; lean_object* v_children_735_; uint8_t v___x_736_; uint8_t v___x_737_; 
v_range_733_ = lean_ctor_get(v_t_732_, 0);
v_value_734_ = lean_ctor_get(v_t_732_, 1);
v_children_735_ = lean_ctor_get(v_t_732_, 2);
v___x_736_ = 0;
v___x_737_ = l_Lean_Syntax_Range_includes(v_range_733_, v_range_731_, v___x_736_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v_range_731_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v___x_739_; 
lean_inc_ref(v_range_731_);
v___x_739_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_children_735_, v_range_731_);
if (lean_obj_tag(v___x_739_) == 1)
{
lean_object* v_val_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_749_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_749_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_val_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_731_, v_val_740_);
lean_dec(v_val_740_);
if (lean_obj_tag(v___x_744_) == 1)
{
lean_del_object(v___x_742_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec(v___x_744_);
lean_inc(v_value_734_);
lean_inc_ref(v_range_733_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_range_733_);
lean_ctor_set(v___x_745_, 1, v_value_734_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_745_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v___x_739_);
lean_dec_ref(v_range_731_);
lean_inc(v_value_734_);
lean_inc_ref(v_range_733_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_range_733_);
lean_ctor_set(v___x_750_, 1, v_value_734_);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg___boxed(lean_object* v_range_752_, lean_object* v_t_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_752_, v_t_753_);
lean_dec_ref(v_t_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go(lean_object* v_00_u03b1_755_, lean_object* v_range_756_, lean_object* v_t_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_756_, v_t_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___boxed(lean_object* v_00_u03b1_759_, lean_object* v_range_760_, lean_object* v_t_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go(v_00_u03b1_759_, v_range_760_, v_t_761_);
lean_dec_ref(v_t_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(lean_object* v_t_763_, lean_object* v_range_764_){
_start:
{
lean_object* v___x_765_; 
lean_inc_ref(v_range_764_);
v___x_765_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_t_763_, v_range_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v_range_764_);
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v___x_765_, 1);
v___x_768_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_764_, v_val_767_);
lean_dec(v_val_767_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg___boxed(lean_object* v_t_769_, lean_object* v_range_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(v_t_769_, v_range_770_);
lean_dec_ref(v_t_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f(lean_object* v_00_u03b1_772_, lean_object* v_inst_773_, lean_object* v_t_774_, lean_object* v_range_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(v_t_774_, v_range_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___boxed(lean_object* v_00_u03b1_777_, lean_object* v_inst_778_, lean_object* v_t_779_, lean_object* v_range_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f(v_00_u03b1_777_, v_inst_778_, v_t_779_, v_range_780_);
lean_dec_ref(v_t_779_);
lean_dec(v_inst_778_);
return v_res_781_;
}
}
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_QSort_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Syntax(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Array_QSort_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Util_RangeTree(builtin);
}
#ifdef __cplusplus
}
#endif
