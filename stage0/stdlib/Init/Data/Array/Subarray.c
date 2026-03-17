// Lean compiler output
// Module: Init.Data.Array.Subarray
// Imports: public import Init.Data.Array.Basic public import Init.Data.Slice.Operations
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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_array___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_array___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_array___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_start___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_start___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_start(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_start___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_stop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_stop___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_stop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_stop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___lam__0___boxed(lean_object*);
static const lean_closure_object l_Subarray_instSliceSizeSubarrayData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_instSliceSizeSubarrayData___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_instSliceSizeSubarrayData___closed__0 = (const lean_object*)&l_Subarray_instSliceSizeSubarrayData___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0 = (const lean_object*)&l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_getD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_getD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_getD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_popFront___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_popFront(lean_object*, lean_object*);
static const lean_array_object l_Subarray_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Subarray_empty___closed__0 = (const lean_object*)&l_Subarray_empty___closed__0_value;
static const lean_ctor_object l_Subarray_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Subarray_empty___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Subarray_empty___closed__1 = (const lean_object*)&l_Subarray_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Subarray_empty(lean_object*);
static lean_once_cell_t l_Subarray_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Subarray_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Subarray_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__0 = (const lean_object*)&l_Subarray_foldr___redArg___closed__0_value;
static const lean_closure_object l_Subarray_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__1 = (const lean_object*)&l_Subarray_foldr___redArg___closed__1_value;
static const lean_closure_object l_Subarray_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__2 = (const lean_object*)&l_Subarray_foldr___redArg___closed__2_value;
static const lean_closure_object l_Subarray_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__3 = (const lean_object*)&l_Subarray_foldr___redArg___closed__3_value;
static const lean_closure_object l_Subarray_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__4 = (const lean_object*)&l_Subarray_foldr___redArg___closed__4_value;
static const lean_closure_object l_Subarray_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__5 = (const lean_object*)&l_Subarray_foldr___redArg___closed__5_value;
static const lean_closure_object l_Subarray_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_foldr___redArg___closed__6 = (const lean_object*)&l_Subarray_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Subarray_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Subarray_foldr___redArg___closed__0_value),((lean_object*)&l_Subarray_foldr___redArg___closed__1_value)}};
static const lean_object* l_Subarray_foldr___redArg___closed__7 = (const lean_object*)&l_Subarray_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Subarray_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Subarray_foldr___redArg___closed__7_value),((lean_object*)&l_Subarray_foldr___redArg___closed__2_value),((lean_object*)&l_Subarray_foldr___redArg___closed__3_value),((lean_object*)&l_Subarray_foldr___redArg___closed__4_value),((lean_object*)&l_Subarray_foldr___redArg___closed__5_value)}};
static const lean_object* l_Subarray_foldr___redArg___closed__8 = (const lean_object*)&l_Subarray_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Subarray_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Subarray_foldr___redArg___closed__8_value),((lean_object*)&l_Subarray_foldr___redArg___closed__6_value)}};
static const lean_object* l_Subarray_foldr___redArg___closed__9 = (const lean_object*)&l_Subarray_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subarray_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subarray_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subarray_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subarray_all___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subarray_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subarray_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toSubarray(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__0 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__0_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_:_]"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__1 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__2_value_aux_0),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(25, 16, 196, 182, 60, 93, 13, 211)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__2 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__2_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__3 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__4 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__5 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__5_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__6 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__6_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__7 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__7_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__8 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__8_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__8_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__9 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__9_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__7_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__9_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__10 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__10_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__11 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__11_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__11_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__12 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__12_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__13 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__13_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__14 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__14_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__15 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__15_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__16 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__16_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__16_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__17 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__17_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__15_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__17_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__18 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__18_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__18_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__15_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__19 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__19_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__12_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__19_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__20 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__20_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__10_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__20_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__21 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__21_value;
static const lean_string_object l_Array_term_____x5b___x3a___x5d___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__22 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__22_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__22_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__23 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__23_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__21_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__23_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__24 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__24_value;
static const lean_ctor_object l_Array_term_____x5b___x3a___x5d___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__24_value)}};
static const lean_object* l_Array_term_____x5b___x3a___x5d___closed__25 = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__25_value;
LEAN_EXPORT const lean_object* l_Array_term_____x5b___x3a___x5d = (const lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__25_value;
static const lean_string_object l_Array_term_____x5b___x3a_x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term__[_:]"};
static const lean_object* l_Array_term_____x5b___x3a_x5d___closed__0 = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__0_value;
static const lean_ctor_object l_Array_term_____x5b___x3a_x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_term_____x5b___x3a_x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__1_value_aux_0),((lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 86, 15, 94, 195, 189, 15, 195)}};
static const lean_object* l_Array_term_____x5b___x3a_x5d___closed__1 = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__1_value;
static const lean_ctor_object l_Array_term_____x5b___x3a_x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__12_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__18_value)}};
static const lean_object* l_Array_term_____x5b___x3a_x5d___closed__2 = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__2_value;
static const lean_ctor_object l_Array_term_____x5b___x3a_x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__10_value),((lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__2_value)}};
static const lean_object* l_Array_term_____x5b___x3a_x5d___closed__3 = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__3_value;
static const lean_ctor_object l_Array_term_____x5b___x3a_x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__3_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__23_value)}};
static const lean_object* l_Array_term_____x5b___x3a_x5d___closed__4 = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__4_value;
static const lean_ctor_object l_Array_term_____x5b___x3a_x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__4_value)}};
static const lean_object* l_Array_term_____x5b___x3a_x5d___closed__5 = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__5_value;
LEAN_EXPORT const lean_object* l_Array_term_____x5b___x3a_x5d = (const lean_object*)&l_Array_term_____x5b___x3a_x5d___closed__5_value;
static const lean_string_object l_Array_term_____x5b_x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term__[:_]"};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__0 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__0_value;
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 75, 86, 255, 23, 9, 108, 116)}};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__1 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__1_value;
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__17_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__15_value)}};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__2 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__2_value;
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__12_value),((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__2_value)}};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__3 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__3_value;
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__10_value),((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__3_value)}};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__4 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__4_value;
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__4_value),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__23_value)}};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__5 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__5_value;
static const lean_ctor_object l_Array_term_____x5b_x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__5_value)}};
static const lean_object* l_Array_term_____x5b_x3a___x5d___closed__6 = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__6_value;
LEAN_EXPORT const lean_object* l_Array_term_____x5b_x3a___x5d = (const lean_object*)&l_Array_term_____x5b_x3a___x5d___closed__6_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Array.toSubarray"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSubarray"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_term_____x5b___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(140, 19, 103, 132, 228, 195, 183, 57)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 166, 195, 152, 24, 103, 8, 2)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "a.size"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(226, 190, 230, 164, 209, 231, 8, 30)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_array___redArg(lean_object* v_xs_1_){
_start:
{
lean_object* v_array_2_; 
v_array_2_ = lean_ctor_get(v_xs_1_, 0);
lean_inc_ref(v_array_2_);
return v_array_2_;
}
}
LEAN_EXPORT lean_object* l_Subarray_array___redArg___boxed(lean_object* v_xs_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Subarray_array___redArg(v_xs_3_);
lean_dec_ref(v_xs_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Subarray_array(lean_object* v_00_u03b1_5_, lean_object* v_xs_6_){
_start:
{
lean_object* v_array_7_; 
v_array_7_ = lean_ctor_get(v_xs_6_, 0);
lean_inc_ref(v_array_7_);
return v_array_7_;
}
}
LEAN_EXPORT lean_object* l_Subarray_array___boxed(lean_object* v_00_u03b1_8_, lean_object* v_xs_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Subarray_array(v_00_u03b1_8_, v_xs_9_);
lean_dec_ref(v_xs_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Subarray_start___redArg(lean_object* v_xs_11_){
_start:
{
lean_object* v_start_12_; 
v_start_12_ = lean_ctor_get(v_xs_11_, 1);
lean_inc(v_start_12_);
return v_start_12_;
}
}
LEAN_EXPORT lean_object* l_Subarray_start___redArg___boxed(lean_object* v_xs_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Subarray_start___redArg(v_xs_13_);
lean_dec_ref(v_xs_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Subarray_start(lean_object* v_00_u03b1_15_, lean_object* v_xs_16_){
_start:
{
lean_object* v_start_17_; 
v_start_17_ = lean_ctor_get(v_xs_16_, 1);
lean_inc(v_start_17_);
return v_start_17_;
}
}
LEAN_EXPORT lean_object* l_Subarray_start___boxed(lean_object* v_00_u03b1_18_, lean_object* v_xs_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Subarray_start(v_00_u03b1_18_, v_xs_19_);
lean_dec_ref(v_xs_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Subarray_stop___redArg(lean_object* v_xs_21_){
_start:
{
lean_object* v_stop_22_; 
v_stop_22_ = lean_ctor_get(v_xs_21_, 2);
lean_inc(v_stop_22_);
return v_stop_22_;
}
}
LEAN_EXPORT lean_object* l_Subarray_stop___redArg___boxed(lean_object* v_xs_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Subarray_stop___redArg(v_xs_23_);
lean_dec_ref(v_xs_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Subarray_stop(lean_object* v_00_u03b1_25_, lean_object* v_xs_26_){
_start:
{
lean_object* v_stop_27_; 
v_stop_27_ = lean_ctor_get(v_xs_26_, 2);
lean_inc(v_stop_27_);
return v_stop_27_;
}
}
LEAN_EXPORT lean_object* l_Subarray_stop___boxed(lean_object* v_00_u03b1_28_, lean_object* v_xs_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Subarray_stop(v_00_u03b1_28_, v_xs_29_);
lean_dec_ref(v_xs_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___lam__0(lean_object* v_s_31_){
_start:
{
lean_object* v_start_32_; lean_object* v_stop_33_; lean_object* v___x_34_; 
v_start_32_ = lean_ctor_get(v_s_31_, 1);
v_stop_33_ = lean_ctor_get(v_s_31_, 2);
v___x_34_ = lean_nat_sub(v_stop_33_, v_start_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___lam__0___boxed(lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Subarray_instSliceSizeSubarrayData___lam__0(v_s_35_);
lean_dec_ref(v_s_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData(lean_object* v_00_u03b1_38_){
_start:
{
lean_object* v___f_39_; 
v___f_39_ = ((lean_object*)(l_Subarray_instSliceSizeSubarrayData___closed__0));
return v___f_39_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___redArg(lean_object* v_s_40_, lean_object* v_i_41_){
_start:
{
lean_object* v_array_42_; lean_object* v_start_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_array_42_ = lean_ctor_get(v_s_40_, 0);
v_start_43_ = lean_ctor_get(v_s_40_, 1);
v___x_44_ = lean_nat_add(v_start_43_, v_i_41_);
v___x_45_ = lean_array_fget_borrowed(v_array_42_, v___x_44_);
lean_dec(v___x_44_);
lean_inc(v___x_45_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___redArg___boxed(lean_object* v_s_46_, lean_object* v_i_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Subarray_get___redArg(v_s_46_, v_i_47_);
lean_dec(v_i_47_);
lean_dec_ref(v_s_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get(lean_object* v_00_u03b1_49_, lean_object* v_s_50_, lean_object* v_i_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Subarray_get___redArg(v_s_50_, v_i_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___boxed(lean_object* v_00_u03b1_53_, lean_object* v_s_54_, lean_object* v_i_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Subarray_get(v_00_u03b1_53_, v_s_54_, v_i_55_);
lean_dec(v_i_55_);
lean_dec_ref(v_s_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(lean_object* v_xs_57_, lean_object* v_i_58_, lean_object* v_h_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Subarray_get___redArg(v_xs_57_, v_i_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed(lean_object* v_xs_61_, lean_object* v_i_62_, lean_object* v_h_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(v_xs_61_, v_i_62_, v_h_63_);
lean_dec(v_i_62_);
lean_dec_ref(v_xs_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData(lean_object* v_00_u03b1_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = ((lean_object*)(l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0));
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___redArg(lean_object* v_s_68_, lean_object* v_i_69_, lean_object* v_v_u2080_70_){
_start:
{
lean_object* v_start_71_; lean_object* v_stop_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v_start_71_ = lean_ctor_get(v_s_68_, 1);
v_stop_72_ = lean_ctor_get(v_s_68_, 2);
v___x_73_ = lean_nat_sub(v_stop_72_, v_start_71_);
v___x_74_ = lean_nat_dec_lt(v_i_69_, v___x_73_);
lean_dec(v___x_73_);
if (v___x_74_ == 0)
{
lean_inc(v_v_u2080_70_);
return v_v_u2080_70_;
}
else
{
lean_object* v___x_75_; 
v___x_75_ = l_Subarray_get___redArg(v_s_68_, v_i_69_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___redArg___boxed(lean_object* v_s_76_, lean_object* v_i_77_, lean_object* v_v_u2080_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Subarray_getD___redArg(v_s_76_, v_i_77_, v_v_u2080_78_);
lean_dec(v_v_u2080_78_);
lean_dec(v_i_77_);
lean_dec_ref(v_s_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Subarray_getD(lean_object* v_00_u03b1_80_, lean_object* v_s_81_, lean_object* v_i_82_, lean_object* v_v_u2080_83_){
_start:
{
lean_object* v_start_84_; lean_object* v_stop_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_start_84_ = lean_ctor_get(v_s_81_, 1);
v_stop_85_ = lean_ctor_get(v_s_81_, 2);
v___x_86_ = lean_nat_sub(v_stop_85_, v_start_84_);
v___x_87_ = lean_nat_dec_lt(v_i_82_, v___x_86_);
lean_dec(v___x_86_);
if (v___x_87_ == 0)
{
lean_inc(v_v_u2080_83_);
return v_v_u2080_83_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = l_Subarray_get___redArg(v_s_81_, v_i_82_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___boxed(lean_object* v_00_u03b1_89_, lean_object* v_s_90_, lean_object* v_i_91_, lean_object* v_v_u2080_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Subarray_getD(v_00_u03b1_89_, v_s_90_, v_i_91_, v_v_u2080_92_);
lean_dec(v_v_u2080_92_);
lean_dec(v_i_91_);
lean_dec_ref(v_s_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg(lean_object* v_inst_94_, lean_object* v_s_95_, lean_object* v_i_96_){
_start:
{
lean_object* v_start_97_; lean_object* v_stop_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_start_97_ = lean_ctor_get(v_s_95_, 1);
v_stop_98_ = lean_ctor_get(v_s_95_, 2);
v___x_99_ = lean_nat_sub(v_stop_98_, v_start_97_);
v___x_100_ = lean_nat_dec_lt(v_i_96_, v___x_99_);
lean_dec(v___x_99_);
if (v___x_100_ == 0)
{
lean_inc(v_inst_94_);
return v_inst_94_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = l_Subarray_get___redArg(v_s_95_, v_i_96_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg___boxed(lean_object* v_inst_102_, lean_object* v_s_103_, lean_object* v_i_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Subarray_get_x21___redArg(v_inst_102_, v_s_103_, v_i_104_);
lean_dec(v_i_104_);
lean_dec_ref(v_s_103_);
lean_dec(v_inst_102_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_s_108_, lean_object* v_i_109_){
_start:
{
lean_object* v_start_110_; lean_object* v_stop_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_start_110_ = lean_ctor_get(v_s_108_, 1);
v_stop_111_ = lean_ctor_get(v_s_108_, 2);
v___x_112_ = lean_nat_sub(v_stop_111_, v_start_110_);
v___x_113_ = lean_nat_dec_lt(v_i_109_, v___x_112_);
lean_dec(v___x_112_);
if (v___x_113_ == 0)
{
lean_inc(v_inst_107_);
return v_inst_107_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = l_Subarray_get___redArg(v_s_108_, v_i_109_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___boxed(lean_object* v_00_u03b1_115_, lean_object* v_inst_116_, lean_object* v_s_117_, lean_object* v_i_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Subarray_get_x21(v_00_u03b1_115_, v_inst_116_, v_s_117_, v_i_118_);
lean_dec(v_i_118_);
lean_dec_ref(v_s_117_);
lean_dec(v_inst_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Subarray_popFront___redArg(lean_object* v_s_120_){
_start:
{
lean_object* v_array_121_; lean_object* v_start_122_; lean_object* v_stop_123_; uint8_t v___x_124_; 
v_array_121_ = lean_ctor_get(v_s_120_, 0);
v_start_122_ = lean_ctor_get(v_s_120_, 1);
v_stop_123_ = lean_ctor_get(v_s_120_, 2);
v___x_124_ = lean_nat_dec_lt(v_start_122_, v_stop_123_);
if (v___x_124_ == 0)
{
return v_s_120_;
}
else
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_133_; 
lean_inc(v_stop_123_);
lean_inc(v_start_122_);
lean_inc_ref(v_array_121_);
v_isSharedCheck_133_ = !lean_is_exclusive(v_s_120_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_134_ = lean_ctor_get(v_s_120_, 2);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_s_120_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_s_120_, 0);
lean_dec(v_unused_136_);
v___x_126_ = v_s_120_;
v_isShared_127_ = v_isSharedCheck_133_;
goto v_resetjp_125_;
}
else
{
lean_dec(v_s_120_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_133_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_start_122_, v___x_128_);
lean_dec(v_start_122_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_129_);
v___x_131_ = v___x_126_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_array_121_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_stop_123_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_popFront(lean_object* v_00_u03b1_137_, lean_object* v_s_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Subarray_popFront___redArg(v_s_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Subarray_empty(lean_object* v_00_u03b1_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l_Subarray_empty___closed__1));
return v___x_146_;
}
}
static lean_object* _init_l_Subarray_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Subarray_empty(lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection(lean_object* v_00_u03b1_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Subarray_instEmptyCollection___closed__0, &l_Subarray_instEmptyCollection___closed__0_once, _init_l_Subarray_instEmptyCollection___closed__0);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instInhabited(lean_object* v_00_u03b1_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Subarray_instEmptyCollection___closed__0, &l_Subarray_instEmptyCollection___closed__0_once, _init_l_Subarray_instEmptyCollection___closed__0);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM___redArg(lean_object* v_inst_152_, lean_object* v_f_153_, lean_object* v_init_154_, lean_object* v_as_155_){
_start:
{
lean_object* v_array_156_; lean_object* v_start_157_; lean_object* v_stop_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_array_156_ = lean_ctor_get(v_as_155_, 0);
lean_inc_ref(v_array_156_);
v_start_157_ = lean_ctor_get(v_as_155_, 1);
lean_inc(v_start_157_);
v_stop_158_ = lean_ctor_get(v_as_155_, 2);
lean_inc(v_stop_158_);
lean_dec_ref(v_as_155_);
v___x_159_ = lean_array_get_size(v_array_156_);
v___x_160_ = lean_nat_dec_le(v_stop_158_, v___x_159_);
if (v___x_160_ == 0)
{
uint8_t v___x_161_; 
lean_dec(v_stop_158_);
v___x_161_ = lean_nat_dec_lt(v_start_157_, v___x_159_);
if (v___x_161_ == 0)
{
lean_object* v_toApplicative_162_; lean_object* v_toPure_163_; lean_object* v___x_164_; 
lean_dec(v_start_157_);
lean_dec_ref(v_array_156_);
lean_dec(v_f_153_);
v_toApplicative_162_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_ref(v_toApplicative_162_);
lean_dec_ref(v_inst_152_);
v_toPure_163_ = lean_ctor_get(v_toApplicative_162_, 1);
lean_inc(v_toPure_163_);
lean_dec_ref(v_toApplicative_162_);
v___x_164_ = lean_apply_2(v_toPure_163_, lean_box(0), v_init_154_);
return v___x_164_;
}
else
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_usize_of_nat(v___x_159_);
v___x_166_ = lean_usize_of_nat(v_start_157_);
lean_dec(v_start_157_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_152_, v_f_153_, v_array_156_, v___x_165_, v___x_166_, v_init_154_);
return v___x_167_;
}
}
else
{
uint8_t v___x_168_; 
v___x_168_ = lean_nat_dec_lt(v_start_157_, v_stop_158_);
if (v___x_168_ == 0)
{
lean_object* v_toApplicative_169_; lean_object* v_toPure_170_; lean_object* v___x_171_; 
lean_dec(v_stop_158_);
lean_dec(v_start_157_);
lean_dec_ref(v_array_156_);
lean_dec(v_f_153_);
v_toApplicative_169_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_ref(v_toApplicative_169_);
lean_dec_ref(v_inst_152_);
v_toPure_170_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_170_);
lean_dec_ref(v_toApplicative_169_);
v___x_171_ = lean_apply_2(v_toPure_170_, lean_box(0), v_init_154_);
return v___x_171_;
}
else
{
size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_usize_of_nat(v_stop_158_);
lean_dec(v_stop_158_);
v___x_173_ = lean_usize_of_nat(v_start_157_);
lean_dec(v_start_157_);
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_152_, v_f_153_, v_array_156_, v___x_172_, v___x_173_, v_init_154_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM(lean_object* v_00_u03b1_175_, lean_object* v_00_u03b2_176_, lean_object* v_m_177_, lean_object* v_inst_178_, lean_object* v_f_179_, lean_object* v_init_180_, lean_object* v_as_181_){
_start:
{
lean_object* v_array_182_; lean_object* v_start_183_; lean_object* v_stop_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_array_182_ = lean_ctor_get(v_as_181_, 0);
lean_inc_ref(v_array_182_);
v_start_183_ = lean_ctor_get(v_as_181_, 1);
lean_inc(v_start_183_);
v_stop_184_ = lean_ctor_get(v_as_181_, 2);
lean_inc(v_stop_184_);
lean_dec_ref(v_as_181_);
v___x_185_ = lean_array_get_size(v_array_182_);
v___x_186_ = lean_nat_dec_le(v_stop_184_, v___x_185_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
lean_dec(v_stop_184_);
v___x_187_ = lean_nat_dec_lt(v_start_183_, v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v_toApplicative_188_; lean_object* v_toPure_189_; lean_object* v___x_190_; 
lean_dec(v_start_183_);
lean_dec_ref(v_array_182_);
lean_dec(v_f_179_);
v_toApplicative_188_ = lean_ctor_get(v_inst_178_, 0);
lean_inc_ref(v_toApplicative_188_);
lean_dec_ref(v_inst_178_);
v_toPure_189_ = lean_ctor_get(v_toApplicative_188_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_188_);
v___x_190_ = lean_apply_2(v_toPure_189_, lean_box(0), v_init_180_);
return v___x_190_;
}
else
{
size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_usize_of_nat(v___x_185_);
v___x_192_ = lean_usize_of_nat(v_start_183_);
lean_dec(v_start_183_);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_178_, v_f_179_, v_array_182_, v___x_191_, v___x_192_, v_init_180_);
return v___x_193_;
}
}
else
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_lt(v_start_183_, v_stop_184_);
if (v___x_194_ == 0)
{
lean_object* v_toApplicative_195_; lean_object* v_toPure_196_; lean_object* v___x_197_; 
lean_dec(v_stop_184_);
lean_dec(v_start_183_);
lean_dec_ref(v_array_182_);
lean_dec(v_f_179_);
v_toApplicative_195_ = lean_ctor_get(v_inst_178_, 0);
lean_inc_ref(v_toApplicative_195_);
lean_dec_ref(v_inst_178_);
v_toPure_196_ = lean_ctor_get(v_toApplicative_195_, 1);
lean_inc(v_toPure_196_);
lean_dec_ref(v_toApplicative_195_);
v___x_197_ = lean_apply_2(v_toPure_196_, lean_box(0), v_init_180_);
return v___x_197_;
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_usize_of_nat(v_stop_184_);
lean_dec(v_stop_184_);
v___x_199_ = lean_usize_of_nat(v_start_183_);
lean_dec(v_start_183_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_178_, v_f_179_, v_array_182_, v___x_198_, v___x_199_, v_init_180_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM___redArg(lean_object* v_inst_201_, lean_object* v_p_202_, lean_object* v_as_203_){
_start:
{
lean_object* v_array_204_; lean_object* v_start_205_; lean_object* v_stop_206_; lean_object* v___y_208_; uint8_t v___x_217_; 
v_array_204_ = lean_ctor_get(v_as_203_, 0);
lean_inc_ref(v_array_204_);
v_start_205_ = lean_ctor_get(v_as_203_, 1);
lean_inc(v_start_205_);
v_stop_206_ = lean_ctor_get(v_as_203_, 2);
lean_inc(v_stop_206_);
lean_dec_ref(v_as_203_);
v___x_217_ = lean_nat_dec_lt(v_start_205_, v_stop_206_);
if (v___x_217_ == 0)
{
lean_object* v_toApplicative_218_; lean_object* v_toPure_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_stop_206_);
lean_dec(v_start_205_);
lean_dec_ref(v_array_204_);
lean_dec(v_p_202_);
v_toApplicative_218_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_ref(v_toApplicative_218_);
lean_dec_ref(v_inst_201_);
v_toPure_219_ = lean_ctor_get(v_toApplicative_218_, 1);
lean_inc(v_toPure_219_);
lean_dec_ref(v_toApplicative_218_);
v___x_220_ = lean_box(v___x_217_);
v___x_221_ = lean_apply_2(v_toPure_219_, lean_box(0), v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_array_get_size(v_array_204_);
v___x_223_ = lean_nat_dec_le(v_stop_206_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v_stop_206_);
v___y_208_ = v___x_222_;
goto v___jp_207_;
}
else
{
v___y_208_ = v_stop_206_;
goto v___jp_207_;
}
}
v___jp_207_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_lt(v_start_205_, v___y_208_);
if (v___x_209_ == 0)
{
lean_object* v_toApplicative_210_; lean_object* v_toPure_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___y_208_);
lean_dec(v_start_205_);
lean_dec_ref(v_array_204_);
lean_dec(v_p_202_);
v_toApplicative_210_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_ref(v_toApplicative_210_);
lean_dec_ref(v_inst_201_);
v_toPure_211_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_inc(v_toPure_211_);
lean_dec_ref(v_toApplicative_210_);
v___x_212_ = lean_box(v___x_209_);
v___x_213_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_212_);
return v___x_213_;
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_usize_of_nat(v_start_205_);
lean_dec(v_start_205_);
v___x_215_ = lean_usize_of_nat(v___y_208_);
lean_dec(v___y_208_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_201_, v_p_202_, v_array_204_, v___x_214_, v___x_215_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM(lean_object* v_00_u03b1_224_, lean_object* v_m_225_, lean_object* v_inst_226_, lean_object* v_p_227_, lean_object* v_as_228_){
_start:
{
lean_object* v_array_229_; lean_object* v_start_230_; lean_object* v_stop_231_; lean_object* v___y_233_; uint8_t v___x_242_; 
v_array_229_ = lean_ctor_get(v_as_228_, 0);
lean_inc_ref(v_array_229_);
v_start_230_ = lean_ctor_get(v_as_228_, 1);
lean_inc(v_start_230_);
v_stop_231_ = lean_ctor_get(v_as_228_, 2);
lean_inc(v_stop_231_);
lean_dec_ref(v_as_228_);
v___x_242_ = lean_nat_dec_lt(v_start_230_, v_stop_231_);
if (v___x_242_ == 0)
{
lean_object* v_toApplicative_243_; lean_object* v_toPure_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v_stop_231_);
lean_dec(v_start_230_);
lean_dec_ref(v_array_229_);
lean_dec(v_p_227_);
v_toApplicative_243_ = lean_ctor_get(v_inst_226_, 0);
lean_inc_ref(v_toApplicative_243_);
lean_dec_ref(v_inst_226_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_243_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_243_);
v___x_245_ = lean_box(v___x_242_);
v___x_246_ = lean_apply_2(v_toPure_244_, lean_box(0), v___x_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_array_get_size(v_array_229_);
v___x_248_ = lean_nat_dec_le(v_stop_231_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_stop_231_);
v___y_233_ = v___x_247_;
goto v___jp_232_;
}
else
{
v___y_233_ = v_stop_231_;
goto v___jp_232_;
}
}
v___jp_232_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_nat_dec_lt(v_start_230_, v___y_233_);
if (v___x_234_ == 0)
{
lean_object* v_toApplicative_235_; lean_object* v_toPure_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v___y_233_);
lean_dec(v_start_230_);
lean_dec_ref(v_array_229_);
lean_dec(v_p_227_);
v_toApplicative_235_ = lean_ctor_get(v_inst_226_, 0);
lean_inc_ref(v_toApplicative_235_);
lean_dec_ref(v_inst_226_);
v_toPure_236_ = lean_ctor_get(v_toApplicative_235_, 1);
lean_inc(v_toPure_236_);
lean_dec_ref(v_toApplicative_235_);
v___x_237_ = lean_box(v___x_234_);
v___x_238_ = lean_apply_2(v_toPure_236_, lean_box(0), v___x_237_);
return v___x_238_;
}
else
{
size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_usize_of_nat(v_start_230_);
lean_dec(v_start_230_);
v___x_240_ = lean_usize_of_nat(v___y_233_);
lean_dec(v___y_233_);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_226_, v_p_227_, v_array_229_, v___x_239_, v___x_240_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0(lean_object* v_toPure_249_, uint8_t v_____do__lift_250_){
_start:
{
if (v_____do__lift_250_ == 0)
{
uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = 1;
v___x_252_ = lean_box(v___x_251_);
v___x_253_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_252_);
return v___x_253_;
}
else
{
uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = 0;
v___x_255_ = lean_box(v___x_254_);
v___x_256_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0___boxed(lean_object* v_toPure_257_, lean_object* v_____do__lift_258_){
_start:
{
uint8_t v_____do__lift_115__boxed_259_; lean_object* v_res_260_; 
v_____do__lift_115__boxed_259_ = lean_unbox(v_____do__lift_258_);
v_res_260_ = l_Subarray_allM___redArg___lam__0(v_toPure_257_, v_____do__lift_115__boxed_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1(lean_object* v_toPure_261_, uint8_t v___x_262_, uint8_t v_____do__lift_263_){
_start:
{
if (v_____do__lift_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_box(v___x_262_);
v___x_265_ = lean_apply_2(v_toPure_261_, lean_box(0), v___x_264_);
return v___x_265_;
}
else
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = 0;
v___x_267_ = lean_box(v___x_266_);
v___x_268_ = lean_apply_2(v_toPure_261_, lean_box(0), v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1___boxed(lean_object* v_toPure_269_, lean_object* v___x_270_, lean_object* v_____do__lift_271_){
_start:
{
uint8_t v___x_130__boxed_272_; uint8_t v_____do__lift_131__boxed_273_; lean_object* v_res_274_; 
v___x_130__boxed_272_ = lean_unbox(v___x_270_);
v_____do__lift_131__boxed_273_ = lean_unbox(v_____do__lift_271_);
v_res_274_ = l_Subarray_allM___redArg___lam__1(v_toPure_269_, v___x_130__boxed_272_, v_____do__lift_131__boxed_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__2(lean_object* v_p_275_, lean_object* v_toBind_276_, lean_object* v___f_277_, lean_object* v_v_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_apply_1(v_p_275_, v_v_278_);
v___x_280_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_279_, v___f_277_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg(lean_object* v_inst_281_, lean_object* v_p_282_, lean_object* v_as_283_){
_start:
{
lean_object* v_toApplicative_284_; lean_object* v_array_285_; lean_object* v_start_286_; lean_object* v_stop_287_; lean_object* v_toBind_288_; lean_object* v_toPure_289_; lean_object* v___f_290_; uint8_t v___x_291_; 
v_toApplicative_284_ = lean_ctor_get(v_inst_281_, 0);
v_array_285_ = lean_ctor_get(v_as_283_, 0);
lean_inc_ref(v_array_285_);
v_start_286_ = lean_ctor_get(v_as_283_, 1);
lean_inc(v_start_286_);
v_stop_287_ = lean_ctor_get(v_as_283_, 2);
lean_inc(v_stop_287_);
lean_dec_ref(v_as_283_);
v_toBind_288_ = lean_ctor_get(v_inst_281_, 1);
lean_inc(v_toBind_288_);
v_toPure_289_ = lean_ctor_get(v_toApplicative_284_, 1);
lean_inc(v_toPure_289_);
v___f_290_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_290_, 0, v_toPure_289_);
v___x_291_ = lean_nat_dec_lt(v_start_286_, v_stop_287_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_inc(v_toPure_289_);
lean_dec(v_stop_287_);
lean_dec(v_start_286_);
lean_dec_ref(v_array_285_);
lean_dec(v_p_282_);
lean_dec_ref(v_inst_281_);
v___x_292_ = lean_box(v___x_291_);
v___x_293_ = lean_apply_2(v_toPure_289_, lean_box(0), v___x_292_);
v___x_294_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_293_, v___f_290_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___y_299_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_295_ = lean_box(v___x_291_);
lean_inc(v_toPure_289_);
v___f_296_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_296_, 0, v_toPure_289_);
lean_closure_set(v___f_296_, 1, v___x_295_);
lean_inc(v_toBind_288_);
v___f_297_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_297_, 0, v_p_282_);
lean_closure_set(v___f_297_, 1, v_toBind_288_);
lean_closure_set(v___f_297_, 2, v___f_296_);
v___x_308_ = lean_array_get_size(v_array_285_);
v___x_309_ = lean_nat_dec_le(v_stop_287_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v_stop_287_);
v___y_299_ = v___x_308_;
goto v___jp_298_;
}
else
{
v___y_299_ = v_stop_287_;
goto v___jp_298_;
}
v___jp_298_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_lt(v_start_286_, v___y_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_inc(v_toPure_289_);
lean_dec(v___y_299_);
lean_dec_ref(v___f_297_);
lean_dec(v_start_286_);
lean_dec_ref(v_array_285_);
lean_dec_ref(v_inst_281_);
v___x_301_ = lean_box(v___x_300_);
v___x_302_ = lean_apply_2(v_toPure_289_, lean_box(0), v___x_301_);
v___x_303_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_302_, v___f_290_);
return v___x_303_;
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_usize_of_nat(v_start_286_);
lean_dec(v_start_286_);
v___x_305_ = lean_usize_of_nat(v___y_299_);
lean_dec(v___y_299_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_281_, v___f_297_, v_array_285_, v___x_304_, v___x_305_);
v___x_307_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_306_, v___f_290_);
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM(lean_object* v_00_u03b1_310_, lean_object* v_m_311_, lean_object* v_inst_312_, lean_object* v_p_313_, lean_object* v_as_314_){
_start:
{
lean_object* v_toApplicative_315_; lean_object* v_array_316_; lean_object* v_start_317_; lean_object* v_stop_318_; lean_object* v_toBind_319_; lean_object* v_toPure_320_; lean_object* v___f_321_; uint8_t v___x_322_; 
v_toApplicative_315_ = lean_ctor_get(v_inst_312_, 0);
v_array_316_ = lean_ctor_get(v_as_314_, 0);
lean_inc_ref(v_array_316_);
v_start_317_ = lean_ctor_get(v_as_314_, 1);
lean_inc(v_start_317_);
v_stop_318_ = lean_ctor_get(v_as_314_, 2);
lean_inc(v_stop_318_);
lean_dec_ref(v_as_314_);
v_toBind_319_ = lean_ctor_get(v_inst_312_, 1);
lean_inc(v_toBind_319_);
v_toPure_320_ = lean_ctor_get(v_toApplicative_315_, 1);
lean_inc(v_toPure_320_);
v___f_321_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_321_, 0, v_toPure_320_);
v___x_322_ = lean_nat_dec_lt(v_start_317_, v_stop_318_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_inc(v_toPure_320_);
lean_dec(v_stop_318_);
lean_dec(v_start_317_);
lean_dec_ref(v_array_316_);
lean_dec(v_p_313_);
lean_dec_ref(v_inst_312_);
v___x_323_ = lean_box(v___x_322_);
v___x_324_ = lean_apply_2(v_toPure_320_, lean_box(0), v___x_323_);
v___x_325_ = lean_apply_4(v_toBind_319_, lean_box(0), lean_box(0), v___x_324_, v___f_321_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___f_327_; lean_object* v___f_328_; lean_object* v___y_330_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_326_ = lean_box(v___x_322_);
lean_inc(v_toPure_320_);
v___f_327_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_327_, 0, v_toPure_320_);
lean_closure_set(v___f_327_, 1, v___x_326_);
lean_inc(v_toBind_319_);
v___f_328_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_328_, 0, v_p_313_);
lean_closure_set(v___f_328_, 1, v_toBind_319_);
lean_closure_set(v___f_328_, 2, v___f_327_);
v___x_339_ = lean_array_get_size(v_array_316_);
v___x_340_ = lean_nat_dec_le(v_stop_318_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v_stop_318_);
v___y_330_ = v___x_339_;
goto v___jp_329_;
}
else
{
v___y_330_ = v_stop_318_;
goto v___jp_329_;
}
v___jp_329_:
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_lt(v_start_317_, v___y_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_inc(v_toPure_320_);
lean_dec(v___y_330_);
lean_dec_ref(v___f_328_);
lean_dec(v_start_317_);
lean_dec_ref(v_array_316_);
lean_dec_ref(v_inst_312_);
v___x_332_ = lean_box(v___x_331_);
v___x_333_ = lean_apply_2(v_toPure_320_, lean_box(0), v___x_332_);
v___x_334_ = lean_apply_4(v_toBind_319_, lean_box(0), lean_box(0), v___x_333_, v___f_321_);
return v___x_334_;
}
else
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_usize_of_nat(v_start_317_);
lean_dec(v_start_317_);
v___x_336_ = lean_usize_of_nat(v___y_330_);
lean_dec(v___y_330_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_312_, v___f_328_, v_array_316_, v___x_335_, v___x_336_);
v___x_338_ = lean_apply_4(v_toBind_319_, lean_box(0), lean_box(0), v___x_337_, v___f_321_);
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg___lam__0(lean_object* v_f_341_, lean_object* v_x_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_apply_1(v_f_341_, v___y_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg(lean_object* v_inst_345_, lean_object* v_f_346_, lean_object* v_as_347_){
_start:
{
lean_object* v_array_348_; lean_object* v_start_349_; lean_object* v_stop_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_array_348_ = lean_ctor_get(v_as_347_, 0);
lean_inc_ref(v_array_348_);
v_start_349_ = lean_ctor_get(v_as_347_, 1);
lean_inc(v_start_349_);
v_stop_350_ = lean_ctor_get(v_as_347_, 2);
lean_inc(v_stop_350_);
lean_dec_ref(v_as_347_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_nat_dec_lt(v_start_349_, v_stop_350_);
if (v___x_352_ == 0)
{
lean_object* v_toApplicative_353_; lean_object* v_toPure_354_; lean_object* v___x_355_; 
lean_dec(v_stop_350_);
lean_dec(v_start_349_);
lean_dec_ref(v_array_348_);
lean_dec(v_f_346_);
v_toApplicative_353_ = lean_ctor_get(v_inst_345_, 0);
lean_inc_ref(v_toApplicative_353_);
lean_dec_ref(v_inst_345_);
v_toPure_354_ = lean_ctor_get(v_toApplicative_353_, 1);
lean_inc(v_toPure_354_);
lean_dec_ref(v_toApplicative_353_);
v___x_355_ = lean_apply_2(v_toPure_354_, lean_box(0), v___x_351_);
return v___x_355_;
}
else
{
lean_object* v___f_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___f_356_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_356_, 0, v_f_346_);
v___x_357_ = lean_array_get_size(v_array_348_);
v___x_358_ = lean_nat_dec_le(v_stop_350_, v___x_357_);
if (v___x_358_ == 0)
{
uint8_t v___x_359_; 
lean_dec(v_stop_350_);
v___x_359_ = lean_nat_dec_lt(v_start_349_, v___x_357_);
if (v___x_359_ == 0)
{
lean_object* v_toApplicative_360_; lean_object* v_toPure_361_; lean_object* v___x_362_; 
lean_dec_ref(v___f_356_);
lean_dec(v_start_349_);
lean_dec_ref(v_array_348_);
v_toApplicative_360_ = lean_ctor_get(v_inst_345_, 0);
lean_inc_ref(v_toApplicative_360_);
lean_dec_ref(v_inst_345_);
v_toPure_361_ = lean_ctor_get(v_toApplicative_360_, 1);
lean_inc(v_toPure_361_);
lean_dec_ref(v_toApplicative_360_);
v___x_362_ = lean_apply_2(v_toPure_361_, lean_box(0), v___x_351_);
return v___x_362_;
}
else
{
size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_usize_of_nat(v_start_349_);
lean_dec(v_start_349_);
v___x_364_ = lean_usize_of_nat(v___x_357_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_345_, v___f_356_, v_array_348_, v___x_363_, v___x_364_, v___x_351_);
return v___x_365_;
}
}
else
{
size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_usize_of_nat(v_start_349_);
lean_dec(v_start_349_);
v___x_367_ = lean_usize_of_nat(v_stop_350_);
lean_dec(v_stop_350_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_345_, v___f_356_, v_array_348_, v___x_366_, v___x_367_, v___x_351_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM(lean_object* v_00_u03b1_369_, lean_object* v_m_370_, lean_object* v_inst_371_, lean_object* v_f_372_, lean_object* v_as_373_){
_start:
{
lean_object* v_array_374_; lean_object* v_start_375_; lean_object* v_stop_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_array_374_ = lean_ctor_get(v_as_373_, 0);
lean_inc_ref(v_array_374_);
v_start_375_ = lean_ctor_get(v_as_373_, 1);
lean_inc(v_start_375_);
v_stop_376_ = lean_ctor_get(v_as_373_, 2);
lean_inc(v_stop_376_);
lean_dec_ref(v_as_373_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_nat_dec_lt(v_start_375_, v_stop_376_);
if (v___x_378_ == 0)
{
lean_object* v_toApplicative_379_; lean_object* v_toPure_380_; lean_object* v___x_381_; 
lean_dec(v_stop_376_);
lean_dec(v_start_375_);
lean_dec_ref(v_array_374_);
lean_dec(v_f_372_);
v_toApplicative_379_ = lean_ctor_get(v_inst_371_, 0);
lean_inc_ref(v_toApplicative_379_);
lean_dec_ref(v_inst_371_);
v_toPure_380_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_380_);
lean_dec_ref(v_toApplicative_379_);
v___x_381_ = lean_apply_2(v_toPure_380_, lean_box(0), v___x_377_);
return v___x_381_;
}
else
{
lean_object* v___f_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___f_382_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_382_, 0, v_f_372_);
v___x_383_ = lean_array_get_size(v_array_374_);
v___x_384_ = lean_nat_dec_le(v_stop_376_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
lean_dec(v_stop_376_);
v___x_385_ = lean_nat_dec_lt(v_start_375_, v___x_383_);
if (v___x_385_ == 0)
{
lean_object* v_toApplicative_386_; lean_object* v_toPure_387_; lean_object* v___x_388_; 
lean_dec_ref(v___f_382_);
lean_dec(v_start_375_);
lean_dec_ref(v_array_374_);
v_toApplicative_386_ = lean_ctor_get(v_inst_371_, 0);
lean_inc_ref(v_toApplicative_386_);
lean_dec_ref(v_inst_371_);
v_toPure_387_ = lean_ctor_get(v_toApplicative_386_, 1);
lean_inc(v_toPure_387_);
lean_dec_ref(v_toApplicative_386_);
v___x_388_ = lean_apply_2(v_toPure_387_, lean_box(0), v___x_377_);
return v___x_388_;
}
else
{
size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_usize_of_nat(v_start_375_);
lean_dec(v_start_375_);
v___x_390_ = lean_usize_of_nat(v___x_383_);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_371_, v___f_382_, v_array_374_, v___x_389_, v___x_390_, v___x_377_);
return v___x_391_;
}
}
else
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_usize_of_nat(v_start_375_);
lean_dec(v_start_375_);
v___x_393_ = lean_usize_of_nat(v_stop_376_);
lean_dec(v_stop_376_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_371_, v___f_382_, v_array_374_, v___x_392_, v___x_393_, v___x_377_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg___lam__0(lean_object* v_f_395_, lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_apply_1(v_f_395_, v_a_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg(lean_object* v_inst_399_, lean_object* v_f_400_, lean_object* v_as_401_){
_start:
{
lean_object* v_array_402_; lean_object* v_start_403_; lean_object* v_stop_404_; lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_array_402_ = lean_ctor_get(v_as_401_, 0);
lean_inc_ref(v_array_402_);
v_start_403_ = lean_ctor_get(v_as_401_, 1);
lean_inc(v_start_403_);
v_stop_404_ = lean_ctor_get(v_as_401_, 2);
lean_inc(v_stop_404_);
lean_dec_ref(v_as_401_);
v___f_405_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_405_, 0, v_f_400_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_array_get_size(v_array_402_);
v___x_408_ = lean_nat_dec_le(v_stop_404_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
lean_dec(v_stop_404_);
v___x_409_ = lean_nat_dec_lt(v_start_403_, v___x_407_);
if (v___x_409_ == 0)
{
lean_object* v_toApplicative_410_; lean_object* v_toPure_411_; lean_object* v___x_412_; 
lean_dec_ref(v___f_405_);
lean_dec(v_start_403_);
lean_dec_ref(v_array_402_);
v_toApplicative_410_ = lean_ctor_get(v_inst_399_, 0);
lean_inc_ref(v_toApplicative_410_);
lean_dec_ref(v_inst_399_);
v_toPure_411_ = lean_ctor_get(v_toApplicative_410_, 1);
lean_inc(v_toPure_411_);
lean_dec_ref(v_toApplicative_410_);
v___x_412_ = lean_apply_2(v_toPure_411_, lean_box(0), v___x_406_);
return v___x_412_;
}
else
{
size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_usize_of_nat(v___x_407_);
v___x_414_ = lean_usize_of_nat(v_start_403_);
lean_dec(v_start_403_);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_399_, v___f_405_, v_array_402_, v___x_413_, v___x_414_, v___x_406_);
return v___x_415_;
}
}
else
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_lt(v_start_403_, v_stop_404_);
if (v___x_416_ == 0)
{
lean_object* v_toApplicative_417_; lean_object* v_toPure_418_; lean_object* v___x_419_; 
lean_dec_ref(v___f_405_);
lean_dec(v_stop_404_);
lean_dec(v_start_403_);
lean_dec_ref(v_array_402_);
v_toApplicative_417_ = lean_ctor_get(v_inst_399_, 0);
lean_inc_ref(v_toApplicative_417_);
lean_dec_ref(v_inst_399_);
v_toPure_418_ = lean_ctor_get(v_toApplicative_417_, 1);
lean_inc(v_toPure_418_);
lean_dec_ref(v_toApplicative_417_);
v___x_419_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_406_);
return v___x_419_;
}
else
{
size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_usize_of_nat(v_stop_404_);
lean_dec(v_stop_404_);
v___x_421_ = lean_usize_of_nat(v_start_403_);
lean_dec(v_start_403_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_399_, v___f_405_, v_array_402_, v___x_420_, v___x_421_, v___x_406_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM(lean_object* v_00_u03b1_423_, lean_object* v_m_424_, lean_object* v_inst_425_, lean_object* v_f_426_, lean_object* v_as_427_){
_start:
{
lean_object* v_array_428_; lean_object* v_start_429_; lean_object* v_stop_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_array_428_ = lean_ctor_get(v_as_427_, 0);
lean_inc_ref(v_array_428_);
v_start_429_ = lean_ctor_get(v_as_427_, 1);
lean_inc(v_start_429_);
v_stop_430_ = lean_ctor_get(v_as_427_, 2);
lean_inc(v_stop_430_);
lean_dec_ref(v_as_427_);
v___f_431_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_431_, 0, v_f_426_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_array_get_size(v_array_428_);
v___x_434_ = lean_nat_dec_le(v_stop_430_, v___x_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
lean_dec(v_stop_430_);
v___x_435_ = lean_nat_dec_lt(v_start_429_, v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v_toApplicative_436_; lean_object* v_toPure_437_; lean_object* v___x_438_; 
lean_dec_ref(v___f_431_);
lean_dec(v_start_429_);
lean_dec_ref(v_array_428_);
v_toApplicative_436_ = lean_ctor_get(v_inst_425_, 0);
lean_inc_ref(v_toApplicative_436_);
lean_dec_ref(v_inst_425_);
v_toPure_437_ = lean_ctor_get(v_toApplicative_436_, 1);
lean_inc(v_toPure_437_);
lean_dec_ref(v_toApplicative_436_);
v___x_438_ = lean_apply_2(v_toPure_437_, lean_box(0), v___x_432_);
return v___x_438_;
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_usize_of_nat(v___x_433_);
v___x_440_ = lean_usize_of_nat(v_start_429_);
lean_dec(v_start_429_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_425_, v___f_431_, v_array_428_, v___x_439_, v___x_440_, v___x_432_);
return v___x_441_;
}
}
else
{
uint8_t v___x_442_; 
v___x_442_ = lean_nat_dec_lt(v_start_429_, v_stop_430_);
if (v___x_442_ == 0)
{
lean_object* v_toApplicative_443_; lean_object* v_toPure_444_; lean_object* v___x_445_; 
lean_dec_ref(v___f_431_);
lean_dec(v_stop_430_);
lean_dec(v_start_429_);
lean_dec_ref(v_array_428_);
v_toApplicative_443_ = lean_ctor_get(v_inst_425_, 0);
lean_inc_ref(v_toApplicative_443_);
lean_dec_ref(v_inst_425_);
v_toPure_444_ = lean_ctor_get(v_toApplicative_443_, 1);
lean_inc(v_toPure_444_);
lean_dec_ref(v_toApplicative_443_);
v___x_445_ = lean_apply_2(v_toPure_444_, lean_box(0), v___x_432_);
return v___x_445_;
}
else
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_usize_of_nat(v_stop_430_);
lean_dec(v_stop_430_);
v___x_447_ = lean_usize_of_nat(v_start_429_);
lean_dec(v_start_429_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_425_, v___f_431_, v_array_428_, v___x_446_, v___x_447_, v___x_432_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg___lam__0(lean_object* v_f_449_, lean_object* v_x1_450_, lean_object* v_x2_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_apply_2(v_f_449_, v_x1_450_, v_x2_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg(lean_object* v_f_472_, lean_object* v_init_473_, lean_object* v_as_474_){
_start:
{
lean_object* v___x_475_; lean_object* v_array_476_; lean_object* v_start_477_; lean_object* v_stop_478_; lean_object* v___f_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_475_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_476_ = lean_ctor_get(v_as_474_, 0);
lean_inc_ref(v_array_476_);
v_start_477_ = lean_ctor_get(v_as_474_, 1);
lean_inc(v_start_477_);
v_stop_478_ = lean_ctor_get(v_as_474_, 2);
lean_inc(v_stop_478_);
lean_dec_ref(v_as_474_);
v___f_479_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_479_, 0, v_f_472_);
v___x_480_ = lean_array_get_size(v_array_476_);
v___x_481_ = lean_nat_dec_le(v_stop_478_, v___x_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
lean_dec(v_stop_478_);
v___x_482_ = lean_nat_dec_lt(v_start_477_, v___x_480_);
if (v___x_482_ == 0)
{
lean_dec_ref(v___f_479_);
lean_dec(v_start_477_);
lean_dec_ref(v_array_476_);
return v_init_473_;
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_usize_of_nat(v___x_480_);
v___x_484_ = lean_usize_of_nat(v_start_477_);
lean_dec(v_start_477_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_475_, v___f_479_, v_array_476_, v___x_483_, v___x_484_, v_init_473_);
return v___x_485_;
}
}
else
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_lt(v_start_477_, v_stop_478_);
if (v___x_486_ == 0)
{
lean_dec_ref(v___f_479_);
lean_dec(v_stop_478_);
lean_dec(v_start_477_);
lean_dec_ref(v_array_476_);
return v_init_473_;
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_usize_of_nat(v_stop_478_);
lean_dec(v_stop_478_);
v___x_488_ = lean_usize_of_nat(v_start_477_);
lean_dec(v_start_477_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_475_, v___f_479_, v_array_476_, v___x_487_, v___x_488_, v_init_473_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_f_492_, lean_object* v_init_493_, lean_object* v_as_494_){
_start:
{
lean_object* v___x_495_; lean_object* v_array_496_; lean_object* v_start_497_; lean_object* v_stop_498_; lean_object* v___f_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_495_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_496_ = lean_ctor_get(v_as_494_, 0);
lean_inc_ref(v_array_496_);
v_start_497_ = lean_ctor_get(v_as_494_, 1);
lean_inc(v_start_497_);
v_stop_498_ = lean_ctor_get(v_as_494_, 2);
lean_inc(v_stop_498_);
lean_dec_ref(v_as_494_);
v___f_499_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_499_, 0, v_f_492_);
v___x_500_ = lean_array_get_size(v_array_496_);
v___x_501_ = lean_nat_dec_le(v_stop_498_, v___x_500_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
lean_dec(v_stop_498_);
v___x_502_ = lean_nat_dec_lt(v_start_497_, v___x_500_);
if (v___x_502_ == 0)
{
lean_dec_ref(v___f_499_);
lean_dec(v_start_497_);
lean_dec_ref(v_array_496_);
return v_init_493_;
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_usize_of_nat(v___x_500_);
v___x_504_ = lean_usize_of_nat(v_start_497_);
lean_dec(v_start_497_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_495_, v___f_499_, v_array_496_, v___x_503_, v___x_504_, v_init_493_);
return v___x_505_;
}
}
else
{
uint8_t v___x_506_; 
v___x_506_ = lean_nat_dec_lt(v_start_497_, v_stop_498_);
if (v___x_506_ == 0)
{
lean_dec_ref(v___f_499_);
lean_dec(v_stop_498_);
lean_dec(v_start_497_);
lean_dec_ref(v_array_496_);
return v_init_493_;
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_usize_of_nat(v_stop_498_);
lean_dec(v_stop_498_);
v___x_508_ = lean_usize_of_nat(v_start_497_);
lean_dec(v_start_497_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_495_, v___f_499_, v_array_496_, v___x_507_, v___x_508_, v_init_493_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg___lam__0(lean_object* v_p_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_apply_1(v_p_510_, v_x_511_);
v___x_513_ = lean_unbox(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___lam__0___boxed(lean_object* v_p_514_, lean_object* v_x_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Subarray_any___redArg___lam__0(v_p_514_, v_x_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg(lean_object* v_p_518_, lean_object* v_as_519_){
_start:
{
lean_object* v___x_520_; lean_object* v_array_521_; lean_object* v_start_522_; lean_object* v_stop_523_; uint8_t v___x_524_; 
v___x_520_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_521_ = lean_ctor_get(v_as_519_, 0);
lean_inc_ref(v_array_521_);
v_start_522_ = lean_ctor_get(v_as_519_, 1);
lean_inc(v_start_522_);
v_stop_523_ = lean_ctor_get(v_as_519_, 2);
lean_inc(v_stop_523_);
lean_dec_ref(v_as_519_);
v___x_524_ = lean_nat_dec_lt(v_start_522_, v_stop_523_);
if (v___x_524_ == 0)
{
lean_dec(v_stop_523_);
lean_dec(v_start_522_);
lean_dec_ref(v_array_521_);
lean_dec_ref(v_p_518_);
return v___x_524_;
}
else
{
lean_object* v___f_525_; lean_object* v___y_527_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___f_525_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_525_, 0, v_p_518_);
v___x_533_ = lean_array_get_size(v_array_521_);
v___x_534_ = lean_nat_dec_le(v_stop_523_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec(v_stop_523_);
v___y_527_ = v___x_533_;
goto v___jp_526_;
}
else
{
v___y_527_ = v_stop_523_;
goto v___jp_526_;
}
v___jp_526_:
{
uint8_t v___x_528_; 
v___x_528_ = lean_nat_dec_lt(v_start_522_, v___y_527_);
if (v___x_528_ == 0)
{
lean_dec(v___y_527_);
lean_dec_ref(v___f_525_);
lean_dec(v_start_522_);
lean_dec_ref(v_array_521_);
return v___x_528_;
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = lean_usize_of_nat(v_start_522_);
lean_dec(v_start_522_);
v___x_530_ = lean_usize_of_nat(v___y_527_);
lean_dec(v___y_527_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_520_, v___f_525_, v_array_521_, v___x_529_, v___x_530_);
v___x_532_ = lean_unbox(v___x_531_);
lean_dec(v___x_531_);
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___boxed(lean_object* v_p_535_, lean_object* v_as_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Subarray_any___redArg(v_p_535_, v_as_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any(lean_object* v_00_u03b1_539_, lean_object* v_p_540_, lean_object* v_as_541_){
_start:
{
lean_object* v___x_542_; lean_object* v_array_543_; lean_object* v_start_544_; lean_object* v_stop_545_; uint8_t v___x_546_; 
v___x_542_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_543_ = lean_ctor_get(v_as_541_, 0);
lean_inc_ref(v_array_543_);
v_start_544_ = lean_ctor_get(v_as_541_, 1);
lean_inc(v_start_544_);
v_stop_545_ = lean_ctor_get(v_as_541_, 2);
lean_inc(v_stop_545_);
lean_dec_ref(v_as_541_);
v___x_546_ = lean_nat_dec_lt(v_start_544_, v_stop_545_);
if (v___x_546_ == 0)
{
lean_dec(v_stop_545_);
lean_dec(v_start_544_);
lean_dec_ref(v_array_543_);
lean_dec_ref(v_p_540_);
return v___x_546_;
}
else
{
lean_object* v___f_547_; lean_object* v___y_549_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___f_547_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_547_, 0, v_p_540_);
v___x_555_ = lean_array_get_size(v_array_543_);
v___x_556_ = lean_nat_dec_le(v_stop_545_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_stop_545_);
v___y_549_ = v___x_555_;
goto v___jp_548_;
}
else
{
v___y_549_ = v_stop_545_;
goto v___jp_548_;
}
v___jp_548_:
{
uint8_t v___x_550_; 
v___x_550_ = lean_nat_dec_lt(v_start_544_, v___y_549_);
if (v___x_550_ == 0)
{
lean_dec(v___y_549_);
lean_dec_ref(v___f_547_);
lean_dec(v_start_544_);
lean_dec_ref(v_array_543_);
return v___x_550_;
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_551_ = lean_usize_of_nat(v_start_544_);
lean_dec(v_start_544_);
v___x_552_ = lean_usize_of_nat(v___y_549_);
lean_dec(v___y_549_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_542_, v___f_547_, v_array_543_, v___x_551_, v___x_552_);
v___x_554_ = lean_unbox(v___x_553_);
lean_dec(v___x_553_);
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___boxed(lean_object* v_00_u03b1_557_, lean_object* v_p_558_, lean_object* v_as_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Subarray_any(v_00_u03b1_557_, v_p_558_, v_as_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg___lam__0(lean_object* v_p_562_, uint8_t v___x_563_, lean_object* v_v_564_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_apply_1(v_p_562_, v_v_564_);
v___x_566_ = lean_unbox(v___x_565_);
if (v___x_566_ == 0)
{
return v___x_563_;
}
else
{
uint8_t v___x_567_; 
v___x_567_ = 0;
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object* v_p_568_, lean_object* v___x_569_, lean_object* v_v_570_){
_start:
{
uint8_t v___x_342__boxed_571_; uint8_t v_res_572_; lean_object* v_r_573_; 
v___x_342__boxed_571_ = lean_unbox(v___x_569_);
v_res_572_ = l_Subarray_all___redArg___lam__0(v_p_568_, v___x_342__boxed_571_, v_v_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg(lean_object* v_p_574_, lean_object* v_as_575_){
_start:
{
lean_object* v___x_576_; lean_object* v_array_577_; lean_object* v_start_578_; lean_object* v_stop_579_; uint8_t v___x_580_; 
v___x_576_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_577_ = lean_ctor_get(v_as_575_, 0);
lean_inc_ref(v_array_577_);
v_start_578_ = lean_ctor_get(v_as_575_, 1);
lean_inc(v_start_578_);
v_stop_579_ = lean_ctor_get(v_as_575_, 2);
lean_inc(v_stop_579_);
lean_dec_ref(v_as_575_);
v___x_580_ = lean_nat_dec_lt(v_start_578_, v_stop_579_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; 
lean_dec(v_stop_579_);
lean_dec(v_start_578_);
lean_dec_ref(v_array_577_);
lean_dec_ref(v_p_574_);
v___x_581_ = 1;
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___y_585_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_582_ = lean_box(v___x_580_);
v___f_583_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_583_, 0, v_p_574_);
lean_closure_set(v___f_583_, 1, v___x_582_);
v___x_592_ = lean_array_get_size(v_array_577_);
v___x_593_ = lean_nat_dec_le(v_stop_579_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v_stop_579_);
v___y_585_ = v___x_592_;
goto v___jp_584_;
}
else
{
v___y_585_ = v_stop_579_;
goto v___jp_584_;
}
v___jp_584_:
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_start_578_, v___y_585_);
if (v___x_586_ == 0)
{
lean_dec(v___y_585_);
lean_dec_ref(v___f_583_);
lean_dec(v_start_578_);
lean_dec_ref(v_array_577_);
return v___x_580_;
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_587_ = lean_usize_of_nat(v_start_578_);
lean_dec(v_start_578_);
v___x_588_ = lean_usize_of_nat(v___y_585_);
lean_dec(v___y_585_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_576_, v___f_583_, v_array_577_, v___x_587_, v___x_588_);
v___x_590_ = lean_unbox(v___x_589_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
return v___x_586_;
}
else
{
uint8_t v___x_591_; 
v___x_591_ = 0;
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___boxed(lean_object* v_p_594_, lean_object* v_as_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Subarray_all___redArg(v_p_594_, v_as_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all(lean_object* v_00_u03b1_598_, lean_object* v_p_599_, lean_object* v_as_600_){
_start:
{
lean_object* v___x_601_; lean_object* v_array_602_; lean_object* v_start_603_; lean_object* v_stop_604_; uint8_t v___x_605_; 
v___x_601_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_602_ = lean_ctor_get(v_as_600_, 0);
lean_inc_ref(v_array_602_);
v_start_603_ = lean_ctor_get(v_as_600_, 1);
lean_inc(v_start_603_);
v_stop_604_ = lean_ctor_get(v_as_600_, 2);
lean_inc(v_stop_604_);
lean_dec_ref(v_as_600_);
v___x_605_ = lean_nat_dec_lt(v_start_603_, v_stop_604_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; 
lean_dec(v_stop_604_);
lean_dec(v_start_603_);
lean_dec_ref(v_array_602_);
lean_dec_ref(v_p_599_);
v___x_606_ = 1;
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___f_608_; lean_object* v___y_610_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_607_ = lean_box(v___x_605_);
v___f_608_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_608_, 0, v_p_599_);
lean_closure_set(v___f_608_, 1, v___x_607_);
v___x_617_ = lean_array_get_size(v_array_602_);
v___x_618_ = lean_nat_dec_le(v_stop_604_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_stop_604_);
v___y_610_ = v___x_617_;
goto v___jp_609_;
}
else
{
v___y_610_ = v_stop_604_;
goto v___jp_609_;
}
v___jp_609_:
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_lt(v_start_603_, v___y_610_);
if (v___x_611_ == 0)
{
lean_dec(v___y_610_);
lean_dec_ref(v___f_608_);
lean_dec(v_start_603_);
lean_dec_ref(v_array_602_);
return v___x_605_;
}
else
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_612_ = lean_usize_of_nat(v_start_603_);
lean_dec(v_start_603_);
v___x_613_ = lean_usize_of_nat(v___y_610_);
lean_dec(v___y_610_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_601_, v___f_608_, v_array_602_, v___x_612_, v___x_613_);
v___x_615_ = lean_unbox(v___x_614_);
lean_dec(v___x_614_);
if (v___x_615_ == 0)
{
return v___x_611_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___boxed(lean_object* v_00_u03b1_619_, lean_object* v_p_620_, lean_object* v_as_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Subarray_all(v_00_u03b1_619_, v_p_620_, v_as_621_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_624_, lean_object* v_as_625_, lean_object* v_f_626_, lean_object* v_n_627_, lean_object* v_toPure_628_, lean_object* v_r_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(v_inst_624_, v_as_625_, v_f_626_, v_n_627_, v_toPure_628_, v_r_629_);
lean_dec(v_n_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(lean_object* v_inst_631_, lean_object* v_as_632_, lean_object* v_f_633_, lean_object* v_i_634_){
_start:
{
lean_object* v_toApplicative_635_; lean_object* v_toBind_636_; lean_object* v_toPure_637_; lean_object* v_zero_638_; uint8_t v_isZero_639_; 
v_toApplicative_635_ = lean_ctor_get(v_inst_631_, 0);
v_toBind_636_ = lean_ctor_get(v_inst_631_, 1);
lean_inc(v_toBind_636_);
v_toPure_637_ = lean_ctor_get(v_toApplicative_635_, 1);
lean_inc(v_toPure_637_);
v_zero_638_ = lean_unsigned_to_nat(0u);
v_isZero_639_ = lean_nat_dec_eq(v_i_634_, v_zero_638_);
if (v_isZero_639_ == 1)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_toBind_636_);
lean_dec(v_f_633_);
lean_dec_ref(v_as_632_);
lean_dec_ref(v_inst_631_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_640_);
return v___x_641_;
}
else
{
lean_object* v_one_642_; lean_object* v_n_643_; lean_object* v___f_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_one_642_ = lean_unsigned_to_nat(1u);
v_n_643_ = lean_nat_sub(v_i_634_, v_one_642_);
lean_inc(v_n_643_);
lean_inc(v_f_633_);
lean_inc_ref(v_as_632_);
v___f_644_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_644_, 0, v_inst_631_);
lean_closure_set(v___f_644_, 1, v_as_632_);
lean_closure_set(v___f_644_, 2, v_f_633_);
lean_closure_set(v___f_644_, 3, v_n_643_);
lean_closure_set(v___f_644_, 4, v_toPure_637_);
v___x_645_ = l_Subarray_get___redArg(v_as_632_, v_n_643_);
lean_dec(v_n_643_);
lean_dec_ref(v_as_632_);
v___x_646_ = lean_apply_1(v_f_633_, v___x_645_);
v___x_647_ = lean_apply_4(v_toBind_636_, lean_box(0), lean_box(0), v___x_646_, v___f_644_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_648_, lean_object* v_as_649_, lean_object* v_f_650_, lean_object* v_n_651_, lean_object* v_toPure_652_, lean_object* v_r_653_){
_start:
{
if (lean_obj_tag(v_r_653_) == 0)
{
lean_object* v___x_654_; 
lean_dec(v_toPure_652_);
v___x_654_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_648_, v_as_649_, v_f_650_, v_n_651_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; 
lean_dec(v_f_650_);
lean_dec_ref(v_as_649_);
lean_dec_ref(v_inst_648_);
v___x_655_ = lean_apply_2(v_toPure_652_, lean_box(0), v_r_653_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_656_, lean_object* v_as_657_, lean_object* v_f_658_, lean_object* v_i_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_656_, v_as_657_, v_f_658_, v_i_659_);
lean_dec(v_i_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_m_663_, lean_object* v_inst_664_, lean_object* v_as_665_, lean_object* v_f_666_, lean_object* v_i_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_664_, v_as_665_, v_f_666_, v_i_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_as_674_, lean_object* v_f_675_, lean_object* v_i_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(v_00_u03b1_670_, v_00_u03b2_671_, v_m_672_, v_inst_673_, v_as_674_, v_f_675_, v_i_676_, v_a_677_);
lean_dec(v_i_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f___redArg(lean_object* v_inst_679_, lean_object* v_as_680_, lean_object* v_f_681_){
_start:
{
lean_object* v_start_682_; lean_object* v_stop_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_start_682_ = lean_ctor_get(v_as_680_, 1);
v_stop_683_ = lean_ctor_get(v_as_680_, 2);
v___x_684_ = lean_nat_sub(v_stop_683_, v_start_682_);
v___x_685_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_679_, v_as_680_, v_f_681_, v___x_684_);
lean_dec(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_m_688_, lean_object* v_inst_689_, lean_object* v_as_690_, lean_object* v_f_691_){
_start:
{
lean_object* v_start_692_; lean_object* v_stop_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_start_692_ = lean_ctor_get(v_as_690_, 1);
v_stop_693_ = lean_ctor_get(v_as_690_, 2);
v___x_694_ = lean_nat_sub(v_stop_693_, v_start_692_);
v___x_695_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_689_, v_as_690_, v_f_691_, v___x_694_);
lean_dec(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_696_, lean_object* v_a_697_, uint8_t v_____do__lift_698_){
_start:
{
if (v_____do__lift_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v_a_697_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_apply_2(v_toPure_696_, lean_box(0), v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v_a_697_);
v___x_702_ = lean_apply_2(v_toPure_696_, lean_box(0), v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_703_, lean_object* v_a_704_, lean_object* v_____do__lift_705_){
_start:
{
uint8_t v_____do__lift_77__boxed_706_; lean_object* v_res_707_; 
v_____do__lift_77__boxed_706_ = lean_unbox(v_____do__lift_705_);
v_res_707_ = l_Subarray_findRevM_x3f___redArg___lam__0(v_toPure_703_, v_a_704_, v_____do__lift_77__boxed_706_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_708_, lean_object* v_p_709_, lean_object* v_toBind_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc(v_a_711_);
v___f_712_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_712_, 0, v_toPure_708_);
lean_closure_set(v___f_712_, 1, v_a_711_);
v___x_713_ = lean_apply_1(v_p_709_, v_a_711_);
v___x_714_ = lean_apply_4(v_toBind_710_, lean_box(0), lean_box(0), v___x_713_, v___f_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg(lean_object* v_inst_715_, lean_object* v_as_716_, lean_object* v_p_717_){
_start:
{
lean_object* v_toApplicative_718_; lean_object* v_toBind_719_; lean_object* v_toPure_720_; lean_object* v_start_721_; lean_object* v_stop_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_715_, 0);
v_toBind_719_ = lean_ctor_get(v_inst_715_, 1);
v_toPure_720_ = lean_ctor_get(v_toApplicative_718_, 1);
v_start_721_ = lean_ctor_get(v_as_716_, 1);
v_stop_722_ = lean_ctor_get(v_as_716_, 2);
lean_inc(v_toBind_719_);
lean_inc(v_toPure_720_);
v___f_723_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_723_, 0, v_toPure_720_);
lean_closure_set(v___f_723_, 1, v_p_717_);
lean_closure_set(v___f_723_, 2, v_toBind_719_);
v___x_724_ = lean_nat_sub(v_stop_722_, v_start_721_);
v___x_725_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_715_, v_as_716_, v___f_723_, v___x_724_);
lean_dec(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f(lean_object* v_00_u03b1_726_, lean_object* v_m_727_, lean_object* v_inst_728_, lean_object* v_as_729_, lean_object* v_p_730_){
_start:
{
lean_object* v_toApplicative_731_; lean_object* v_toBind_732_; lean_object* v_toPure_733_; lean_object* v_start_734_; lean_object* v_stop_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_toApplicative_731_ = lean_ctor_get(v_inst_728_, 0);
v_toBind_732_ = lean_ctor_get(v_inst_728_, 1);
v_toPure_733_ = lean_ctor_get(v_toApplicative_731_, 1);
v_start_734_ = lean_ctor_get(v_as_729_, 1);
v_stop_735_ = lean_ctor_get(v_as_729_, 2);
lean_inc(v_toBind_732_);
lean_inc(v_toPure_733_);
v___f_736_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_736_, 0, v_toPure_733_);
lean_closure_set(v___f_736_, 1, v_p_730_);
lean_closure_set(v___f_736_, 2, v_toBind_732_);
v___x_737_ = lean_nat_sub(v_stop_735_, v_start_734_);
v___x_738_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_728_, v_as_729_, v___f_736_, v___x_737_);
lean_dec(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg___lam__0(lean_object* v_p_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
lean_inc(v_a_740_);
v___x_741_ = lean_apply_1(v_p_739_, v_a_740_);
v___x_742_ = lean_unbox(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_a_740_);
v___x_743_ = lean_box(0);
return v___x_743_;
}
else
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_a_740_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg(lean_object* v_as_745_, lean_object* v_p_746_){
_start:
{
lean_object* v___x_747_; lean_object* v_start_748_; lean_object* v_stop_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_748_ = lean_ctor_get(v_as_745_, 1);
v_stop_749_ = lean_ctor_get(v_as_745_, 2);
v___f_750_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_750_, 0, v_p_746_);
v___x_751_ = lean_nat_sub(v_stop_749_, v_start_748_);
v___x_752_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_747_, v_as_745_, v___f_750_, v___x_751_);
lean_dec(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f(lean_object* v_00_u03b1_753_, lean_object* v_as_754_, lean_object* v_p_755_){
_start:
{
lean_object* v___x_756_; lean_object* v_start_757_; lean_object* v_stop_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_756_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_757_ = lean_ctor_get(v_as_754_, 1);
v_stop_758_ = lean_ctor_get(v_as_754_, 2);
v___f_759_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_759_, 0, v_p_755_);
v___x_760_ = lean_nat_sub(v_stop_758_, v_start_757_);
v___x_761_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_756_, v_as_754_, v___f_759_, v___x_760_);
lean_dec(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray___redArg(lean_object* v_as_762_, lean_object* v_start_763_, lean_object* v_stop_764_){
_start:
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = lean_array_get_size(v_as_762_);
v___x_766_ = lean_nat_dec_le(v_stop_764_, v___x_765_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
lean_dec(v_stop_764_);
v___x_767_ = lean_nat_dec_le(v_start_763_, v___x_765_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec(v_start_763_);
v___x_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_768_, 0, v_as_762_);
lean_ctor_set(v___x_768_, 1, v___x_765_);
lean_ctor_set(v___x_768_, 2, v___x_765_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v_as_762_);
lean_ctor_set(v___x_769_, 1, v_start_763_);
lean_ctor_set(v___x_769_, 2, v___x_765_);
return v___x_769_;
}
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_nat_dec_le(v_start_763_, v_stop_764_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec(v_start_763_);
lean_inc(v_stop_764_);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v_as_762_);
lean_ctor_set(v___x_771_, 1, v_stop_764_);
lean_ctor_set(v___x_771_, 2, v_stop_764_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v_as_762_);
lean_ctor_set(v___x_772_, 1, v_start_763_);
lean_ctor_set(v___x_772_, 2, v_stop_764_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray(lean_object* v_00_u03b1_773_, lean_object* v_as_774_, lean_object* v_start_775_, lean_object* v_stop_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Array_toSubarray___redArg(v_as_774_, v_start_775_, v_stop_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5));
v___x_895_ = l_String_toRawSubstring_x27(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(lean_object* v_x_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = ((lean_object*)(l_Array_term_____x5b___x3a___x5d___closed__2));
lean_inc(v_x_909_);
v___x_913_ = l_Lean_Syntax_isOfKind(v_x_909_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref(v_a_910_);
lean_dec(v_x_909_);
v___x_914_ = lean_box(1);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_a_911_);
return v___x_915_;
}
else
{
lean_object* v_quotContext_916_; lean_object* v_currMacroScope_917_; lean_object* v_ref_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_quotContext_916_ = lean_ctor_get(v_a_910_, 1);
lean_inc(v_quotContext_916_);
v_currMacroScope_917_ = lean_ctor_get(v_a_910_, 2);
lean_inc(v_currMacroScope_917_);
v_ref_918_ = lean_ctor_get(v_a_910_, 5);
lean_inc(v_ref_918_);
lean_dec_ref(v_a_910_);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = l_Lean_Syntax_getArg(v_x_909_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(2u);
v___x_922_ = l_Lean_Syntax_getArg(v_x_909_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(4u);
v___x_924_ = l_Lean_Syntax_getArg(v_x_909_, v___x_923_);
lean_dec(v_x_909_);
v___x_925_ = 0;
v___x_926_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_925_);
lean_dec(v_ref_918_);
v___x_927_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_928_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_929_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
v___x_930_ = l_Lean_addMacroScope(v_quotContext_916_, v___x_929_, v_currMacroScope_917_);
v___x_931_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc(v___x_926_);
v___x_932_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_932_, 0, v___x_926_);
lean_ctor_set(v___x_932_, 1, v___x_928_);
lean_ctor_set(v___x_932_, 2, v___x_930_);
lean_ctor_set(v___x_932_, 3, v___x_931_);
v___x_933_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
lean_inc(v___x_926_);
v___x_934_ = l_Lean_Syntax_node3(v___x_926_, v___x_933_, v___x_920_, v___x_922_, v___x_924_);
v___x_935_ = l_Lean_Syntax_node2(v___x_926_, v___x_927_, v___x_932_, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_a_911_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object* v_x_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = ((lean_object*)(l_Array_term_____x5b_x3a___x5d___closed__1));
lean_inc(v_x_941_);
v___x_945_ = l_Lean_Syntax_isOfKind(v_x_941_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref(v_a_942_);
lean_dec(v_x_941_);
v___x_946_ = lean_box(1);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_943_);
return v___x_947_;
}
else
{
lean_object* v_quotContext_948_; lean_object* v_currMacroScope_949_; lean_object* v_ref_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_quotContext_948_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_quotContext_948_);
v_currMacroScope_949_ = lean_ctor_get(v_a_942_, 2);
lean_inc(v_currMacroScope_949_);
v_ref_950_ = lean_ctor_get(v_a_942_, 5);
lean_inc(v_ref_950_);
lean_dec_ref(v_a_942_);
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = l_Lean_Syntax_getArg(v_x_941_, v___x_951_);
v___x_953_ = lean_unsigned_to_nat(3u);
v___x_954_ = l_Lean_Syntax_getArg(v_x_941_, v___x_953_);
lean_dec(v_x_941_);
v___x_955_ = 0;
v___x_956_ = l_Lean_SourceInfo_fromRef(v_ref_950_, v___x_955_);
lean_dec(v_ref_950_);
v___x_957_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_958_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_959_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
v___x_960_ = l_Lean_addMacroScope(v_quotContext_948_, v___x_959_, v_currMacroScope_949_);
v___x_961_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc(v___x_956_);
v___x_962_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_962_, 0, v___x_956_);
lean_ctor_set(v___x_962_, 1, v___x_958_);
lean_ctor_set(v___x_962_, 2, v___x_960_);
lean_ctor_set(v___x_962_, 3, v___x_961_);
v___x_963_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_964_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1));
v___x_965_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2));
lean_inc(v___x_956_);
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_956_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_inc(v___x_956_);
v___x_967_ = l_Lean_Syntax_node1(v___x_956_, v___x_964_, v___x_966_);
lean_inc(v___x_956_);
v___x_968_ = l_Lean_Syntax_node3(v___x_956_, v___x_963_, v___x_952_, v___x_967_, v___x_954_);
v___x_969_ = l_Lean_Syntax_node2(v___x_956_, v___x_957_, v___x_962_, v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v_a_943_);
return v___x_970_;
}
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Array_mkArray0(lean_box(0));
return v___x_983_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11));
v___x_1004_ = l_String_toRawSubstring_x27(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18));
v___x_1017_ = l_String_toRawSubstring_x27(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(lean_object* v_x_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Array_term_____x5b___x3a_x5d___closed__1));
lean_inc(v_x_1022_);
v___x_1026_ = l_Lean_Syntax_isOfKind(v_x_1022_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_a_1023_);
lean_dec(v_x_1022_);
v___x_1027_ = lean_box(1);
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_a_1024_);
return v___x_1028_;
}
else
{
lean_object* v_quotContext_1029_; lean_object* v_currMacroScope_1030_; lean_object* v_ref_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_quotContext_1029_ = lean_ctor_get(v_a_1023_, 1);
lean_inc(v_quotContext_1029_);
v_currMacroScope_1030_ = lean_ctor_get(v_a_1023_, 2);
lean_inc(v_currMacroScope_1030_);
v_ref_1031_ = lean_ctor_get(v_a_1023_, 5);
lean_inc(v_ref_1031_);
lean_dec_ref(v_a_1023_);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = l_Lean_Syntax_getArg(v_x_1022_, v___x_1032_);
v___x_1034_ = lean_unsigned_to_nat(2u);
v___x_1035_ = l_Lean_Syntax_getArg(v_x_1022_, v___x_1034_);
lean_dec(v_x_1022_);
v___x_1036_ = 0;
v___x_1037_ = l_Lean_SourceInfo_fromRef(v_ref_1031_, v___x_1036_);
lean_dec(v_ref_1031_);
v___x_1038_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0));
v___x_1039_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1));
lean_inc(v___x_1037_);
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1038_);
v___x_1041_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3));
v___x_1042_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_1043_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
lean_inc(v___x_1037_);
v___x_1044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1037_);
lean_ctor_set(v___x_1044_, 1, v___x_1042_);
lean_ctor_set(v___x_1044_, 2, v___x_1043_);
lean_inc_ref(v___x_1044_);
lean_inc(v___x_1037_);
v___x_1045_ = l_Lean_Syntax_node1(v___x_1037_, v___x_1041_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6));
v___x_1047_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8));
v___x_1048_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10));
v___x_1049_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
v___x_1050_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13));
lean_inc(v_currMacroScope_1030_);
lean_inc(v_quotContext_1029_);
v___x_1051_ = l_Lean_addMacroScope(v_quotContext_1029_, v___x_1050_, v_currMacroScope_1030_);
v___x_1052_ = lean_box(0);
lean_inc(v___x_1037_);
v___x_1053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1037_);
lean_ctor_set(v___x_1053_, 1, v___x_1049_);
lean_ctor_set(v___x_1053_, 2, v___x_1051_);
lean_ctor_set(v___x_1053_, 3, v___x_1052_);
lean_inc_ref(v___x_1053_);
lean_inc(v___x_1037_);
v___x_1054_ = l_Lean_Syntax_node1(v___x_1037_, v___x_1048_, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14));
lean_inc(v___x_1037_);
v___x_1056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1037_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_inc_ref(v___x_1044_);
lean_inc(v___x_1037_);
v___x_1057_ = l_Lean_Syntax_node5(v___x_1037_, v___x_1047_, v___x_1054_, v___x_1044_, v___x_1044_, v___x_1056_, v___x_1033_);
lean_inc(v___x_1037_);
v___x_1058_ = l_Lean_Syntax_node1(v___x_1037_, v___x_1046_, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15));
lean_inc(v___x_1037_);
v___x_1060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1037_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_1062_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_1063_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_1030_);
lean_inc(v_quotContext_1029_);
v___x_1064_ = l_Lean_addMacroScope(v_quotContext_1029_, v___x_1063_, v_currMacroScope_1030_);
v___x_1065_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17));
lean_inc(v___x_1037_);
v___x_1066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1037_);
lean_ctor_set(v___x_1066_, 1, v___x_1062_);
lean_ctor_set(v___x_1066_, 2, v___x_1064_);
lean_ctor_set(v___x_1066_, 3, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
v___x_1068_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21));
v___x_1069_ = l_Lean_addMacroScope(v_quotContext_1029_, v___x_1068_, v_currMacroScope_1030_);
lean_inc(v___x_1037_);
v___x_1070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1037_);
lean_ctor_set(v___x_1070_, 1, v___x_1067_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set(v___x_1070_, 3, v___x_1052_);
lean_inc(v___x_1037_);
v___x_1071_ = l_Lean_Syntax_node3(v___x_1037_, v___x_1042_, v___x_1053_, v___x_1035_, v___x_1070_);
lean_inc(v___x_1037_);
v___x_1072_ = l_Lean_Syntax_node2(v___x_1037_, v___x_1061_, v___x_1066_, v___x_1071_);
v___x_1073_ = l_Lean_Syntax_node5(v___x_1037_, v___x_1039_, v___x_1040_, v___x_1045_, v___x_1058_, v___x_1060_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_1024_);
return v___x_1074_;
}
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Subarray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Subarray(builtin);
}
#ifdef __cplusplus
}
#endif
