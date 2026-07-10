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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT uint8_t l_Subarray_all___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_bool_not(v_____do__lift_250_);
v___x_252_ = lean_box(v___x_251_);
v___x_253_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0___boxed(lean_object* v_toPure_254_, lean_object* v_____do__lift_255_){
_start:
{
uint8_t v_____do__lift_99__boxed_256_; lean_object* v_res_257_; 
v_____do__lift_99__boxed_256_ = lean_unbox(v_____do__lift_255_);
v_res_257_ = l_Subarray_allM___redArg___lam__0(v_toPure_254_, v_____do__lift_99__boxed_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__2(lean_object* v_p_258_, lean_object* v_toBind_259_, lean_object* v___f_260_, lean_object* v_v_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_apply_1(v_p_258_, v_v_261_);
v___x_263_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_262_, v___f_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg(lean_object* v_inst_264_, lean_object* v_p_265_, lean_object* v_as_266_){
_start:
{
lean_object* v_toApplicative_267_; lean_object* v_array_268_; lean_object* v_start_269_; lean_object* v_stop_270_; lean_object* v_toBind_271_; lean_object* v_toPure_272_; lean_object* v___f_273_; uint8_t v___x_274_; 
v_toApplicative_267_ = lean_ctor_get(v_inst_264_, 0);
v_array_268_ = lean_ctor_get(v_as_266_, 0);
lean_inc_ref(v_array_268_);
v_start_269_ = lean_ctor_get(v_as_266_, 1);
lean_inc(v_start_269_);
v_stop_270_ = lean_ctor_get(v_as_266_, 2);
lean_inc(v_stop_270_);
lean_dec_ref(v_as_266_);
v_toBind_271_ = lean_ctor_get(v_inst_264_, 1);
lean_inc(v_toBind_271_);
v_toPure_272_ = lean_ctor_get(v_toApplicative_267_, 1);
lean_inc(v_toPure_272_);
v___f_273_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_273_, 0, v_toPure_272_);
v___x_274_ = lean_nat_dec_lt(v_start_269_, v_stop_270_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_inc(v_toPure_272_);
lean_dec(v_stop_270_);
lean_dec(v_start_269_);
lean_dec_ref(v_array_268_);
lean_dec(v_p_265_);
lean_dec_ref(v_inst_264_);
v___x_275_ = lean_box(v___x_274_);
v___x_276_ = lean_apply_2(v_toPure_272_, lean_box(0), v___x_275_);
v___x_277_ = lean_apply_4(v_toBind_271_, lean_box(0), lean_box(0), v___x_276_, v___f_273_);
return v___x_277_;
}
else
{
lean_object* v___f_278_; lean_object* v___y_280_; lean_object* v___x_289_; uint8_t v___x_290_; 
lean_inc_ref(v___f_273_);
lean_inc(v_toBind_271_);
v___f_278_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_278_, 0, v_p_265_);
lean_closure_set(v___f_278_, 1, v_toBind_271_);
lean_closure_set(v___f_278_, 2, v___f_273_);
v___x_289_ = lean_array_get_size(v_array_268_);
v___x_290_ = lean_nat_dec_le(v_stop_270_, v___x_289_);
if (v___x_290_ == 0)
{
lean_dec(v_stop_270_);
v___y_280_ = v___x_289_;
goto v___jp_279_;
}
else
{
v___y_280_ = v_stop_270_;
goto v___jp_279_;
}
v___jp_279_:
{
uint8_t v___x_281_; 
v___x_281_ = lean_nat_dec_lt(v_start_269_, v___y_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc(v_toPure_272_);
lean_dec(v___y_280_);
lean_dec_ref(v___f_278_);
lean_dec(v_start_269_);
lean_dec_ref(v_array_268_);
lean_dec_ref(v_inst_264_);
v___x_282_ = lean_box(v___x_281_);
v___x_283_ = lean_apply_2(v_toPure_272_, lean_box(0), v___x_282_);
v___x_284_ = lean_apply_4(v_toBind_271_, lean_box(0), lean_box(0), v___x_283_, v___f_273_);
return v___x_284_;
}
else
{
size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_usize_of_nat(v_start_269_);
lean_dec(v_start_269_);
v___x_286_ = lean_usize_of_nat(v___y_280_);
lean_dec(v___y_280_);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_264_, v___f_278_, v_array_268_, v___x_285_, v___x_286_);
v___x_288_ = lean_apply_4(v_toBind_271_, lean_box(0), lean_box(0), v___x_287_, v___f_273_);
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM(lean_object* v_00_u03b1_291_, lean_object* v_m_292_, lean_object* v_inst_293_, lean_object* v_p_294_, lean_object* v_as_295_){
_start:
{
lean_object* v_toApplicative_296_; lean_object* v_array_297_; lean_object* v_start_298_; lean_object* v_stop_299_; lean_object* v_toBind_300_; lean_object* v_toPure_301_; lean_object* v___f_302_; uint8_t v___x_303_; 
v_toApplicative_296_ = lean_ctor_get(v_inst_293_, 0);
v_array_297_ = lean_ctor_get(v_as_295_, 0);
lean_inc_ref(v_array_297_);
v_start_298_ = lean_ctor_get(v_as_295_, 1);
lean_inc(v_start_298_);
v_stop_299_ = lean_ctor_get(v_as_295_, 2);
lean_inc(v_stop_299_);
lean_dec_ref(v_as_295_);
v_toBind_300_ = lean_ctor_get(v_inst_293_, 1);
lean_inc(v_toBind_300_);
v_toPure_301_ = lean_ctor_get(v_toApplicative_296_, 1);
lean_inc(v_toPure_301_);
v___f_302_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_302_, 0, v_toPure_301_);
v___x_303_ = lean_nat_dec_lt(v_start_298_, v_stop_299_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc(v_toPure_301_);
lean_dec(v_stop_299_);
lean_dec(v_start_298_);
lean_dec_ref(v_array_297_);
lean_dec(v_p_294_);
lean_dec_ref(v_inst_293_);
v___x_304_ = lean_box(v___x_303_);
v___x_305_ = lean_apply_2(v_toPure_301_, lean_box(0), v___x_304_);
v___x_306_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_305_, v___f_302_);
return v___x_306_;
}
else
{
lean_object* v___f_307_; lean_object* v___y_309_; lean_object* v___x_318_; uint8_t v___x_319_; 
lean_inc_ref(v___f_302_);
lean_inc(v_toBind_300_);
v___f_307_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_307_, 0, v_p_294_);
lean_closure_set(v___f_307_, 1, v_toBind_300_);
lean_closure_set(v___f_307_, 2, v___f_302_);
v___x_318_ = lean_array_get_size(v_array_297_);
v___x_319_ = lean_nat_dec_le(v_stop_299_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec(v_stop_299_);
v___y_309_ = v___x_318_;
goto v___jp_308_;
}
else
{
v___y_309_ = v_stop_299_;
goto v___jp_308_;
}
v___jp_308_:
{
uint8_t v___x_310_; 
v___x_310_ = lean_nat_dec_lt(v_start_298_, v___y_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc(v_toPure_301_);
lean_dec(v___y_309_);
lean_dec_ref(v___f_307_);
lean_dec(v_start_298_);
lean_dec_ref(v_array_297_);
lean_dec_ref(v_inst_293_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_apply_2(v_toPure_301_, lean_box(0), v___x_311_);
v___x_313_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_312_, v___f_302_);
return v___x_313_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = lean_usize_of_nat(v_start_298_);
lean_dec(v_start_298_);
v___x_315_ = lean_usize_of_nat(v___y_309_);
lean_dec(v___y_309_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_293_, v___f_307_, v_array_297_, v___x_314_, v___x_315_);
v___x_317_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_316_, v___f_302_);
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg___lam__0(lean_object* v_f_320_, lean_object* v_x_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_apply_1(v_f_320_, v___y_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg(lean_object* v_inst_324_, lean_object* v_f_325_, lean_object* v_as_326_){
_start:
{
lean_object* v_array_327_; lean_object* v_start_328_; lean_object* v_stop_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_array_327_ = lean_ctor_get(v_as_326_, 0);
lean_inc_ref(v_array_327_);
v_start_328_ = lean_ctor_get(v_as_326_, 1);
lean_inc(v_start_328_);
v_stop_329_ = lean_ctor_get(v_as_326_, 2);
lean_inc(v_stop_329_);
lean_dec_ref(v_as_326_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_nat_dec_lt(v_start_328_, v_stop_329_);
if (v___x_331_ == 0)
{
lean_object* v_toApplicative_332_; lean_object* v_toPure_333_; lean_object* v___x_334_; 
lean_dec(v_stop_329_);
lean_dec(v_start_328_);
lean_dec_ref(v_array_327_);
lean_dec(v_f_325_);
v_toApplicative_332_ = lean_ctor_get(v_inst_324_, 0);
lean_inc_ref(v_toApplicative_332_);
lean_dec_ref(v_inst_324_);
v_toPure_333_ = lean_ctor_get(v_toApplicative_332_, 1);
lean_inc(v_toPure_333_);
lean_dec_ref(v_toApplicative_332_);
v___x_334_ = lean_apply_2(v_toPure_333_, lean_box(0), v___x_330_);
return v___x_334_;
}
else
{
lean_object* v___f_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___f_335_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_335_, 0, v_f_325_);
v___x_336_ = lean_array_get_size(v_array_327_);
v___x_337_ = lean_nat_dec_le(v_stop_329_, v___x_336_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
lean_dec(v_stop_329_);
v___x_338_ = lean_nat_dec_lt(v_start_328_, v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v_toApplicative_339_; lean_object* v_toPure_340_; lean_object* v___x_341_; 
lean_dec_ref(v___f_335_);
lean_dec(v_start_328_);
lean_dec_ref(v_array_327_);
v_toApplicative_339_ = lean_ctor_get(v_inst_324_, 0);
lean_inc_ref(v_toApplicative_339_);
lean_dec_ref(v_inst_324_);
v_toPure_340_ = lean_ctor_get(v_toApplicative_339_, 1);
lean_inc(v_toPure_340_);
lean_dec_ref(v_toApplicative_339_);
v___x_341_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_330_);
return v___x_341_;
}
else
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_usize_of_nat(v_start_328_);
lean_dec(v_start_328_);
v___x_343_ = lean_usize_of_nat(v___x_336_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_324_, v___f_335_, v_array_327_, v___x_342_, v___x_343_, v___x_330_);
return v___x_344_;
}
}
else
{
size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_usize_of_nat(v_start_328_);
lean_dec(v_start_328_);
v___x_346_ = lean_usize_of_nat(v_stop_329_);
lean_dec(v_stop_329_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_324_, v___f_335_, v_array_327_, v___x_345_, v___x_346_, v___x_330_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM(lean_object* v_00_u03b1_348_, lean_object* v_m_349_, lean_object* v_inst_350_, lean_object* v_f_351_, lean_object* v_as_352_){
_start:
{
lean_object* v_array_353_; lean_object* v_start_354_; lean_object* v_stop_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_array_353_ = lean_ctor_get(v_as_352_, 0);
lean_inc_ref(v_array_353_);
v_start_354_ = lean_ctor_get(v_as_352_, 1);
lean_inc(v_start_354_);
v_stop_355_ = lean_ctor_get(v_as_352_, 2);
lean_inc(v_stop_355_);
lean_dec_ref(v_as_352_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_nat_dec_lt(v_start_354_, v_stop_355_);
if (v___x_357_ == 0)
{
lean_object* v_toApplicative_358_; lean_object* v_toPure_359_; lean_object* v___x_360_; 
lean_dec(v_stop_355_);
lean_dec(v_start_354_);
lean_dec_ref(v_array_353_);
lean_dec(v_f_351_);
v_toApplicative_358_ = lean_ctor_get(v_inst_350_, 0);
lean_inc_ref(v_toApplicative_358_);
lean_dec_ref(v_inst_350_);
v_toPure_359_ = lean_ctor_get(v_toApplicative_358_, 1);
lean_inc(v_toPure_359_);
lean_dec_ref(v_toApplicative_358_);
v___x_360_ = lean_apply_2(v_toPure_359_, lean_box(0), v___x_356_);
return v___x_360_;
}
else
{
lean_object* v___f_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___f_361_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_361_, 0, v_f_351_);
v___x_362_ = lean_array_get_size(v_array_353_);
v___x_363_ = lean_nat_dec_le(v_stop_355_, v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
lean_dec(v_stop_355_);
v___x_364_ = lean_nat_dec_lt(v_start_354_, v___x_362_);
if (v___x_364_ == 0)
{
lean_object* v_toApplicative_365_; lean_object* v_toPure_366_; lean_object* v___x_367_; 
lean_dec_ref(v___f_361_);
lean_dec(v_start_354_);
lean_dec_ref(v_array_353_);
v_toApplicative_365_ = lean_ctor_get(v_inst_350_, 0);
lean_inc_ref(v_toApplicative_365_);
lean_dec_ref(v_inst_350_);
v_toPure_366_ = lean_ctor_get(v_toApplicative_365_, 1);
lean_inc(v_toPure_366_);
lean_dec_ref(v_toApplicative_365_);
v___x_367_ = lean_apply_2(v_toPure_366_, lean_box(0), v___x_356_);
return v___x_367_;
}
else
{
size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_usize_of_nat(v_start_354_);
lean_dec(v_start_354_);
v___x_369_ = lean_usize_of_nat(v___x_362_);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_350_, v___f_361_, v_array_353_, v___x_368_, v___x_369_, v___x_356_);
return v___x_370_;
}
}
else
{
size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_usize_of_nat(v_start_354_);
lean_dec(v_start_354_);
v___x_372_ = lean_usize_of_nat(v_stop_355_);
lean_dec(v_stop_355_);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_350_, v___f_361_, v_array_353_, v___x_371_, v___x_372_, v___x_356_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg___lam__0(lean_object* v_f_374_, lean_object* v_a_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_apply_1(v_f_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg(lean_object* v_inst_378_, lean_object* v_f_379_, lean_object* v_as_380_){
_start:
{
lean_object* v_array_381_; lean_object* v_start_382_; lean_object* v_stop_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_array_381_ = lean_ctor_get(v_as_380_, 0);
lean_inc_ref(v_array_381_);
v_start_382_ = lean_ctor_get(v_as_380_, 1);
lean_inc(v_start_382_);
v_stop_383_ = lean_ctor_get(v_as_380_, 2);
lean_inc(v_stop_383_);
lean_dec_ref(v_as_380_);
v___f_384_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_384_, 0, v_f_379_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_array_get_size(v_array_381_);
v___x_387_ = lean_nat_dec_le(v_stop_383_, v___x_386_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; 
lean_dec(v_stop_383_);
v___x_388_ = lean_nat_dec_lt(v_start_382_, v___x_386_);
if (v___x_388_ == 0)
{
lean_object* v_toApplicative_389_; lean_object* v_toPure_390_; lean_object* v___x_391_; 
lean_dec_ref(v___f_384_);
lean_dec(v_start_382_);
lean_dec_ref(v_array_381_);
v_toApplicative_389_ = lean_ctor_get(v_inst_378_, 0);
lean_inc_ref(v_toApplicative_389_);
lean_dec_ref(v_inst_378_);
v_toPure_390_ = lean_ctor_get(v_toApplicative_389_, 1);
lean_inc(v_toPure_390_);
lean_dec_ref(v_toApplicative_389_);
v___x_391_ = lean_apply_2(v_toPure_390_, lean_box(0), v___x_385_);
return v___x_391_;
}
else
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_usize_of_nat(v___x_386_);
v___x_393_ = lean_usize_of_nat(v_start_382_);
lean_dec(v_start_382_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_378_, v___f_384_, v_array_381_, v___x_392_, v___x_393_, v___x_385_);
return v___x_394_;
}
}
else
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_lt(v_start_382_, v_stop_383_);
if (v___x_395_ == 0)
{
lean_object* v_toApplicative_396_; lean_object* v_toPure_397_; lean_object* v___x_398_; 
lean_dec_ref(v___f_384_);
lean_dec(v_stop_383_);
lean_dec(v_start_382_);
lean_dec_ref(v_array_381_);
v_toApplicative_396_ = lean_ctor_get(v_inst_378_, 0);
lean_inc_ref(v_toApplicative_396_);
lean_dec_ref(v_inst_378_);
v_toPure_397_ = lean_ctor_get(v_toApplicative_396_, 1);
lean_inc(v_toPure_397_);
lean_dec_ref(v_toApplicative_396_);
v___x_398_ = lean_apply_2(v_toPure_397_, lean_box(0), v___x_385_);
return v___x_398_;
}
else
{
size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_usize_of_nat(v_stop_383_);
lean_dec(v_stop_383_);
v___x_400_ = lean_usize_of_nat(v_start_382_);
lean_dec(v_start_382_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_378_, v___f_384_, v_array_381_, v___x_399_, v___x_400_, v___x_385_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM(lean_object* v_00_u03b1_402_, lean_object* v_m_403_, lean_object* v_inst_404_, lean_object* v_f_405_, lean_object* v_as_406_){
_start:
{
lean_object* v_array_407_; lean_object* v_start_408_; lean_object* v_stop_409_; lean_object* v___f_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_array_407_ = lean_ctor_get(v_as_406_, 0);
lean_inc_ref(v_array_407_);
v_start_408_ = lean_ctor_get(v_as_406_, 1);
lean_inc(v_start_408_);
v_stop_409_ = lean_ctor_get(v_as_406_, 2);
lean_inc(v_stop_409_);
lean_dec_ref(v_as_406_);
v___f_410_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_410_, 0, v_f_405_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_array_get_size(v_array_407_);
v___x_413_ = lean_nat_dec_le(v_stop_409_, v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
lean_dec(v_stop_409_);
v___x_414_ = lean_nat_dec_lt(v_start_408_, v___x_412_);
if (v___x_414_ == 0)
{
lean_object* v_toApplicative_415_; lean_object* v_toPure_416_; lean_object* v___x_417_; 
lean_dec_ref(v___f_410_);
lean_dec(v_start_408_);
lean_dec_ref(v_array_407_);
v_toApplicative_415_ = lean_ctor_get(v_inst_404_, 0);
lean_inc_ref(v_toApplicative_415_);
lean_dec_ref(v_inst_404_);
v_toPure_416_ = lean_ctor_get(v_toApplicative_415_, 1);
lean_inc(v_toPure_416_);
lean_dec_ref(v_toApplicative_415_);
v___x_417_ = lean_apply_2(v_toPure_416_, lean_box(0), v___x_411_);
return v___x_417_;
}
else
{
size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_usize_of_nat(v___x_412_);
v___x_419_ = lean_usize_of_nat(v_start_408_);
lean_dec(v_start_408_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_404_, v___f_410_, v_array_407_, v___x_418_, v___x_419_, v___x_411_);
return v___x_420_;
}
}
else
{
uint8_t v___x_421_; 
v___x_421_ = lean_nat_dec_lt(v_start_408_, v_stop_409_);
if (v___x_421_ == 0)
{
lean_object* v_toApplicative_422_; lean_object* v_toPure_423_; lean_object* v___x_424_; 
lean_dec_ref(v___f_410_);
lean_dec(v_stop_409_);
lean_dec(v_start_408_);
lean_dec_ref(v_array_407_);
v_toApplicative_422_ = lean_ctor_get(v_inst_404_, 0);
lean_inc_ref(v_toApplicative_422_);
lean_dec_ref(v_inst_404_);
v_toPure_423_ = lean_ctor_get(v_toApplicative_422_, 1);
lean_inc(v_toPure_423_);
lean_dec_ref(v_toApplicative_422_);
v___x_424_ = lean_apply_2(v_toPure_423_, lean_box(0), v___x_411_);
return v___x_424_;
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_usize_of_nat(v_stop_409_);
lean_dec(v_stop_409_);
v___x_426_ = lean_usize_of_nat(v_start_408_);
lean_dec(v_start_408_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_404_, v___f_410_, v_array_407_, v___x_425_, v___x_426_, v___x_411_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg___lam__0(lean_object* v_f_428_, lean_object* v_x1_429_, lean_object* v_x2_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_apply_2(v_f_428_, v_x1_429_, v_x2_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg(lean_object* v_f_451_, lean_object* v_init_452_, lean_object* v_as_453_){
_start:
{
lean_object* v___x_454_; lean_object* v_array_455_; lean_object* v_start_456_; lean_object* v_stop_457_; lean_object* v___f_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_454_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_455_ = lean_ctor_get(v_as_453_, 0);
lean_inc_ref(v_array_455_);
v_start_456_ = lean_ctor_get(v_as_453_, 1);
lean_inc(v_start_456_);
v_stop_457_ = lean_ctor_get(v_as_453_, 2);
lean_inc(v_stop_457_);
lean_dec_ref(v_as_453_);
v___f_458_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_458_, 0, v_f_451_);
v___x_459_ = lean_array_get_size(v_array_455_);
v___x_460_ = lean_nat_dec_le(v_stop_457_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
lean_dec(v_stop_457_);
v___x_461_ = lean_nat_dec_lt(v_start_456_, v___x_459_);
if (v___x_461_ == 0)
{
lean_dec_ref(v___f_458_);
lean_dec(v_start_456_);
lean_dec_ref(v_array_455_);
return v_init_452_;
}
else
{
size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_usize_of_nat(v___x_459_);
v___x_463_ = lean_usize_of_nat(v_start_456_);
lean_dec(v_start_456_);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_454_, v___f_458_, v_array_455_, v___x_462_, v___x_463_, v_init_452_);
return v___x_464_;
}
}
else
{
uint8_t v___x_465_; 
v___x_465_ = lean_nat_dec_lt(v_start_456_, v_stop_457_);
if (v___x_465_ == 0)
{
lean_dec_ref(v___f_458_);
lean_dec(v_stop_457_);
lean_dec(v_start_456_);
lean_dec_ref(v_array_455_);
return v_init_452_;
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_usize_of_nat(v_stop_457_);
lean_dec(v_stop_457_);
v___x_467_ = lean_usize_of_nat(v_start_456_);
lean_dec(v_start_456_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_454_, v___f_458_, v_array_455_, v___x_466_, v___x_467_, v_init_452_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_f_471_, lean_object* v_init_472_, lean_object* v_as_473_){
_start:
{
lean_object* v___x_474_; lean_object* v_array_475_; lean_object* v_start_476_; lean_object* v_stop_477_; lean_object* v___f_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_474_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_475_ = lean_ctor_get(v_as_473_, 0);
lean_inc_ref(v_array_475_);
v_start_476_ = lean_ctor_get(v_as_473_, 1);
lean_inc(v_start_476_);
v_stop_477_ = lean_ctor_get(v_as_473_, 2);
lean_inc(v_stop_477_);
lean_dec_ref(v_as_473_);
v___f_478_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_478_, 0, v_f_471_);
v___x_479_ = lean_array_get_size(v_array_475_);
v___x_480_ = lean_nat_dec_le(v_stop_477_, v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; 
lean_dec(v_stop_477_);
v___x_481_ = lean_nat_dec_lt(v_start_476_, v___x_479_);
if (v___x_481_ == 0)
{
lean_dec_ref(v___f_478_);
lean_dec(v_start_476_);
lean_dec_ref(v_array_475_);
return v_init_472_;
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_usize_of_nat(v___x_479_);
v___x_483_ = lean_usize_of_nat(v_start_476_);
lean_dec(v_start_476_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_474_, v___f_478_, v_array_475_, v___x_482_, v___x_483_, v_init_472_);
return v___x_484_;
}
}
else
{
uint8_t v___x_485_; 
v___x_485_ = lean_nat_dec_lt(v_start_476_, v_stop_477_);
if (v___x_485_ == 0)
{
lean_dec_ref(v___f_478_);
lean_dec(v_stop_477_);
lean_dec(v_start_476_);
lean_dec_ref(v_array_475_);
return v_init_472_;
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_usize_of_nat(v_stop_477_);
lean_dec(v_stop_477_);
v___x_487_ = lean_usize_of_nat(v_start_476_);
lean_dec(v_start_476_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_474_, v___f_478_, v_array_475_, v___x_486_, v___x_487_, v_init_472_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg___lam__0(lean_object* v_p_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_apply_1(v_p_489_, v_x_490_);
v___x_492_ = lean_unbox(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___lam__0___boxed(lean_object* v_p_493_, lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Subarray_any___redArg___lam__0(v_p_493_, v_x_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg(lean_object* v_p_497_, lean_object* v_as_498_){
_start:
{
lean_object* v___x_499_; lean_object* v_array_500_; lean_object* v_start_501_; lean_object* v_stop_502_; uint8_t v___x_503_; 
v___x_499_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_500_ = lean_ctor_get(v_as_498_, 0);
lean_inc_ref(v_array_500_);
v_start_501_ = lean_ctor_get(v_as_498_, 1);
lean_inc(v_start_501_);
v_stop_502_ = lean_ctor_get(v_as_498_, 2);
lean_inc(v_stop_502_);
lean_dec_ref(v_as_498_);
v___x_503_ = lean_nat_dec_lt(v_start_501_, v_stop_502_);
if (v___x_503_ == 0)
{
lean_dec(v_stop_502_);
lean_dec(v_start_501_);
lean_dec_ref(v_array_500_);
lean_dec_ref(v_p_497_);
return v___x_503_;
}
else
{
lean_object* v___f_504_; lean_object* v___y_506_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___f_504_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_504_, 0, v_p_497_);
v___x_512_ = lean_array_get_size(v_array_500_);
v___x_513_ = lean_nat_dec_le(v_stop_502_, v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v_stop_502_);
v___y_506_ = v___x_512_;
goto v___jp_505_;
}
else
{
v___y_506_ = v_stop_502_;
goto v___jp_505_;
}
v___jp_505_:
{
uint8_t v___x_507_; 
v___x_507_ = lean_nat_dec_lt(v_start_501_, v___y_506_);
if (v___x_507_ == 0)
{
lean_dec(v___y_506_);
lean_dec_ref(v___f_504_);
lean_dec(v_start_501_);
lean_dec_ref(v_array_500_);
return v___x_507_;
}
else
{
size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_usize_of_nat(v_start_501_);
lean_dec(v_start_501_);
v___x_509_ = lean_usize_of_nat(v___y_506_);
lean_dec(v___y_506_);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_499_, v___f_504_, v_array_500_, v___x_508_, v___x_509_);
v___x_511_ = lean_unbox(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___boxed(lean_object* v_p_514_, lean_object* v_as_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Subarray_any___redArg(v_p_514_, v_as_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any(lean_object* v_00_u03b1_518_, lean_object* v_p_519_, lean_object* v_as_520_){
_start:
{
lean_object* v___x_521_; lean_object* v_array_522_; lean_object* v_start_523_; lean_object* v_stop_524_; uint8_t v___x_525_; 
v___x_521_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_522_ = lean_ctor_get(v_as_520_, 0);
lean_inc_ref(v_array_522_);
v_start_523_ = lean_ctor_get(v_as_520_, 1);
lean_inc(v_start_523_);
v_stop_524_ = lean_ctor_get(v_as_520_, 2);
lean_inc(v_stop_524_);
lean_dec_ref(v_as_520_);
v___x_525_ = lean_nat_dec_lt(v_start_523_, v_stop_524_);
if (v___x_525_ == 0)
{
lean_dec(v_stop_524_);
lean_dec(v_start_523_);
lean_dec_ref(v_array_522_);
lean_dec_ref(v_p_519_);
return v___x_525_;
}
else
{
lean_object* v___f_526_; lean_object* v___y_528_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___f_526_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_526_, 0, v_p_519_);
v___x_534_ = lean_array_get_size(v_array_522_);
v___x_535_ = lean_nat_dec_le(v_stop_524_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec(v_stop_524_);
v___y_528_ = v___x_534_;
goto v___jp_527_;
}
else
{
v___y_528_ = v_stop_524_;
goto v___jp_527_;
}
v___jp_527_:
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_lt(v_start_523_, v___y_528_);
if (v___x_529_ == 0)
{
lean_dec(v___y_528_);
lean_dec_ref(v___f_526_);
lean_dec(v_start_523_);
lean_dec_ref(v_array_522_);
return v___x_529_;
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_530_ = lean_usize_of_nat(v_start_523_);
lean_dec(v_start_523_);
v___x_531_ = lean_usize_of_nat(v___y_528_);
lean_dec(v___y_528_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_521_, v___f_526_, v_array_522_, v___x_530_, v___x_531_);
v___x_533_ = lean_unbox(v___x_532_);
lean_dec(v___x_532_);
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___boxed(lean_object* v_00_u03b1_536_, lean_object* v_p_537_, lean_object* v_as_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Subarray_any(v_00_u03b1_536_, v_p_537_, v_as_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg___lam__0(lean_object* v_p_541_, lean_object* v_v_542_){
_start:
{
lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_apply_1(v_p_541_, v_v_542_);
v___x_544_ = lean_unbox(v___x_543_);
v___x_545_ = lean_bool_not(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object* v_p_546_, lean_object* v_v_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l_Subarray_all___redArg___lam__0(v_p_546_, v_v_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg(lean_object* v_p_550_, lean_object* v_as_551_){
_start:
{
lean_object* v___x_552_; lean_object* v_array_553_; lean_object* v_start_554_; lean_object* v_stop_555_; uint8_t v___x_556_; 
v___x_552_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_553_ = lean_ctor_get(v_as_551_, 0);
lean_inc_ref(v_array_553_);
v_start_554_ = lean_ctor_get(v_as_551_, 1);
lean_inc(v_start_554_);
v_stop_555_ = lean_ctor_get(v_as_551_, 2);
lean_inc(v_stop_555_);
lean_dec_ref(v_as_551_);
v___x_556_ = lean_nat_dec_lt(v_start_554_, v_stop_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
lean_dec_ref(v_p_550_);
v___x_557_ = lean_bool_not(v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___f_558_; lean_object* v___y_560_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___f_558_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_558_, 0, v_p_550_);
v___x_568_ = lean_array_get_size(v_array_553_);
v___x_569_ = lean_nat_dec_le(v_stop_555_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v_stop_555_);
v___y_560_ = v___x_568_;
goto v___jp_559_;
}
else
{
v___y_560_ = v_stop_555_;
goto v___jp_559_;
}
v___jp_559_:
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_lt(v_start_554_, v___y_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
lean_dec(v___y_560_);
lean_dec_ref(v___f_558_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
v___x_562_ = lean_bool_not(v___x_561_);
return v___x_562_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_563_ = lean_usize_of_nat(v_start_554_);
lean_dec(v_start_554_);
v___x_564_ = lean_usize_of_nat(v___y_560_);
lean_dec(v___y_560_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_552_, v___f_558_, v_array_553_, v___x_563_, v___x_564_);
v___x_566_ = lean_unbox(v___x_565_);
lean_dec(v___x_565_);
v___x_567_ = lean_bool_not(v___x_566_);
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___boxed(lean_object* v_p_570_, lean_object* v_as_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Subarray_all___redArg(v_p_570_, v_as_571_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all(lean_object* v_00_u03b1_574_, lean_object* v_p_575_, lean_object* v_as_576_){
_start:
{
lean_object* v___x_577_; lean_object* v_array_578_; lean_object* v_start_579_; lean_object* v_stop_580_; uint8_t v___x_581_; 
v___x_577_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_578_ = lean_ctor_get(v_as_576_, 0);
lean_inc_ref(v_array_578_);
v_start_579_ = lean_ctor_get(v_as_576_, 1);
lean_inc(v_start_579_);
v_stop_580_ = lean_ctor_get(v_as_576_, 2);
lean_inc(v_stop_580_);
lean_dec_ref(v_as_576_);
v___x_581_ = lean_nat_dec_lt(v_start_579_, v_stop_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
lean_dec(v_stop_580_);
lean_dec(v_start_579_);
lean_dec_ref(v_array_578_);
lean_dec_ref(v_p_575_);
v___x_582_ = lean_bool_not(v___x_581_);
return v___x_582_;
}
else
{
lean_object* v___f_583_; lean_object* v___y_585_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___f_583_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_583_, 0, v_p_575_);
v___x_593_ = lean_array_get_size(v_array_578_);
v___x_594_ = lean_nat_dec_le(v_stop_580_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_stop_580_);
v___y_585_ = v___x_593_;
goto v___jp_584_;
}
else
{
v___y_585_ = v_stop_580_;
goto v___jp_584_;
}
v___jp_584_:
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_start_579_, v___y_585_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
lean_dec(v___y_585_);
lean_dec_ref(v___f_583_);
lean_dec(v_start_579_);
lean_dec_ref(v_array_578_);
v___x_587_ = lean_bool_not(v___x_586_);
return v___x_587_;
}
else
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; uint8_t v___x_592_; 
v___x_588_ = lean_usize_of_nat(v_start_579_);
lean_dec(v_start_579_);
v___x_589_ = lean_usize_of_nat(v___y_585_);
lean_dec(v___y_585_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_577_, v___f_583_, v_array_578_, v___x_588_, v___x_589_);
v___x_591_ = lean_unbox(v___x_590_);
lean_dec(v___x_590_);
v___x_592_ = lean_bool_not(v___x_591_);
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___boxed(lean_object* v_00_u03b1_595_, lean_object* v_p_596_, lean_object* v_as_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Subarray_all(v_00_u03b1_595_, v_p_596_, v_as_597_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_600_, lean_object* v_as_601_, lean_object* v_f_602_, lean_object* v_n_603_, lean_object* v_toPure_604_, lean_object* v_r_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(v_inst_600_, v_as_601_, v_f_602_, v_n_603_, v_toPure_604_, v_r_605_);
lean_dec(v_n_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(lean_object* v_inst_607_, lean_object* v_as_608_, lean_object* v_f_609_, lean_object* v_i_610_){
_start:
{
lean_object* v_toApplicative_611_; lean_object* v_toBind_612_; lean_object* v_toPure_613_; lean_object* v_zero_614_; uint8_t v_isZero_615_; 
v_toApplicative_611_ = lean_ctor_get(v_inst_607_, 0);
v_toBind_612_ = lean_ctor_get(v_inst_607_, 1);
lean_inc(v_toBind_612_);
v_toPure_613_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_inc(v_toPure_613_);
v_zero_614_ = lean_unsigned_to_nat(0u);
v_isZero_615_ = lean_nat_dec_eq(v_i_610_, v_zero_614_);
if (v_isZero_615_ == 1)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec(v_toBind_612_);
lean_dec(v_f_609_);
lean_dec_ref(v_as_608_);
lean_dec_ref(v_inst_607_);
v___x_616_ = lean_box(0);
v___x_617_ = lean_apply_2(v_toPure_613_, lean_box(0), v___x_616_);
return v___x_617_;
}
else
{
lean_object* v_one_618_; lean_object* v_n_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_one_618_ = lean_unsigned_to_nat(1u);
v_n_619_ = lean_nat_sub(v_i_610_, v_one_618_);
lean_inc(v_n_619_);
lean_inc(v_f_609_);
lean_inc_ref(v_as_608_);
v___f_620_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_620_, 0, v_inst_607_);
lean_closure_set(v___f_620_, 1, v_as_608_);
lean_closure_set(v___f_620_, 2, v_f_609_);
lean_closure_set(v___f_620_, 3, v_n_619_);
lean_closure_set(v___f_620_, 4, v_toPure_613_);
v___x_621_ = l_Subarray_get___redArg(v_as_608_, v_n_619_);
lean_dec(v_n_619_);
lean_dec_ref(v_as_608_);
v___x_622_ = lean_apply_1(v_f_609_, v___x_621_);
v___x_623_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v___x_622_, v___f_620_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_624_, lean_object* v_as_625_, lean_object* v_f_626_, lean_object* v_n_627_, lean_object* v_toPure_628_, lean_object* v_r_629_){
_start:
{
if (lean_obj_tag(v_r_629_) == 0)
{
lean_object* v___x_630_; 
lean_dec(v_toPure_628_);
v___x_630_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_624_, v_as_625_, v_f_626_, v_n_627_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
lean_dec(v_f_626_);
lean_dec_ref(v_as_625_);
lean_dec_ref(v_inst_624_);
v___x_631_ = lean_apply_2(v_toPure_628_, lean_box(0), v_r_629_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_632_, lean_object* v_as_633_, lean_object* v_f_634_, lean_object* v_i_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_632_, v_as_633_, v_f_634_, v_i_635_);
lean_dec(v_i_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_m_639_, lean_object* v_inst_640_, lean_object* v_as_641_, lean_object* v_f_642_, lean_object* v_i_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_640_, v_as_641_, v_f_642_, v_i_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_m_648_, lean_object* v_inst_649_, lean_object* v_as_650_, lean_object* v_f_651_, lean_object* v_i_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(v_00_u03b1_646_, v_00_u03b2_647_, v_m_648_, v_inst_649_, v_as_650_, v_f_651_, v_i_652_, v_a_653_);
lean_dec(v_i_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f___redArg(lean_object* v_inst_655_, lean_object* v_as_656_, lean_object* v_f_657_){
_start:
{
lean_object* v_start_658_; lean_object* v_stop_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_start_658_ = lean_ctor_get(v_as_656_, 1);
v_stop_659_ = lean_ctor_get(v_as_656_, 2);
v___x_660_ = lean_nat_sub(v_stop_659_, v_start_658_);
v___x_661_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_655_, v_as_656_, v_f_657_, v___x_660_);
lean_dec(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_m_664_, lean_object* v_inst_665_, lean_object* v_as_666_, lean_object* v_f_667_){
_start:
{
lean_object* v_start_668_; lean_object* v_stop_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_start_668_ = lean_ctor_get(v_as_666_, 1);
v_stop_669_ = lean_ctor_get(v_as_666_, 2);
v___x_670_ = lean_nat_sub(v_stop_669_, v_start_668_);
v___x_671_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_665_, v_as_666_, v_f_667_, v___x_670_);
lean_dec(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_672_, lean_object* v_a_673_, uint8_t v_____do__lift_674_){
_start:
{
if (v_____do__lift_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_a_673_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_apply_2(v_toPure_672_, lean_box(0), v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v_a_673_);
v___x_678_ = lean_apply_2(v_toPure_672_, lean_box(0), v___x_677_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_679_, lean_object* v_a_680_, lean_object* v_____do__lift_681_){
_start:
{
uint8_t v_____do__lift_77__boxed_682_; lean_object* v_res_683_; 
v_____do__lift_77__boxed_682_ = lean_unbox(v_____do__lift_681_);
v_res_683_ = l_Subarray_findRevM_x3f___redArg___lam__0(v_toPure_679_, v_a_680_, v_____do__lift_77__boxed_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_684_, lean_object* v_p_685_, lean_object* v_toBind_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_inc(v_a_687_);
v___f_688_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_688_, 0, v_toPure_684_);
lean_closure_set(v___f_688_, 1, v_a_687_);
v___x_689_ = lean_apply_1(v_p_685_, v_a_687_);
v___x_690_ = lean_apply_4(v_toBind_686_, lean_box(0), lean_box(0), v___x_689_, v___f_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg(lean_object* v_inst_691_, lean_object* v_as_692_, lean_object* v_p_693_){
_start:
{
lean_object* v_toApplicative_694_; lean_object* v_toBind_695_; lean_object* v_toPure_696_; lean_object* v_start_697_; lean_object* v_stop_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_toApplicative_694_ = lean_ctor_get(v_inst_691_, 0);
v_toBind_695_ = lean_ctor_get(v_inst_691_, 1);
v_toPure_696_ = lean_ctor_get(v_toApplicative_694_, 1);
v_start_697_ = lean_ctor_get(v_as_692_, 1);
v_stop_698_ = lean_ctor_get(v_as_692_, 2);
lean_inc(v_toBind_695_);
lean_inc(v_toPure_696_);
v___f_699_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_699_, 0, v_toPure_696_);
lean_closure_set(v___f_699_, 1, v_p_693_);
lean_closure_set(v___f_699_, 2, v_toBind_695_);
v___x_700_ = lean_nat_sub(v_stop_698_, v_start_697_);
v___x_701_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_691_, v_as_692_, v___f_699_, v___x_700_);
lean_dec(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f(lean_object* v_00_u03b1_702_, lean_object* v_m_703_, lean_object* v_inst_704_, lean_object* v_as_705_, lean_object* v_p_706_){
_start:
{
lean_object* v_toApplicative_707_; lean_object* v_toBind_708_; lean_object* v_toPure_709_; lean_object* v_start_710_; lean_object* v_stop_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_toApplicative_707_ = lean_ctor_get(v_inst_704_, 0);
v_toBind_708_ = lean_ctor_get(v_inst_704_, 1);
v_toPure_709_ = lean_ctor_get(v_toApplicative_707_, 1);
v_start_710_ = lean_ctor_get(v_as_705_, 1);
v_stop_711_ = lean_ctor_get(v_as_705_, 2);
lean_inc(v_toBind_708_);
lean_inc(v_toPure_709_);
v___f_712_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_712_, 0, v_toPure_709_);
lean_closure_set(v___f_712_, 1, v_p_706_);
lean_closure_set(v___f_712_, 2, v_toBind_708_);
v___x_713_ = lean_nat_sub(v_stop_711_, v_start_710_);
v___x_714_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_704_, v_as_705_, v___f_712_, v___x_713_);
lean_dec(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg___lam__0(lean_object* v_p_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
lean_inc(v_a_716_);
v___x_717_ = lean_apply_1(v_p_715_, v_a_716_);
v___x_718_ = lean_unbox(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec(v_a_716_);
v___x_719_ = lean_box(0);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v_a_716_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg(lean_object* v_as_721_, lean_object* v_p_722_){
_start:
{
lean_object* v___x_723_; lean_object* v_start_724_; lean_object* v_stop_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_724_ = lean_ctor_get(v_as_721_, 1);
v_stop_725_ = lean_ctor_get(v_as_721_, 2);
v___f_726_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_726_, 0, v_p_722_);
v___x_727_ = lean_nat_sub(v_stop_725_, v_start_724_);
v___x_728_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_723_, v_as_721_, v___f_726_, v___x_727_);
lean_dec(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f(lean_object* v_00_u03b1_729_, lean_object* v_as_730_, lean_object* v_p_731_){
_start:
{
lean_object* v___x_732_; lean_object* v_start_733_; lean_object* v_stop_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_733_ = lean_ctor_get(v_as_730_, 1);
v_stop_734_ = lean_ctor_get(v_as_730_, 2);
v___f_735_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_735_, 0, v_p_731_);
v___x_736_ = lean_nat_sub(v_stop_734_, v_start_733_);
v___x_737_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_732_, v_as_730_, v___f_735_, v___x_736_);
lean_dec(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray___redArg(lean_object* v_as_738_, lean_object* v_start_739_, lean_object* v_stop_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_as_738_);
v___x_742_ = lean_nat_dec_le(v_stop_740_, v___x_741_);
if (v___x_742_ == 0)
{
uint8_t v___x_743_; 
lean_dec(v_stop_740_);
v___x_743_ = lean_nat_dec_le(v_start_739_, v___x_741_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_start_739_);
v___x_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_744_, 0, v_as_738_);
lean_ctor_set(v___x_744_, 1, v___x_741_);
lean_ctor_set(v___x_744_, 2, v___x_741_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v_as_738_);
lean_ctor_set(v___x_745_, 1, v_start_739_);
lean_ctor_set(v___x_745_, 2, v___x_741_);
return v___x_745_;
}
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_le(v_start_739_, v_stop_740_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_start_739_);
lean_inc(v_stop_740_);
v___x_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_747_, 0, v_as_738_);
lean_ctor_set(v___x_747_, 1, v_stop_740_);
lean_ctor_set(v___x_747_, 2, v_stop_740_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_748_, 0, v_as_738_);
lean_ctor_set(v___x_748_, 1, v_start_739_);
lean_ctor_set(v___x_748_, 2, v_stop_740_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray(lean_object* v_00_u03b1_749_, lean_object* v_as_750_, lean_object* v_start_751_, lean_object* v_stop_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Array_toSubarray___redArg(v_as_750_, v_start_751_, v_stop_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5));
v___x_871_ = l_String_toRawSubstring_x27(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(lean_object* v_x_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = ((lean_object*)(l_Array_term_____x5b___x3a___x5d___closed__2));
lean_inc(v_x_885_);
v___x_889_ = l_Lean_Syntax_isOfKind(v_x_885_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_x_885_);
v___x_890_ = lean_box(1);
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_a_887_);
return v___x_891_;
}
else
{
lean_object* v_quotContext_892_; lean_object* v_currMacroScope_893_; lean_object* v_ref_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_quotContext_892_ = lean_ctor_get(v_a_886_, 1);
v_currMacroScope_893_ = lean_ctor_get(v_a_886_, 2);
v_ref_894_ = lean_ctor_get(v_a_886_, 5);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = l_Lean_Syntax_getArg(v_x_885_, v___x_895_);
v___x_897_ = lean_unsigned_to_nat(2u);
v___x_898_ = l_Lean_Syntax_getArg(v_x_885_, v___x_897_);
v___x_899_ = lean_unsigned_to_nat(4u);
v___x_900_ = l_Lean_Syntax_getArg(v_x_885_, v___x_899_);
lean_dec(v_x_885_);
v___x_901_ = 0;
v___x_902_ = l_Lean_SourceInfo_fromRef(v_ref_894_, v___x_901_);
v___x_903_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_904_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_905_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_893_);
lean_inc(v_quotContext_892_);
v___x_906_ = l_Lean_addMacroScope(v_quotContext_892_, v___x_905_, v_currMacroScope_893_);
v___x_907_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_902_, 2);
v___x_908_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_908_, 0, v___x_902_);
lean_ctor_set(v___x_908_, 1, v___x_904_);
lean_ctor_set(v___x_908_, 2, v___x_906_);
lean_ctor_set(v___x_908_, 3, v___x_907_);
v___x_909_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_910_ = l_Lean_Syntax_node3(v___x_902_, v___x_909_, v___x_896_, v___x_898_, v___x_900_);
v___x_911_ = l_Lean_Syntax_node2(v___x_902_, v___x_903_, v___x_908_, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_a_887_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(lean_object* v_x_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(v_x_913_, v_a_914_, v_a_915_);
lean_dec_ref(v_a_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object* v_x_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = ((lean_object*)(l_Array_term_____x5b_x3a___x5d___closed__1));
lean_inc(v_x_921_);
v___x_925_ = l_Lean_Syntax_isOfKind(v_x_921_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_x_921_);
v___x_926_ = lean_box(1);
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_923_);
return v___x_927_;
}
else
{
lean_object* v_quotContext_928_; lean_object* v_currMacroScope_929_; lean_object* v_ref_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_quotContext_928_ = lean_ctor_get(v_a_922_, 1);
v_currMacroScope_929_ = lean_ctor_get(v_a_922_, 2);
v_ref_930_ = lean_ctor_get(v_a_922_, 5);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = l_Lean_Syntax_getArg(v_x_921_, v___x_931_);
v___x_933_ = lean_unsigned_to_nat(3u);
v___x_934_ = l_Lean_Syntax_getArg(v_x_921_, v___x_933_);
lean_dec(v_x_921_);
v___x_935_ = 0;
v___x_936_ = l_Lean_SourceInfo_fromRef(v_ref_930_, v___x_935_);
v___x_937_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_938_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_939_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_929_);
lean_inc(v_quotContext_928_);
v___x_940_ = l_Lean_addMacroScope(v_quotContext_928_, v___x_939_, v_currMacroScope_929_);
v___x_941_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_936_, 4);
v___x_942_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_942_, 0, v___x_936_);
lean_ctor_set(v___x_942_, 1, v___x_938_);
lean_ctor_set(v___x_942_, 2, v___x_940_);
lean_ctor_set(v___x_942_, 3, v___x_941_);
v___x_943_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_944_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1));
v___x_945_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2));
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_936_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_Syntax_node1(v___x_936_, v___x_944_, v___x_946_);
v___x_948_ = l_Lean_Syntax_node3(v___x_936_, v___x_943_, v___x_932_, v___x_947_, v___x_934_);
v___x_949_ = l_Lean_Syntax_node2(v___x_936_, v___x_937_, v___x_942_, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v_a_923_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(lean_object* v_x_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(v_x_951_, v_a_952_, v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_954_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Array_mkArray0(lean_box(0));
return v___x_967_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11));
v___x_988_ = l_String_toRawSubstring_x27(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18));
v___x_1001_ = l_String_toRawSubstring_x27(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(lean_object* v_x_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Array_term_____x5b___x3a_x5d___closed__1));
lean_inc(v_x_1006_);
v___x_1010_ = l_Lean_Syntax_isOfKind(v_x_1006_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v_x_1006_);
v___x_1011_ = lean_box(1);
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_a_1008_);
return v___x_1012_;
}
else
{
lean_object* v_quotContext_1013_; lean_object* v_currMacroScope_1014_; lean_object* v_ref_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_quotContext_1013_ = lean_ctor_get(v_a_1007_, 1);
v_currMacroScope_1014_ = lean_ctor_get(v_a_1007_, 2);
v_ref_1015_ = lean_ctor_get(v_a_1007_, 5);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = l_Lean_Syntax_getArg(v_x_1006_, v___x_1016_);
v___x_1018_ = lean_unsigned_to_nat(2u);
v___x_1019_ = l_Lean_Syntax_getArg(v_x_1006_, v___x_1018_);
lean_dec(v_x_1006_);
v___x_1020_ = 0;
v___x_1021_ = l_Lean_SourceInfo_fromRef(v_ref_1015_, v___x_1020_);
v___x_1022_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0));
v___x_1023_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1));
lean_inc_n(v___x_1021_, 13);
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1021_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
v___x_1025_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3));
v___x_1026_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_1027_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
v___x_1028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1021_);
lean_ctor_set(v___x_1028_, 1, v___x_1026_);
lean_ctor_set(v___x_1028_, 2, v___x_1027_);
lean_inc_ref_n(v___x_1028_, 2);
v___x_1029_ = l_Lean_Syntax_node1(v___x_1021_, v___x_1025_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6));
v___x_1031_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8));
v___x_1032_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10));
v___x_1033_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
v___x_1034_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13));
lean_inc_n(v_currMacroScope_1014_, 3);
lean_inc_n(v_quotContext_1013_, 3);
v___x_1035_ = l_Lean_addMacroScope(v_quotContext_1013_, v___x_1034_, v_currMacroScope_1014_);
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1021_);
lean_ctor_set(v___x_1037_, 1, v___x_1033_);
lean_ctor_set(v___x_1037_, 2, v___x_1035_);
lean_ctor_set(v___x_1037_, 3, v___x_1036_);
lean_inc_ref(v___x_1037_);
v___x_1038_ = l_Lean_Syntax_node1(v___x_1021_, v___x_1032_, v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14));
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1021_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node5(v___x_1021_, v___x_1031_, v___x_1038_, v___x_1028_, v___x_1028_, v___x_1040_, v___x_1017_);
v___x_1042_ = l_Lean_Syntax_node1(v___x_1021_, v___x_1030_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15));
v___x_1044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1021_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_1046_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_1047_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
v___x_1048_ = l_Lean_addMacroScope(v_quotContext_1013_, v___x_1047_, v_currMacroScope_1014_);
v___x_1049_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17));
v___x_1050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1021_);
lean_ctor_set(v___x_1050_, 1, v___x_1046_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
lean_ctor_set(v___x_1050_, 3, v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
v___x_1052_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21));
v___x_1053_ = l_Lean_addMacroScope(v_quotContext_1013_, v___x_1052_, v_currMacroScope_1014_);
v___x_1054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1021_);
lean_ctor_set(v___x_1054_, 1, v___x_1051_);
lean_ctor_set(v___x_1054_, 2, v___x_1053_);
lean_ctor_set(v___x_1054_, 3, v___x_1036_);
v___x_1055_ = l_Lean_Syntax_node3(v___x_1021_, v___x_1026_, v___x_1037_, v___x_1019_, v___x_1054_);
v___x_1056_ = l_Lean_Syntax_node2(v___x_1021_, v___x_1045_, v___x_1050_, v___x_1055_);
v___x_1057_ = l_Lean_Syntax_node5(v___x_1021_, v___x_1023_, v___x_1024_, v___x_1029_, v___x_1042_, v___x_1044_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_a_1008_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(lean_object* v_x_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(v_x_1059_, v_a_1060_, v_a_1061_);
lean_dec_ref(v_a_1060_);
return v_res_1062_;
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
