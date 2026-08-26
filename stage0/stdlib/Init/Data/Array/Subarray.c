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
lean_object* v_toApplicative_156_; lean_object* v_array_157_; lean_object* v_start_158_; lean_object* v_stop_159_; lean_object* v_toPure_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_toApplicative_156_ = lean_ctor_get(v_inst_152_, 0);
v_array_157_ = lean_ctor_get(v_as_155_, 0);
lean_inc_ref(v_array_157_);
v_start_158_ = lean_ctor_get(v_as_155_, 1);
lean_inc(v_start_158_);
v_stop_159_ = lean_ctor_get(v_as_155_, 2);
lean_inc(v_stop_159_);
lean_dec_ref(v_as_155_);
v_toPure_160_ = lean_ctor_get(v_toApplicative_156_, 1);
v___x_161_ = lean_array_get_size(v_array_157_);
v___x_162_ = lean_nat_dec_le(v_stop_159_, v___x_161_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; 
lean_dec(v_stop_159_);
v___x_163_ = lean_nat_dec_lt(v_start_158_, v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_inc(v_toPure_160_);
lean_dec(v_start_158_);
lean_dec_ref(v_array_157_);
lean_dec(v_f_153_);
lean_dec_ref(v_inst_152_);
v___x_164_ = lean_apply_2(v_toPure_160_, lean_box(0), v_init_154_);
return v___x_164_;
}
else
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_usize_of_nat(v___x_161_);
v___x_166_ = lean_usize_of_nat(v_start_158_);
lean_dec(v_start_158_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_152_, v_f_153_, v_array_157_, v___x_165_, v___x_166_, v_init_154_);
return v___x_167_;
}
}
else
{
uint8_t v___x_168_; 
v___x_168_ = lean_nat_dec_lt(v_start_158_, v_stop_159_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_inc(v_toPure_160_);
lean_dec(v_stop_159_);
lean_dec(v_start_158_);
lean_dec_ref(v_array_157_);
lean_dec(v_f_153_);
lean_dec_ref(v_inst_152_);
v___x_169_ = lean_apply_2(v_toPure_160_, lean_box(0), v_init_154_);
return v___x_169_;
}
else
{
size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_usize_of_nat(v_stop_159_);
lean_dec(v_stop_159_);
v___x_171_ = lean_usize_of_nat(v_start_158_);
lean_dec(v_start_158_);
v___x_172_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_152_, v_f_153_, v_array_157_, v___x_170_, v___x_171_, v_init_154_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_m_175_, lean_object* v_inst_176_, lean_object* v_f_177_, lean_object* v_init_178_, lean_object* v_as_179_){
_start:
{
lean_object* v_toApplicative_180_; lean_object* v_array_181_; lean_object* v_start_182_; lean_object* v_stop_183_; lean_object* v_toPure_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_toApplicative_180_ = lean_ctor_get(v_inst_176_, 0);
v_array_181_ = lean_ctor_get(v_as_179_, 0);
lean_inc_ref(v_array_181_);
v_start_182_ = lean_ctor_get(v_as_179_, 1);
lean_inc(v_start_182_);
v_stop_183_ = lean_ctor_get(v_as_179_, 2);
lean_inc(v_stop_183_);
lean_dec_ref(v_as_179_);
v_toPure_184_ = lean_ctor_get(v_toApplicative_180_, 1);
v___x_185_ = lean_array_get_size(v_array_181_);
v___x_186_ = lean_nat_dec_le(v_stop_183_, v___x_185_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
lean_dec(v_stop_183_);
v___x_187_ = lean_nat_dec_lt(v_start_182_, v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_inc(v_toPure_184_);
lean_dec(v_start_182_);
lean_dec_ref(v_array_181_);
lean_dec(v_f_177_);
lean_dec_ref(v_inst_176_);
v___x_188_ = lean_apply_2(v_toPure_184_, lean_box(0), v_init_178_);
return v___x_188_;
}
else
{
size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_usize_of_nat(v___x_185_);
v___x_190_ = lean_usize_of_nat(v_start_182_);
lean_dec(v_start_182_);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_176_, v_f_177_, v_array_181_, v___x_189_, v___x_190_, v_init_178_);
return v___x_191_;
}
}
else
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_lt(v_start_182_, v_stop_183_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_inc(v_toPure_184_);
lean_dec(v_stop_183_);
lean_dec(v_start_182_);
lean_dec_ref(v_array_181_);
lean_dec(v_f_177_);
lean_dec_ref(v_inst_176_);
v___x_193_ = lean_apply_2(v_toPure_184_, lean_box(0), v_init_178_);
return v___x_193_;
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_usize_of_nat(v_stop_183_);
lean_dec(v_stop_183_);
v___x_195_ = lean_usize_of_nat(v_start_182_);
lean_dec(v_start_182_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_176_, v_f_177_, v_array_181_, v___x_194_, v___x_195_, v_init_178_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM___redArg(lean_object* v_inst_197_, lean_object* v_p_198_, lean_object* v_as_199_){
_start:
{
lean_object* v_toApplicative_200_; lean_object* v_array_201_; lean_object* v_start_202_; lean_object* v_stop_203_; lean_object* v_toPure_204_; lean_object* v___y_206_; uint8_t v___x_213_; 
v_toApplicative_200_ = lean_ctor_get(v_inst_197_, 0);
v_array_201_ = lean_ctor_get(v_as_199_, 0);
lean_inc_ref(v_array_201_);
v_start_202_ = lean_ctor_get(v_as_199_, 1);
lean_inc(v_start_202_);
v_stop_203_ = lean_ctor_get(v_as_199_, 2);
lean_inc(v_stop_203_);
lean_dec_ref(v_as_199_);
v_toPure_204_ = lean_ctor_get(v_toApplicative_200_, 1);
v___x_213_ = lean_nat_dec_lt(v_start_202_, v_stop_203_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_inc(v_toPure_204_);
lean_dec(v_stop_203_);
lean_dec(v_start_202_);
lean_dec_ref(v_array_201_);
lean_dec(v_p_198_);
lean_dec_ref(v_inst_197_);
v___x_214_ = lean_box(v___x_213_);
v___x_215_ = lean_apply_2(v_toPure_204_, lean_box(0), v___x_214_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_get_size(v_array_201_);
v___x_217_ = lean_nat_dec_le(v_stop_203_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_stop_203_);
v___y_206_ = v___x_216_;
goto v___jp_205_;
}
else
{
v___y_206_ = v_stop_203_;
goto v___jp_205_;
}
}
v___jp_205_:
{
uint8_t v___x_207_; 
v___x_207_ = lean_nat_dec_lt(v_start_202_, v___y_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc(v_toPure_204_);
lean_dec(v___y_206_);
lean_dec(v_start_202_);
lean_dec_ref(v_array_201_);
lean_dec(v_p_198_);
lean_dec_ref(v_inst_197_);
v___x_208_ = lean_box(v___x_207_);
v___x_209_ = lean_apply_2(v_toPure_204_, lean_box(0), v___x_208_);
return v___x_209_;
}
else
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_usize_of_nat(v_start_202_);
lean_dec(v_start_202_);
v___x_211_ = lean_usize_of_nat(v___y_206_);
lean_dec(v___y_206_);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_197_, v_p_198_, v_array_201_, v___x_210_, v___x_211_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM(lean_object* v_00_u03b1_218_, lean_object* v_m_219_, lean_object* v_inst_220_, lean_object* v_p_221_, lean_object* v_as_222_){
_start:
{
lean_object* v_toApplicative_223_; lean_object* v_array_224_; lean_object* v_start_225_; lean_object* v_stop_226_; lean_object* v_toPure_227_; lean_object* v___y_229_; uint8_t v___x_236_; 
v_toApplicative_223_ = lean_ctor_get(v_inst_220_, 0);
v_array_224_ = lean_ctor_get(v_as_222_, 0);
lean_inc_ref(v_array_224_);
v_start_225_ = lean_ctor_get(v_as_222_, 1);
lean_inc(v_start_225_);
v_stop_226_ = lean_ctor_get(v_as_222_, 2);
lean_inc(v_stop_226_);
lean_dec_ref(v_as_222_);
v_toPure_227_ = lean_ctor_get(v_toApplicative_223_, 1);
v___x_236_ = lean_nat_dec_lt(v_start_225_, v_stop_226_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_inc(v_toPure_227_);
lean_dec(v_stop_226_);
lean_dec(v_start_225_);
lean_dec_ref(v_array_224_);
lean_dec(v_p_221_);
lean_dec_ref(v_inst_220_);
v___x_237_ = lean_box(v___x_236_);
v___x_238_ = lean_apply_2(v_toPure_227_, lean_box(0), v___x_237_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_array_get_size(v_array_224_);
v___x_240_ = lean_nat_dec_le(v_stop_226_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v_stop_226_);
v___y_229_ = v___x_239_;
goto v___jp_228_;
}
else
{
v___y_229_ = v_stop_226_;
goto v___jp_228_;
}
}
v___jp_228_:
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_lt(v_start_225_, v___y_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_inc(v_toPure_227_);
lean_dec(v___y_229_);
lean_dec(v_start_225_);
lean_dec_ref(v_array_224_);
lean_dec(v_p_221_);
lean_dec_ref(v_inst_220_);
v___x_231_ = lean_box(v___x_230_);
v___x_232_ = lean_apply_2(v_toPure_227_, lean_box(0), v___x_231_);
return v___x_232_;
}
else
{
size_t v___x_233_; size_t v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_usize_of_nat(v_start_225_);
lean_dec(v_start_225_);
v___x_234_ = lean_usize_of_nat(v___y_229_);
lean_dec(v___y_229_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_220_, v_p_221_, v_array_224_, v___x_233_, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0(lean_object* v_toPure_241_, uint8_t v_____do__lift_242_){
_start:
{
if (v_____do__lift_242_ == 0)
{
uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = 1;
v___x_244_ = lean_box(v___x_243_);
v___x_245_ = lean_apply_2(v_toPure_241_, lean_box(0), v___x_244_);
return v___x_245_;
}
else
{
uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = 0;
v___x_247_ = lean_box(v___x_246_);
v___x_248_ = lean_apply_2(v_toPure_241_, lean_box(0), v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0___boxed(lean_object* v_toPure_249_, lean_object* v_____do__lift_250_){
_start:
{
uint8_t v_____do__lift_110__boxed_251_; lean_object* v_res_252_; 
v_____do__lift_110__boxed_251_ = lean_unbox(v_____do__lift_250_);
v_res_252_ = l_Subarray_allM___redArg___lam__0(v_toPure_249_, v_____do__lift_110__boxed_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1(lean_object* v_toPure_253_, uint8_t v___x_254_, uint8_t v_____do__lift_255_){
_start:
{
if (v_____do__lift_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_box(v___x_254_);
v___x_257_ = lean_apply_2(v_toPure_253_, lean_box(0), v___x_256_);
return v___x_257_;
}
else
{
uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = 0;
v___x_259_ = lean_box(v___x_258_);
v___x_260_ = lean_apply_2(v_toPure_253_, lean_box(0), v___x_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1___boxed(lean_object* v_toPure_261_, lean_object* v___x_262_, lean_object* v_____do__lift_263_){
_start:
{
uint8_t v___x_125__boxed_264_; uint8_t v_____do__lift_126__boxed_265_; lean_object* v_res_266_; 
v___x_125__boxed_264_ = lean_unbox(v___x_262_);
v_____do__lift_126__boxed_265_ = lean_unbox(v_____do__lift_263_);
v_res_266_ = l_Subarray_allM___redArg___lam__1(v_toPure_261_, v___x_125__boxed_264_, v_____do__lift_126__boxed_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__2(lean_object* v_p_267_, lean_object* v_toBind_268_, lean_object* v___f_269_, lean_object* v_v_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_apply_1(v_p_267_, v_v_270_);
v___x_272_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v___x_271_, v___f_269_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg(lean_object* v_inst_273_, lean_object* v_p_274_, lean_object* v_as_275_){
_start:
{
lean_object* v_toApplicative_276_; lean_object* v_array_277_; lean_object* v_start_278_; lean_object* v_stop_279_; lean_object* v_toBind_280_; lean_object* v_toPure_281_; lean_object* v___f_282_; uint8_t v___x_283_; 
v_toApplicative_276_ = lean_ctor_get(v_inst_273_, 0);
v_array_277_ = lean_ctor_get(v_as_275_, 0);
lean_inc_ref(v_array_277_);
v_start_278_ = lean_ctor_get(v_as_275_, 1);
lean_inc(v_start_278_);
v_stop_279_ = lean_ctor_get(v_as_275_, 2);
lean_inc(v_stop_279_);
lean_dec_ref(v_as_275_);
v_toBind_280_ = lean_ctor_get(v_inst_273_, 1);
lean_inc(v_toBind_280_);
v_toPure_281_ = lean_ctor_get(v_toApplicative_276_, 1);
lean_inc(v_toPure_281_);
v___f_282_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_282_, 0, v_toPure_281_);
v___x_283_ = lean_nat_dec_lt(v_start_278_, v_stop_279_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_inc(v_toPure_281_);
lean_dec(v_stop_279_);
lean_dec(v_start_278_);
lean_dec_ref(v_array_277_);
lean_dec(v_p_274_);
lean_dec_ref(v_inst_273_);
v___x_284_ = lean_box(v___x_283_);
v___x_285_ = lean_apply_2(v_toPure_281_, lean_box(0), v___x_284_);
v___x_286_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_285_, v___f_282_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___f_289_; lean_object* v___y_291_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_287_ = lean_box(v___x_283_);
lean_inc(v_toPure_281_);
v___f_288_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_288_, 0, v_toPure_281_);
lean_closure_set(v___f_288_, 1, v___x_287_);
lean_inc(v_toBind_280_);
v___f_289_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_289_, 0, v_p_274_);
lean_closure_set(v___f_289_, 1, v_toBind_280_);
lean_closure_set(v___f_289_, 2, v___f_288_);
v___x_300_ = lean_array_get_size(v_array_277_);
v___x_301_ = lean_nat_dec_le(v_stop_279_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v_stop_279_);
v___y_291_ = v___x_300_;
goto v___jp_290_;
}
else
{
v___y_291_ = v_stop_279_;
goto v___jp_290_;
}
v___jp_290_:
{
uint8_t v___x_292_; 
v___x_292_ = lean_nat_dec_lt(v_start_278_, v___y_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_inc(v_toPure_281_);
lean_dec(v___y_291_);
lean_dec_ref(v___f_289_);
lean_dec(v_start_278_);
lean_dec_ref(v_array_277_);
lean_dec_ref(v_inst_273_);
v___x_293_ = lean_box(v___x_292_);
v___x_294_ = lean_apply_2(v_toPure_281_, lean_box(0), v___x_293_);
v___x_295_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_294_, v___f_282_);
return v___x_295_;
}
else
{
size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = lean_usize_of_nat(v_start_278_);
lean_dec(v_start_278_);
v___x_297_ = lean_usize_of_nat(v___y_291_);
lean_dec(v___y_291_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_273_, v___f_289_, v_array_277_, v___x_296_, v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_298_, v___f_282_);
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM(lean_object* v_00_u03b1_302_, lean_object* v_m_303_, lean_object* v_inst_304_, lean_object* v_p_305_, lean_object* v_as_306_){
_start:
{
lean_object* v_toApplicative_307_; lean_object* v_array_308_; lean_object* v_start_309_; lean_object* v_stop_310_; lean_object* v_toBind_311_; lean_object* v_toPure_312_; lean_object* v___f_313_; uint8_t v___x_314_; 
v_toApplicative_307_ = lean_ctor_get(v_inst_304_, 0);
v_array_308_ = lean_ctor_get(v_as_306_, 0);
lean_inc_ref(v_array_308_);
v_start_309_ = lean_ctor_get(v_as_306_, 1);
lean_inc(v_start_309_);
v_stop_310_ = lean_ctor_get(v_as_306_, 2);
lean_inc(v_stop_310_);
lean_dec_ref(v_as_306_);
v_toBind_311_ = lean_ctor_get(v_inst_304_, 1);
lean_inc(v_toBind_311_);
v_toPure_312_ = lean_ctor_get(v_toApplicative_307_, 1);
lean_inc(v_toPure_312_);
v___f_313_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_313_, 0, v_toPure_312_);
v___x_314_ = lean_nat_dec_lt(v_start_309_, v_stop_310_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc(v_toPure_312_);
lean_dec(v_stop_310_);
lean_dec(v_start_309_);
lean_dec_ref(v_array_308_);
lean_dec(v_p_305_);
lean_dec_ref(v_inst_304_);
v___x_315_ = lean_box(v___x_314_);
v___x_316_ = lean_apply_2(v_toPure_312_, lean_box(0), v___x_315_);
v___x_317_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_316_, v___f_313_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___y_322_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_318_ = lean_box(v___x_314_);
lean_inc(v_toPure_312_);
v___f_319_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_319_, 0, v_toPure_312_);
lean_closure_set(v___f_319_, 1, v___x_318_);
lean_inc(v_toBind_311_);
v___f_320_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_320_, 0, v_p_305_);
lean_closure_set(v___f_320_, 1, v_toBind_311_);
lean_closure_set(v___f_320_, 2, v___f_319_);
v___x_331_ = lean_array_get_size(v_array_308_);
v___x_332_ = lean_nat_dec_le(v_stop_310_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec(v_stop_310_);
v___y_322_ = v___x_331_;
goto v___jp_321_;
}
else
{
v___y_322_ = v_stop_310_;
goto v___jp_321_;
}
v___jp_321_:
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_lt(v_start_309_, v___y_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_inc(v_toPure_312_);
lean_dec(v___y_322_);
lean_dec_ref(v___f_320_);
lean_dec(v_start_309_);
lean_dec_ref(v_array_308_);
lean_dec_ref(v_inst_304_);
v___x_324_ = lean_box(v___x_323_);
v___x_325_ = lean_apply_2(v_toPure_312_, lean_box(0), v___x_324_);
v___x_326_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_325_, v___f_313_);
return v___x_326_;
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_usize_of_nat(v_start_309_);
lean_dec(v_start_309_);
v___x_328_ = lean_usize_of_nat(v___y_322_);
lean_dec(v___y_322_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_304_, v___f_320_, v_array_308_, v___x_327_, v___x_328_);
v___x_330_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_329_, v___f_313_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg___lam__0(lean_object* v_f_333_, lean_object* v_x_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_apply_1(v_f_333_, v___y_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg(lean_object* v_inst_337_, lean_object* v_f_338_, lean_object* v_as_339_){
_start:
{
lean_object* v_toApplicative_340_; lean_object* v_array_341_; lean_object* v_start_342_; lean_object* v_stop_343_; lean_object* v_toPure_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_337_, 0);
v_array_341_ = lean_ctor_get(v_as_339_, 0);
lean_inc_ref(v_array_341_);
v_start_342_ = lean_ctor_get(v_as_339_, 1);
lean_inc(v_start_342_);
v_stop_343_ = lean_ctor_get(v_as_339_, 2);
lean_inc(v_stop_343_);
lean_dec_ref(v_as_339_);
v_toPure_344_ = lean_ctor_get(v_toApplicative_340_, 1);
v___x_345_ = lean_box(0);
v___x_346_ = lean_nat_dec_lt(v_start_342_, v_stop_343_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_inc(v_toPure_344_);
lean_dec(v_stop_343_);
lean_dec(v_start_342_);
lean_dec_ref(v_array_341_);
lean_dec(v_f_338_);
lean_dec_ref(v_inst_337_);
v___x_347_ = lean_apply_2(v_toPure_344_, lean_box(0), v___x_345_);
return v___x_347_;
}
else
{
lean_object* v___f_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___f_348_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_348_, 0, v_f_338_);
v___x_349_ = lean_array_get_size(v_array_341_);
v___x_350_ = lean_nat_dec_le(v_stop_343_, v___x_349_);
if (v___x_350_ == 0)
{
uint8_t v___x_351_; 
lean_dec(v_stop_343_);
v___x_351_ = lean_nat_dec_lt(v_start_342_, v___x_349_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_inc(v_toPure_344_);
lean_dec_ref(v___f_348_);
lean_dec(v_start_342_);
lean_dec_ref(v_array_341_);
lean_dec_ref(v_inst_337_);
v___x_352_ = lean_apply_2(v_toPure_344_, lean_box(0), v___x_345_);
return v___x_352_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_usize_of_nat(v_start_342_);
lean_dec(v_start_342_);
v___x_354_ = lean_usize_of_nat(v___x_349_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_337_, v___f_348_, v_array_341_, v___x_353_, v___x_354_, v___x_345_);
return v___x_355_;
}
}
else
{
size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_usize_of_nat(v_start_342_);
lean_dec(v_start_342_);
v___x_357_ = lean_usize_of_nat(v_stop_343_);
lean_dec(v_stop_343_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_337_, v___f_348_, v_array_341_, v___x_356_, v___x_357_, v___x_345_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM(lean_object* v_00_u03b1_359_, lean_object* v_m_360_, lean_object* v_inst_361_, lean_object* v_f_362_, lean_object* v_as_363_){
_start:
{
lean_object* v_toApplicative_364_; lean_object* v_array_365_; lean_object* v_start_366_; lean_object* v_stop_367_; lean_object* v_toPure_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_toApplicative_364_ = lean_ctor_get(v_inst_361_, 0);
v_array_365_ = lean_ctor_get(v_as_363_, 0);
lean_inc_ref(v_array_365_);
v_start_366_ = lean_ctor_get(v_as_363_, 1);
lean_inc(v_start_366_);
v_stop_367_ = lean_ctor_get(v_as_363_, 2);
lean_inc(v_stop_367_);
lean_dec_ref(v_as_363_);
v_toPure_368_ = lean_ctor_get(v_toApplicative_364_, 1);
v___x_369_ = lean_box(0);
v___x_370_ = lean_nat_dec_lt(v_start_366_, v_stop_367_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_inc(v_toPure_368_);
lean_dec(v_stop_367_);
lean_dec(v_start_366_);
lean_dec_ref(v_array_365_);
lean_dec(v_f_362_);
lean_dec_ref(v_inst_361_);
v___x_371_ = lean_apply_2(v_toPure_368_, lean_box(0), v___x_369_);
return v___x_371_;
}
else
{
lean_object* v___f_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___f_372_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_372_, 0, v_f_362_);
v___x_373_ = lean_array_get_size(v_array_365_);
v___x_374_ = lean_nat_dec_le(v_stop_367_, v___x_373_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
lean_dec(v_stop_367_);
v___x_375_ = lean_nat_dec_lt(v_start_366_, v___x_373_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_inc(v_toPure_368_);
lean_dec_ref(v___f_372_);
lean_dec(v_start_366_);
lean_dec_ref(v_array_365_);
lean_dec_ref(v_inst_361_);
v___x_376_ = lean_apply_2(v_toPure_368_, lean_box(0), v___x_369_);
return v___x_376_;
}
else
{
size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_usize_of_nat(v_start_366_);
lean_dec(v_start_366_);
v___x_378_ = lean_usize_of_nat(v___x_373_);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_361_, v___f_372_, v_array_365_, v___x_377_, v___x_378_, v___x_369_);
return v___x_379_;
}
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_usize_of_nat(v_start_366_);
lean_dec(v_start_366_);
v___x_381_ = lean_usize_of_nat(v_stop_367_);
lean_dec(v_stop_367_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_361_, v___f_372_, v_array_365_, v___x_380_, v___x_381_, v___x_369_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg___lam__0(lean_object* v_f_383_, lean_object* v_a_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_apply_1(v_f_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg(lean_object* v_inst_387_, lean_object* v_f_388_, lean_object* v_as_389_){
_start:
{
lean_object* v_toApplicative_390_; lean_object* v_array_391_; lean_object* v_start_392_; lean_object* v_stop_393_; lean_object* v_toPure_394_; lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_toApplicative_390_ = lean_ctor_get(v_inst_387_, 0);
v_array_391_ = lean_ctor_get(v_as_389_, 0);
lean_inc_ref(v_array_391_);
v_start_392_ = lean_ctor_get(v_as_389_, 1);
lean_inc(v_start_392_);
v_stop_393_ = lean_ctor_get(v_as_389_, 2);
lean_inc(v_stop_393_);
lean_dec_ref(v_as_389_);
v_toPure_394_ = lean_ctor_get(v_toApplicative_390_, 1);
v___f_395_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_395_, 0, v_f_388_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_array_get_size(v_array_391_);
v___x_398_ = lean_nat_dec_le(v_stop_393_, v___x_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
lean_dec(v_stop_393_);
v___x_399_ = lean_nat_dec_lt(v_start_392_, v___x_397_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_inc(v_toPure_394_);
lean_dec_ref(v___f_395_);
lean_dec(v_start_392_);
lean_dec_ref(v_array_391_);
lean_dec_ref(v_inst_387_);
v___x_400_ = lean_apply_2(v_toPure_394_, lean_box(0), v___x_396_);
return v___x_400_;
}
else
{
size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_usize_of_nat(v___x_397_);
v___x_402_ = lean_usize_of_nat(v_start_392_);
lean_dec(v_start_392_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_387_, v___f_395_, v_array_391_, v___x_401_, v___x_402_, v___x_396_);
return v___x_403_;
}
}
else
{
uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_lt(v_start_392_, v_stop_393_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_inc(v_toPure_394_);
lean_dec_ref(v___f_395_);
lean_dec(v_stop_393_);
lean_dec(v_start_392_);
lean_dec_ref(v_array_391_);
lean_dec_ref(v_inst_387_);
v___x_405_ = lean_apply_2(v_toPure_394_, lean_box(0), v___x_396_);
return v___x_405_;
}
else
{
size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_usize_of_nat(v_stop_393_);
lean_dec(v_stop_393_);
v___x_407_ = lean_usize_of_nat(v_start_392_);
lean_dec(v_start_392_);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_387_, v___f_395_, v_array_391_, v___x_406_, v___x_407_, v___x_396_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM(lean_object* v_00_u03b1_409_, lean_object* v_m_410_, lean_object* v_inst_411_, lean_object* v_f_412_, lean_object* v_as_413_){
_start:
{
lean_object* v_toApplicative_414_; lean_object* v_array_415_; lean_object* v_start_416_; lean_object* v_stop_417_; lean_object* v_toPure_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_toApplicative_414_ = lean_ctor_get(v_inst_411_, 0);
v_array_415_ = lean_ctor_get(v_as_413_, 0);
lean_inc_ref(v_array_415_);
v_start_416_ = lean_ctor_get(v_as_413_, 1);
lean_inc(v_start_416_);
v_stop_417_ = lean_ctor_get(v_as_413_, 2);
lean_inc(v_stop_417_);
lean_dec_ref(v_as_413_);
v_toPure_418_ = lean_ctor_get(v_toApplicative_414_, 1);
v___f_419_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_419_, 0, v_f_412_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_array_get_size(v_array_415_);
v___x_422_ = lean_nat_dec_le(v_stop_417_, v___x_421_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
lean_dec(v_stop_417_);
v___x_423_ = lean_nat_dec_lt(v_start_416_, v___x_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_inc(v_toPure_418_);
lean_dec_ref(v___f_419_);
lean_dec(v_start_416_);
lean_dec_ref(v_array_415_);
lean_dec_ref(v_inst_411_);
v___x_424_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_420_);
return v___x_424_;
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_usize_of_nat(v___x_421_);
v___x_426_ = lean_usize_of_nat(v_start_416_);
lean_dec(v_start_416_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_411_, v___f_419_, v_array_415_, v___x_425_, v___x_426_, v___x_420_);
return v___x_427_;
}
}
else
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_lt(v_start_416_, v_stop_417_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_inc(v_toPure_418_);
lean_dec_ref(v___f_419_);
lean_dec(v_stop_417_);
lean_dec(v_start_416_);
lean_dec_ref(v_array_415_);
lean_dec_ref(v_inst_411_);
v___x_429_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_420_);
return v___x_429_;
}
else
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_usize_of_nat(v_stop_417_);
lean_dec(v_stop_417_);
v___x_431_ = lean_usize_of_nat(v_start_416_);
lean_dec(v_start_416_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_411_, v___f_419_, v_array_415_, v___x_430_, v___x_431_, v___x_420_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg___lam__0(lean_object* v_f_433_, lean_object* v_x1_434_, lean_object* v_x2_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_apply_2(v_f_433_, v_x1_434_, v_x2_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg(lean_object* v_f_456_, lean_object* v_init_457_, lean_object* v_as_458_){
_start:
{
lean_object* v___x_459_; lean_object* v_array_460_; lean_object* v_start_461_; lean_object* v_stop_462_; lean_object* v___f_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_459_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_460_ = lean_ctor_get(v_as_458_, 0);
lean_inc_ref(v_array_460_);
v_start_461_ = lean_ctor_get(v_as_458_, 1);
lean_inc(v_start_461_);
v_stop_462_ = lean_ctor_get(v_as_458_, 2);
lean_inc(v_stop_462_);
lean_dec_ref(v_as_458_);
v___f_463_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_463_, 0, v_f_456_);
v___x_464_ = lean_array_get_size(v_array_460_);
v___x_465_ = lean_nat_dec_le(v_stop_462_, v___x_464_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
lean_dec(v_stop_462_);
v___x_466_ = lean_nat_dec_lt(v_start_461_, v___x_464_);
if (v___x_466_ == 0)
{
lean_dec_ref(v___f_463_);
lean_dec(v_start_461_);
lean_dec_ref(v_array_460_);
return v_init_457_;
}
else
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_usize_of_nat(v___x_464_);
v___x_468_ = lean_usize_of_nat(v_start_461_);
lean_dec(v_start_461_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_459_, v___f_463_, v_array_460_, v___x_467_, v___x_468_, v_init_457_);
return v___x_469_;
}
}
else
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_lt(v_start_461_, v_stop_462_);
if (v___x_470_ == 0)
{
lean_dec_ref(v___f_463_);
lean_dec(v_stop_462_);
lean_dec(v_start_461_);
lean_dec_ref(v_array_460_);
return v_init_457_;
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_usize_of_nat(v_stop_462_);
lean_dec(v_stop_462_);
v___x_472_ = lean_usize_of_nat(v_start_461_);
lean_dec(v_start_461_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_459_, v___f_463_, v_array_460_, v___x_471_, v___x_472_, v_init_457_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_f_476_, lean_object* v_init_477_, lean_object* v_as_478_){
_start:
{
lean_object* v___x_479_; lean_object* v_array_480_; lean_object* v_start_481_; lean_object* v_stop_482_; lean_object* v___f_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_479_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_480_ = lean_ctor_get(v_as_478_, 0);
lean_inc_ref(v_array_480_);
v_start_481_ = lean_ctor_get(v_as_478_, 1);
lean_inc(v_start_481_);
v_stop_482_ = lean_ctor_get(v_as_478_, 2);
lean_inc(v_stop_482_);
lean_dec_ref(v_as_478_);
v___f_483_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_483_, 0, v_f_476_);
v___x_484_ = lean_array_get_size(v_array_480_);
v___x_485_ = lean_nat_dec_le(v_stop_482_, v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
lean_dec(v_stop_482_);
v___x_486_ = lean_nat_dec_lt(v_start_481_, v___x_484_);
if (v___x_486_ == 0)
{
lean_dec_ref(v___f_483_);
lean_dec(v_start_481_);
lean_dec_ref(v_array_480_);
return v_init_477_;
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_usize_of_nat(v___x_484_);
v___x_488_ = lean_usize_of_nat(v_start_481_);
lean_dec(v_start_481_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_479_, v___f_483_, v_array_480_, v___x_487_, v___x_488_, v_init_477_);
return v___x_489_;
}
}
else
{
uint8_t v___x_490_; 
v___x_490_ = lean_nat_dec_lt(v_start_481_, v_stop_482_);
if (v___x_490_ == 0)
{
lean_dec_ref(v___f_483_);
lean_dec(v_stop_482_);
lean_dec(v_start_481_);
lean_dec_ref(v_array_480_);
return v_init_477_;
}
else
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_usize_of_nat(v_stop_482_);
lean_dec(v_stop_482_);
v___x_492_ = lean_usize_of_nat(v_start_481_);
lean_dec(v_start_481_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_479_, v___f_483_, v_array_480_, v___x_491_, v___x_492_, v_init_477_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg___lam__0(lean_object* v_p_494_, lean_object* v_x_495_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_apply_1(v_p_494_, v_x_495_);
v___x_497_ = lean_unbox(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___lam__0___boxed(lean_object* v_p_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Subarray_any___redArg___lam__0(v_p_498_, v_x_499_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg(lean_object* v_p_502_, lean_object* v_as_503_){
_start:
{
lean_object* v___x_504_; lean_object* v_array_505_; lean_object* v_start_506_; lean_object* v_stop_507_; uint8_t v___x_508_; 
v___x_504_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_505_ = lean_ctor_get(v_as_503_, 0);
lean_inc_ref(v_array_505_);
v_start_506_ = lean_ctor_get(v_as_503_, 1);
lean_inc(v_start_506_);
v_stop_507_ = lean_ctor_get(v_as_503_, 2);
lean_inc(v_stop_507_);
lean_dec_ref(v_as_503_);
v___x_508_ = lean_nat_dec_lt(v_start_506_, v_stop_507_);
if (v___x_508_ == 0)
{
lean_dec(v_stop_507_);
lean_dec(v_start_506_);
lean_dec_ref(v_array_505_);
lean_dec_ref(v_p_502_);
return v___x_508_;
}
else
{
lean_object* v___f_509_; lean_object* v___y_511_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___f_509_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_509_, 0, v_p_502_);
v___x_517_ = lean_array_get_size(v_array_505_);
v___x_518_ = lean_nat_dec_le(v_stop_507_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec(v_stop_507_);
v___y_511_ = v___x_517_;
goto v___jp_510_;
}
else
{
v___y_511_ = v_stop_507_;
goto v___jp_510_;
}
v___jp_510_:
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_lt(v_start_506_, v___y_511_);
if (v___x_512_ == 0)
{
lean_dec(v___y_511_);
lean_dec_ref(v___f_509_);
lean_dec(v_start_506_);
lean_dec_ref(v_array_505_);
return v___x_512_;
}
else
{
size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_usize_of_nat(v_start_506_);
lean_dec(v_start_506_);
v___x_514_ = lean_usize_of_nat(v___y_511_);
lean_dec(v___y_511_);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_504_, v___f_509_, v_array_505_, v___x_513_, v___x_514_);
v___x_516_ = lean_unbox(v___x_515_);
lean_dec(v___x_515_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___boxed(lean_object* v_p_519_, lean_object* v_as_520_){
_start:
{
uint8_t v_res_521_; lean_object* v_r_522_; 
v_res_521_ = l_Subarray_any___redArg(v_p_519_, v_as_520_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any(lean_object* v_00_u03b1_523_, lean_object* v_p_524_, lean_object* v_as_525_){
_start:
{
lean_object* v___x_526_; lean_object* v_array_527_; lean_object* v_start_528_; lean_object* v_stop_529_; uint8_t v___x_530_; 
v___x_526_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_527_ = lean_ctor_get(v_as_525_, 0);
lean_inc_ref(v_array_527_);
v_start_528_ = lean_ctor_get(v_as_525_, 1);
lean_inc(v_start_528_);
v_stop_529_ = lean_ctor_get(v_as_525_, 2);
lean_inc(v_stop_529_);
lean_dec_ref(v_as_525_);
v___x_530_ = lean_nat_dec_lt(v_start_528_, v_stop_529_);
if (v___x_530_ == 0)
{
lean_dec(v_stop_529_);
lean_dec(v_start_528_);
lean_dec_ref(v_array_527_);
lean_dec_ref(v_p_524_);
return v___x_530_;
}
else
{
lean_object* v___f_531_; lean_object* v___y_533_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___f_531_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_531_, 0, v_p_524_);
v___x_539_ = lean_array_get_size(v_array_527_);
v___x_540_ = lean_nat_dec_le(v_stop_529_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec(v_stop_529_);
v___y_533_ = v___x_539_;
goto v___jp_532_;
}
else
{
v___y_533_ = v_stop_529_;
goto v___jp_532_;
}
v___jp_532_:
{
uint8_t v___x_534_; 
v___x_534_ = lean_nat_dec_lt(v_start_528_, v___y_533_);
if (v___x_534_ == 0)
{
lean_dec(v___y_533_);
lean_dec_ref(v___f_531_);
lean_dec(v_start_528_);
lean_dec_ref(v_array_527_);
return v___x_534_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_535_ = lean_usize_of_nat(v_start_528_);
lean_dec(v_start_528_);
v___x_536_ = lean_usize_of_nat(v___y_533_);
lean_dec(v___y_533_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_526_, v___f_531_, v_array_527_, v___x_535_, v___x_536_);
v___x_538_ = lean_unbox(v___x_537_);
lean_dec(v___x_537_);
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___boxed(lean_object* v_00_u03b1_541_, lean_object* v_p_542_, lean_object* v_as_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l_Subarray_any(v_00_u03b1_541_, v_p_542_, v_as_543_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg___lam__0(lean_object* v_p_546_, uint8_t v___x_547_, lean_object* v_v_548_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_apply_1(v_p_546_, v_v_548_);
v___x_550_ = lean_unbox(v___x_549_);
if (v___x_550_ == 0)
{
return v___x_547_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = 0;
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object* v_p_552_, lean_object* v___x_553_, lean_object* v_v_554_){
_start:
{
uint8_t v___x_337__boxed_555_; uint8_t v_res_556_; lean_object* v_r_557_; 
v___x_337__boxed_555_ = lean_unbox(v___x_553_);
v_res_556_ = l_Subarray_all___redArg___lam__0(v_p_552_, v___x_337__boxed_555_, v_v_554_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg(lean_object* v_p_558_, lean_object* v_as_559_){
_start:
{
lean_object* v___x_560_; lean_object* v_array_561_; lean_object* v_start_562_; lean_object* v_stop_563_; uint8_t v___x_564_; 
v___x_560_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_561_ = lean_ctor_get(v_as_559_, 0);
lean_inc_ref(v_array_561_);
v_start_562_ = lean_ctor_get(v_as_559_, 1);
lean_inc(v_start_562_);
v_stop_563_ = lean_ctor_get(v_as_559_, 2);
lean_inc(v_stop_563_);
lean_dec_ref(v_as_559_);
v___x_564_ = lean_nat_dec_lt(v_start_562_, v_stop_563_);
if (v___x_564_ == 0)
{
uint8_t v___x_565_; 
lean_dec(v_stop_563_);
lean_dec(v_start_562_);
lean_dec_ref(v_array_561_);
lean_dec_ref(v_p_558_);
v___x_565_ = 1;
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___f_567_; lean_object* v___y_569_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_566_ = lean_box(v___x_564_);
v___f_567_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_567_, 0, v_p_558_);
lean_closure_set(v___f_567_, 1, v___x_566_);
v___x_576_ = lean_array_get_size(v_array_561_);
v___x_577_ = lean_nat_dec_le(v_stop_563_, v___x_576_);
if (v___x_577_ == 0)
{
lean_dec(v_stop_563_);
v___y_569_ = v___x_576_;
goto v___jp_568_;
}
else
{
v___y_569_ = v_stop_563_;
goto v___jp_568_;
}
v___jp_568_:
{
uint8_t v___x_570_; 
v___x_570_ = lean_nat_dec_lt(v_start_562_, v___y_569_);
if (v___x_570_ == 0)
{
lean_dec(v___y_569_);
lean_dec_ref(v___f_567_);
lean_dec(v_start_562_);
lean_dec_ref(v_array_561_);
return v___x_564_;
}
else
{
size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_571_ = lean_usize_of_nat(v_start_562_);
lean_dec(v_start_562_);
v___x_572_ = lean_usize_of_nat(v___y_569_);
lean_dec(v___y_569_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_560_, v___f_567_, v_array_561_, v___x_571_, v___x_572_);
v___x_574_ = lean_unbox(v___x_573_);
lean_dec(v___x_573_);
if (v___x_574_ == 0)
{
return v___x_570_;
}
else
{
uint8_t v___x_575_; 
v___x_575_ = 0;
return v___x_575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___boxed(lean_object* v_p_578_, lean_object* v_as_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l_Subarray_all___redArg(v_p_578_, v_as_579_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all(lean_object* v_00_u03b1_582_, lean_object* v_p_583_, lean_object* v_as_584_){
_start:
{
lean_object* v___x_585_; lean_object* v_array_586_; lean_object* v_start_587_; lean_object* v_stop_588_; uint8_t v___x_589_; 
v___x_585_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_586_ = lean_ctor_get(v_as_584_, 0);
lean_inc_ref(v_array_586_);
v_start_587_ = lean_ctor_get(v_as_584_, 1);
lean_inc(v_start_587_);
v_stop_588_ = lean_ctor_get(v_as_584_, 2);
lean_inc(v_stop_588_);
lean_dec_ref(v_as_584_);
v___x_589_ = lean_nat_dec_lt(v_start_587_, v_stop_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
lean_dec(v_stop_588_);
lean_dec(v_start_587_);
lean_dec_ref(v_array_586_);
lean_dec_ref(v_p_583_);
v___x_590_ = 1;
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___y_594_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_591_ = lean_box(v___x_589_);
v___f_592_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_592_, 0, v_p_583_);
lean_closure_set(v___f_592_, 1, v___x_591_);
v___x_601_ = lean_array_get_size(v_array_586_);
v___x_602_ = lean_nat_dec_le(v_stop_588_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_stop_588_);
v___y_594_ = v___x_601_;
goto v___jp_593_;
}
else
{
v___y_594_ = v_stop_588_;
goto v___jp_593_;
}
v___jp_593_:
{
uint8_t v___x_595_; 
v___x_595_ = lean_nat_dec_lt(v_start_587_, v___y_594_);
if (v___x_595_ == 0)
{
lean_dec(v___y_594_);
lean_dec_ref(v___f_592_);
lean_dec(v_start_587_);
lean_dec_ref(v_array_586_);
return v___x_589_;
}
else
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_596_ = lean_usize_of_nat(v_start_587_);
lean_dec(v_start_587_);
v___x_597_ = lean_usize_of_nat(v___y_594_);
lean_dec(v___y_594_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_585_, v___f_592_, v_array_586_, v___x_596_, v___x_597_);
v___x_599_ = lean_unbox(v___x_598_);
lean_dec(v___x_598_);
if (v___x_599_ == 0)
{
return v___x_595_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___boxed(lean_object* v_00_u03b1_603_, lean_object* v_p_604_, lean_object* v_as_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Subarray_all(v_00_u03b1_603_, v_p_604_, v_as_605_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_608_, lean_object* v_as_609_, lean_object* v_f_610_, lean_object* v_n_611_, lean_object* v_toPure_612_, lean_object* v_r_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(v_inst_608_, v_as_609_, v_f_610_, v_n_611_, v_toPure_612_, v_r_613_);
lean_dec(v_n_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(lean_object* v_inst_615_, lean_object* v_as_616_, lean_object* v_f_617_, lean_object* v_i_618_){
_start:
{
lean_object* v_toApplicative_619_; lean_object* v_toBind_620_; lean_object* v_toPure_621_; lean_object* v_zero_622_; uint8_t v_isZero_623_; 
v_toApplicative_619_ = lean_ctor_get(v_inst_615_, 0);
v_toBind_620_ = lean_ctor_get(v_inst_615_, 1);
lean_inc(v_toBind_620_);
v_toPure_621_ = lean_ctor_get(v_toApplicative_619_, 1);
lean_inc(v_toPure_621_);
v_zero_622_ = lean_unsigned_to_nat(0u);
v_isZero_623_ = lean_nat_dec_eq(v_i_618_, v_zero_622_);
if (v_isZero_623_ == 1)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_toBind_620_);
lean_dec(v_f_617_);
lean_dec_ref(v_as_616_);
lean_dec_ref(v_inst_615_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_apply_2(v_toPure_621_, lean_box(0), v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_one_626_; lean_object* v_n_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_one_626_ = lean_unsigned_to_nat(1u);
v_n_627_ = lean_nat_sub(v_i_618_, v_one_626_);
lean_inc(v_n_627_);
lean_inc(v_f_617_);
lean_inc_ref(v_as_616_);
v___f_628_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_628_, 0, v_inst_615_);
lean_closure_set(v___f_628_, 1, v_as_616_);
lean_closure_set(v___f_628_, 2, v_f_617_);
lean_closure_set(v___f_628_, 3, v_n_627_);
lean_closure_set(v___f_628_, 4, v_toPure_621_);
v___x_629_ = l_Subarray_get___redArg(v_as_616_, v_n_627_);
lean_dec(v_n_627_);
lean_dec_ref(v_as_616_);
v___x_630_ = lean_apply_1(v_f_617_, v___x_629_);
v___x_631_ = lean_apply_4(v_toBind_620_, lean_box(0), lean_box(0), v___x_630_, v___f_628_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_632_, lean_object* v_as_633_, lean_object* v_f_634_, lean_object* v_n_635_, lean_object* v_toPure_636_, lean_object* v_r_637_){
_start:
{
if (lean_obj_tag(v_r_637_) == 0)
{
lean_object* v___x_638_; 
lean_dec(v_toPure_636_);
v___x_638_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_632_, v_as_633_, v_f_634_, v_n_635_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
lean_dec(v_f_634_);
lean_dec_ref(v_as_633_);
lean_dec_ref(v_inst_632_);
v___x_639_ = lean_apply_2(v_toPure_636_, lean_box(0), v_r_637_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_640_, lean_object* v_as_641_, lean_object* v_f_642_, lean_object* v_i_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_640_, v_as_641_, v_f_642_, v_i_643_);
lean_dec(v_i_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_m_647_, lean_object* v_inst_648_, lean_object* v_as_649_, lean_object* v_f_650_, lean_object* v_i_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_648_, v_as_649_, v_f_650_, v_i_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_m_656_, lean_object* v_inst_657_, lean_object* v_as_658_, lean_object* v_f_659_, lean_object* v_i_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(v_00_u03b1_654_, v_00_u03b2_655_, v_m_656_, v_inst_657_, v_as_658_, v_f_659_, v_i_660_, v_a_661_);
lean_dec(v_i_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f___redArg(lean_object* v_inst_663_, lean_object* v_as_664_, lean_object* v_f_665_){
_start:
{
lean_object* v_start_666_; lean_object* v_stop_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_start_666_ = lean_ctor_get(v_as_664_, 1);
v_stop_667_ = lean_ctor_get(v_as_664_, 2);
v___x_668_ = lean_nat_sub(v_stop_667_, v_start_666_);
v___x_669_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_663_, v_as_664_, v_f_665_, v___x_668_);
lean_dec(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f(lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_as_674_, lean_object* v_f_675_){
_start:
{
lean_object* v_start_676_; lean_object* v_stop_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_start_676_ = lean_ctor_get(v_as_674_, 1);
v_stop_677_ = lean_ctor_get(v_as_674_, 2);
v___x_678_ = lean_nat_sub(v_stop_677_, v_start_676_);
v___x_679_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_673_, v_as_674_, v_f_675_, v___x_678_);
lean_dec(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_680_, lean_object* v_a_681_, uint8_t v_____do__lift_682_){
_start:
{
if (v_____do__lift_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v_a_681_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_apply_2(v_toPure_680_, lean_box(0), v___x_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_a_681_);
v___x_686_ = lean_apply_2(v_toPure_680_, lean_box(0), v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_687_, lean_object* v_a_688_, lean_object* v_____do__lift_689_){
_start:
{
uint8_t v_____do__lift_62__boxed_690_; lean_object* v_res_691_; 
v_____do__lift_62__boxed_690_ = lean_unbox(v_____do__lift_689_);
v_res_691_ = l_Subarray_findRevM_x3f___redArg___lam__0(v_toPure_687_, v_a_688_, v_____do__lift_62__boxed_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_692_, lean_object* v_p_693_, lean_object* v_toBind_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc(v_a_695_);
v___f_696_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_696_, 0, v_toPure_692_);
lean_closure_set(v___f_696_, 1, v_a_695_);
v___x_697_ = lean_apply_1(v_p_693_, v_a_695_);
v___x_698_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v___x_697_, v___f_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg(lean_object* v_inst_699_, lean_object* v_as_700_, lean_object* v_p_701_){
_start:
{
lean_object* v_toApplicative_702_; lean_object* v_toBind_703_; lean_object* v_toPure_704_; lean_object* v_start_705_; lean_object* v_stop_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_toApplicative_702_ = lean_ctor_get(v_inst_699_, 0);
v_toBind_703_ = lean_ctor_get(v_inst_699_, 1);
v_toPure_704_ = lean_ctor_get(v_toApplicative_702_, 1);
v_start_705_ = lean_ctor_get(v_as_700_, 1);
v_stop_706_ = lean_ctor_get(v_as_700_, 2);
lean_inc(v_toBind_703_);
lean_inc(v_toPure_704_);
v___f_707_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_707_, 0, v_toPure_704_);
lean_closure_set(v___f_707_, 1, v_p_701_);
lean_closure_set(v___f_707_, 2, v_toBind_703_);
v___x_708_ = lean_nat_sub(v_stop_706_, v_start_705_);
v___x_709_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_699_, v_as_700_, v___f_707_, v___x_708_);
lean_dec(v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f(lean_object* v_00_u03b1_710_, lean_object* v_m_711_, lean_object* v_inst_712_, lean_object* v_as_713_, lean_object* v_p_714_){
_start:
{
lean_object* v_toApplicative_715_; lean_object* v_toBind_716_; lean_object* v_toPure_717_; lean_object* v_start_718_; lean_object* v_stop_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_toApplicative_715_ = lean_ctor_get(v_inst_712_, 0);
v_toBind_716_ = lean_ctor_get(v_inst_712_, 1);
v_toPure_717_ = lean_ctor_get(v_toApplicative_715_, 1);
v_start_718_ = lean_ctor_get(v_as_713_, 1);
v_stop_719_ = lean_ctor_get(v_as_713_, 2);
lean_inc(v_toBind_716_);
lean_inc(v_toPure_717_);
v___f_720_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_720_, 0, v_toPure_717_);
lean_closure_set(v___f_720_, 1, v_p_714_);
lean_closure_set(v___f_720_, 2, v_toBind_716_);
v___x_721_ = lean_nat_sub(v_stop_719_, v_start_718_);
v___x_722_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_712_, v_as_713_, v___f_720_, v___x_721_);
lean_dec(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg___lam__0(lean_object* v_p_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
lean_inc(v_a_724_);
v___x_725_ = lean_apply_1(v_p_723_, v_a_724_);
v___x_726_ = lean_unbox(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v_a_724_);
v___x_727_ = lean_box(0);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_a_724_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg(lean_object* v_as_729_, lean_object* v_p_730_){
_start:
{
lean_object* v___x_731_; lean_object* v_start_732_; lean_object* v_stop_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_731_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_732_ = lean_ctor_get(v_as_729_, 1);
v_stop_733_ = lean_ctor_get(v_as_729_, 2);
v___f_734_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_734_, 0, v_p_730_);
v___x_735_ = lean_nat_sub(v_stop_733_, v_start_732_);
v___x_736_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_731_, v_as_729_, v___f_734_, v___x_735_);
lean_dec(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f(lean_object* v_00_u03b1_737_, lean_object* v_as_738_, lean_object* v_p_739_){
_start:
{
lean_object* v___x_740_; lean_object* v_start_741_; lean_object* v_stop_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_741_ = lean_ctor_get(v_as_738_, 1);
v_stop_742_ = lean_ctor_get(v_as_738_, 2);
v___f_743_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_743_, 0, v_p_739_);
v___x_744_ = lean_nat_sub(v_stop_742_, v_start_741_);
v___x_745_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_740_, v_as_738_, v___f_743_, v___x_744_);
lean_dec(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray___redArg(lean_object* v_as_746_, lean_object* v_start_747_, lean_object* v_stop_748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_as_746_);
v___x_750_ = lean_nat_dec_le(v_stop_748_, v___x_749_);
if (v___x_750_ == 0)
{
uint8_t v___x_751_; 
lean_dec(v_stop_748_);
v___x_751_ = lean_nat_dec_le(v_start_747_, v___x_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v_start_747_);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v_as_746_);
lean_ctor_set(v___x_752_, 1, v___x_749_);
lean_ctor_set(v___x_752_, 2, v___x_749_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_753_, 0, v_as_746_);
lean_ctor_set(v___x_753_, 1, v_start_747_);
lean_ctor_set(v___x_753_, 2, v___x_749_);
return v___x_753_;
}
}
else
{
uint8_t v___x_754_; 
v___x_754_ = lean_nat_dec_le(v_start_747_, v_stop_748_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v_start_747_);
lean_inc(v_stop_748_);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v_as_746_);
lean_ctor_set(v___x_755_, 1, v_stop_748_);
lean_ctor_set(v___x_755_, 2, v_stop_748_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_756_, 0, v_as_746_);
lean_ctor_set(v___x_756_, 1, v_start_747_);
lean_ctor_set(v___x_756_, 2, v_stop_748_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray(lean_object* v_00_u03b1_757_, lean_object* v_as_758_, lean_object* v_start_759_, lean_object* v_stop_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Array_toSubarray___redArg(v_as_758_, v_start_759_, v_stop_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5));
v___x_879_ = l_String_toRawSubstring_x27(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(lean_object* v_x_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = ((lean_object*)(l_Array_term_____x5b___x3a___x5d___closed__2));
lean_inc(v_x_893_);
v___x_897_ = l_Lean_Syntax_isOfKind(v_x_893_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_x_893_);
v___x_898_ = lean_box(1);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_a_895_);
return v___x_899_;
}
else
{
lean_object* v_quotContext_900_; lean_object* v_currMacroScope_901_; lean_object* v_ref_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_quotContext_900_ = lean_ctor_get(v_a_894_, 1);
v_currMacroScope_901_ = lean_ctor_get(v_a_894_, 2);
v_ref_902_ = lean_ctor_get(v_a_894_, 5);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = l_Lean_Syntax_getArg(v_x_893_, v___x_903_);
v___x_905_ = lean_unsigned_to_nat(2u);
v___x_906_ = l_Lean_Syntax_getArg(v_x_893_, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(4u);
v___x_908_ = l_Lean_Syntax_getArg(v_x_893_, v___x_907_);
lean_dec(v_x_893_);
v___x_909_ = 0;
v___x_910_ = l_Lean_SourceInfo_fromRef(v_ref_902_, v___x_909_);
v___x_911_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_912_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_913_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_901_);
lean_inc(v_quotContext_900_);
v___x_914_ = l_Lean_addMacroScope(v_quotContext_900_, v___x_913_, v_currMacroScope_901_);
v___x_915_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_910_, 2);
v___x_916_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_916_, 0, v___x_910_);
lean_ctor_set(v___x_916_, 1, v___x_912_);
lean_ctor_set(v___x_916_, 2, v___x_914_);
lean_ctor_set(v___x_916_, 3, v___x_915_);
v___x_917_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_918_ = l_Lean_Syntax_node3(v___x_910_, v___x_917_, v___x_904_, v___x_906_, v___x_908_);
v___x_919_ = l_Lean_Syntax_node2(v___x_910_, v___x_911_, v___x_916_, v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v_a_895_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(lean_object* v_x_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(v_x_921_, v_a_922_, v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object* v_x_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = ((lean_object*)(l_Array_term_____x5b_x3a___x5d___closed__1));
lean_inc(v_x_929_);
v___x_933_ = l_Lean_Syntax_isOfKind(v_x_929_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v_x_929_);
v___x_934_ = lean_box(1);
v___x_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_a_931_);
return v___x_935_;
}
else
{
lean_object* v_quotContext_936_; lean_object* v_currMacroScope_937_; lean_object* v_ref_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_quotContext_936_ = lean_ctor_get(v_a_930_, 1);
v_currMacroScope_937_ = lean_ctor_get(v_a_930_, 2);
v_ref_938_ = lean_ctor_get(v_a_930_, 5);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l_Lean_Syntax_getArg(v_x_929_, v___x_939_);
v___x_941_ = lean_unsigned_to_nat(3u);
v___x_942_ = l_Lean_Syntax_getArg(v_x_929_, v___x_941_);
lean_dec(v_x_929_);
v___x_943_ = 0;
v___x_944_ = l_Lean_SourceInfo_fromRef(v_ref_938_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_946_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_947_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_937_);
lean_inc(v_quotContext_936_);
v___x_948_ = l_Lean_addMacroScope(v_quotContext_936_, v___x_947_, v_currMacroScope_937_);
v___x_949_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_944_, 4);
v___x_950_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_950_, 0, v___x_944_);
lean_ctor_set(v___x_950_, 1, v___x_946_);
lean_ctor_set(v___x_950_, 2, v___x_948_);
lean_ctor_set(v___x_950_, 3, v___x_949_);
v___x_951_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_952_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1));
v___x_953_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2));
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_944_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_Syntax_node1(v___x_944_, v___x_952_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node3(v___x_944_, v___x_951_, v___x_940_, v___x_955_, v___x_942_);
v___x_957_ = l_Lean_Syntax_node2(v___x_944_, v___x_945_, v___x_950_, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_a_931_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(lean_object* v_x_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(v_x_959_, v_a_960_, v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_962_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4(void){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Array_mkArray0(lean_box(0));
return v___x_975_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11));
v___x_996_ = l_String_toRawSubstring_x27(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18));
v___x_1009_ = l_String_toRawSubstring_x27(v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(lean_object* v_x_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_Array_term_____x5b___x3a_x5d___closed__1));
lean_inc(v_x_1014_);
v___x_1018_ = l_Lean_Syntax_isOfKind(v_x_1014_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_x_1014_);
v___x_1019_ = lean_box(1);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_1016_);
return v___x_1020_;
}
else
{
lean_object* v_quotContext_1021_; lean_object* v_currMacroScope_1022_; lean_object* v_ref_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_quotContext_1021_ = lean_ctor_get(v_a_1015_, 1);
v_currMacroScope_1022_ = lean_ctor_get(v_a_1015_, 2);
v_ref_1023_ = lean_ctor_get(v_a_1015_, 5);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = l_Lean_Syntax_getArg(v_x_1014_, v___x_1024_);
v___x_1026_ = lean_unsigned_to_nat(2u);
v___x_1027_ = l_Lean_Syntax_getArg(v_x_1014_, v___x_1026_);
lean_dec(v_x_1014_);
v___x_1028_ = 0;
v___x_1029_ = l_Lean_SourceInfo_fromRef(v_ref_1023_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0));
v___x_1031_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1));
lean_inc_n(v___x_1029_, 13);
v___x_1032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1029_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
v___x_1033_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3));
v___x_1034_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_1035_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
v___x_1036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1029_);
lean_ctor_set(v___x_1036_, 1, v___x_1034_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
lean_inc_ref_n(v___x_1036_, 2);
v___x_1037_ = l_Lean_Syntax_node1(v___x_1029_, v___x_1033_, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6));
v___x_1039_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8));
v___x_1040_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10));
v___x_1041_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
v___x_1042_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13));
lean_inc_n(v_currMacroScope_1022_, 3);
lean_inc_n(v_quotContext_1021_, 3);
v___x_1043_ = l_Lean_addMacroScope(v_quotContext_1021_, v___x_1042_, v_currMacroScope_1022_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1029_);
lean_ctor_set(v___x_1045_, 1, v___x_1041_);
lean_ctor_set(v___x_1045_, 2, v___x_1043_);
lean_ctor_set(v___x_1045_, 3, v___x_1044_);
lean_inc_ref(v___x_1045_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_1029_, v___x_1040_, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14));
v___x_1048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1029_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_node5(v___x_1029_, v___x_1039_, v___x_1046_, v___x_1036_, v___x_1036_, v___x_1048_, v___x_1025_);
v___x_1050_ = l_Lean_Syntax_node1(v___x_1029_, v___x_1038_, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15));
v___x_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1029_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_1054_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_1055_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
v___x_1056_ = l_Lean_addMacroScope(v_quotContext_1021_, v___x_1055_, v_currMacroScope_1022_);
v___x_1057_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17));
v___x_1058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1029_);
lean_ctor_set(v___x_1058_, 1, v___x_1054_);
lean_ctor_set(v___x_1058_, 2, v___x_1056_);
lean_ctor_set(v___x_1058_, 3, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
v___x_1060_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21));
v___x_1061_ = l_Lean_addMacroScope(v_quotContext_1021_, v___x_1060_, v_currMacroScope_1022_);
v___x_1062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1029_);
lean_ctor_set(v___x_1062_, 1, v___x_1059_);
lean_ctor_set(v___x_1062_, 2, v___x_1061_);
lean_ctor_set(v___x_1062_, 3, v___x_1044_);
v___x_1063_ = l_Lean_Syntax_node3(v___x_1029_, v___x_1034_, v___x_1045_, v___x_1027_, v___x_1062_);
v___x_1064_ = l_Lean_Syntax_node2(v___x_1029_, v___x_1053_, v___x_1058_, v___x_1063_);
v___x_1065_ = l_Lean_Syntax_node5(v___x_1029_, v___x_1031_, v___x_1032_, v___x_1037_, v___x_1050_, v___x_1052_, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_a_1016_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(lean_object* v_x_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(v_x_1067_, v_a_1068_, v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1070_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
