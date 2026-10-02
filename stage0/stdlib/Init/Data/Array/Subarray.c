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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Subarray_instSliceSizeSubarrayData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_instSliceSizeSubarrayData___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___closed__0 = (const lean_object*)&l_Subarray_instSliceSizeSubarrayData___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg();
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0 = (const lean_object*)&l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg();
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___boxed(lean_object*);
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
static const lean_array_object l_Subarray_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Subarray_empty___redArg___closed__0 = (const lean_object*)&l_Subarray_empty___redArg___closed__0_value;
static const lean_ctor_object l_Subarray_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Subarray_empty___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Subarray_empty___redArg___closed__1 = (const lean_object*)&l_Subarray_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Subarray_empty___redArg();
LEAN_EXPORT lean_object* l_Subarray_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Subarray_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Subarray_empty___closed__0;
LEAN_EXPORT lean_object* l_Subarray_empty(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Subarray_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___lam__0(lean_object* v_s_31_){
_start:
{
lean_object* v_start_32_; lean_object* v_stop_33_; lean_object* v___x_34_; 
v_start_32_ = lean_ctor_get(v_s_31_, 1);
v_stop_33_ = lean_ctor_get(v_s_31_, 2);
v___x_34_ = lean_nat_sub(v_stop_33_, v_start_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___lam__0___boxed(lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Subarray_instSliceSizeSubarrayData___redArg___lam__0(v_s_35_);
lean_dec_ref(v_s_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg(){
_start:
{
lean_object* v___f_39_; 
v___f_39_ = ((lean_object*)(l_Subarray_instSliceSizeSubarrayData___redArg___closed__0));
return v___f_39_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Subarray_instSliceSizeSubarrayData___redArg();
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData(lean_object* v_00_u03b1_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = ((lean_object*)(l_Subarray_instSliceSizeSubarrayData___redArg___closed__0));
return v___f_43_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___redArg(lean_object* v_s_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_array_46_; lean_object* v_start_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_array_46_ = lean_ctor_get(v_s_44_, 0);
v_start_47_ = lean_ctor_get(v_s_44_, 1);
v___x_48_ = lean_nat_add(v_start_47_, v_i_45_);
v___x_49_ = lean_array_fget_borrowed(v_array_46_, v___x_48_);
lean_dec(v___x_48_);
lean_inc(v___x_49_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___redArg___boxed(lean_object* v_s_50_, lean_object* v_i_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Subarray_get___redArg(v_s_50_, v_i_51_);
lean_dec(v_i_51_);
lean_dec_ref(v_s_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get(lean_object* v_00_u03b1_53_, lean_object* v_s_54_, lean_object* v_i_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Subarray_get___redArg(v_s_54_, v_i_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___boxed(lean_object* v_00_u03b1_57_, lean_object* v_s_58_, lean_object* v_i_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Subarray_get(v_00_u03b1_57_, v_s_58_, v_i_59_);
lean_dec(v_i_59_);
lean_dec_ref(v_s_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0(lean_object* v_xs_61_, lean_object* v_i_62_, lean_object* v_h_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Subarray_get___redArg(v_xs_61_, v_i_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0___boxed(lean_object* v_xs_65_, lean_object* v_i_66_, lean_object* v_h_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0(v_xs_65_, v_i_66_, v_h_67_);
lean_dec(v_i_66_);
lean_dec_ref(v_xs_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg(){
_start:
{
lean_object* v___f_71_; 
v___f_71_ = ((lean_object*)(l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0));
return v___f_71_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___boxed(lean_object* v___dummy_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Subarray_instGetElemNatLtSizeSubarrayData___redArg();
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData(lean_object* v_00_u03b1_74_){
_start:
{
lean_object* v___f_75_; 
v___f_75_ = ((lean_object*)(l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0));
return v___f_75_;
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___redArg(lean_object* v_s_76_, lean_object* v_i_77_, lean_object* v_v_u2080_78_){
_start:
{
lean_object* v_start_79_; lean_object* v_stop_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_start_79_ = lean_ctor_get(v_s_76_, 1);
v_stop_80_ = lean_ctor_get(v_s_76_, 2);
v___x_81_ = lean_nat_sub(v_stop_80_, v_start_79_);
v___x_82_ = lean_nat_dec_lt(v_i_77_, v___x_81_);
lean_dec(v___x_81_);
if (v___x_82_ == 0)
{
lean_inc(v_v_u2080_78_);
return v_v_u2080_78_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = l_Subarray_get___redArg(v_s_76_, v_i_77_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___redArg___boxed(lean_object* v_s_84_, lean_object* v_i_85_, lean_object* v_v_u2080_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Subarray_getD___redArg(v_s_84_, v_i_85_, v_v_u2080_86_);
lean_dec(v_v_u2080_86_);
lean_dec(v_i_85_);
lean_dec_ref(v_s_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Subarray_getD(lean_object* v_00_u03b1_88_, lean_object* v_s_89_, lean_object* v_i_90_, lean_object* v_v_u2080_91_){
_start:
{
lean_object* v_start_92_; lean_object* v_stop_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_start_92_ = lean_ctor_get(v_s_89_, 1);
v_stop_93_ = lean_ctor_get(v_s_89_, 2);
v___x_94_ = lean_nat_sub(v_stop_93_, v_start_92_);
v___x_95_ = lean_nat_dec_lt(v_i_90_, v___x_94_);
lean_dec(v___x_94_);
if (v___x_95_ == 0)
{
lean_inc(v_v_u2080_91_);
return v_v_u2080_91_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = l_Subarray_get___redArg(v_s_89_, v_i_90_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___boxed(lean_object* v_00_u03b1_97_, lean_object* v_s_98_, lean_object* v_i_99_, lean_object* v_v_u2080_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Subarray_getD(v_00_u03b1_97_, v_s_98_, v_i_99_, v_v_u2080_100_);
lean_dec(v_v_u2080_100_);
lean_dec(v_i_99_);
lean_dec_ref(v_s_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg(lean_object* v_inst_102_, lean_object* v_s_103_, lean_object* v_i_104_){
_start:
{
lean_object* v_start_105_; lean_object* v_stop_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_start_105_ = lean_ctor_get(v_s_103_, 1);
v_stop_106_ = lean_ctor_get(v_s_103_, 2);
v___x_107_ = lean_nat_sub(v_stop_106_, v_start_105_);
v___x_108_ = lean_nat_dec_lt(v_i_104_, v___x_107_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
lean_inc(v_inst_102_);
return v_inst_102_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = l_Subarray_get___redArg(v_s_103_, v_i_104_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg___boxed(lean_object* v_inst_110_, lean_object* v_s_111_, lean_object* v_i_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Subarray_get_x21___redArg(v_inst_110_, v_s_111_, v_i_112_);
lean_dec(v_i_112_);
lean_dec_ref(v_s_111_);
lean_dec(v_inst_110_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21(lean_object* v_00_u03b1_114_, lean_object* v_inst_115_, lean_object* v_s_116_, lean_object* v_i_117_){
_start:
{
lean_object* v_start_118_; lean_object* v_stop_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_start_118_ = lean_ctor_get(v_s_116_, 1);
v_stop_119_ = lean_ctor_get(v_s_116_, 2);
v___x_120_ = lean_nat_sub(v_stop_119_, v_start_118_);
v___x_121_ = lean_nat_dec_lt(v_i_117_, v___x_120_);
lean_dec(v___x_120_);
if (v___x_121_ == 0)
{
lean_inc(v_inst_115_);
return v_inst_115_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = l_Subarray_get___redArg(v_s_116_, v_i_117_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___boxed(lean_object* v_00_u03b1_123_, lean_object* v_inst_124_, lean_object* v_s_125_, lean_object* v_i_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Subarray_get_x21(v_00_u03b1_123_, v_inst_124_, v_s_125_, v_i_126_);
lean_dec(v_i_126_);
lean_dec_ref(v_s_125_);
lean_dec(v_inst_124_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Subarray_popFront___redArg(lean_object* v_s_128_){
_start:
{
lean_object* v_array_129_; lean_object* v_start_130_; lean_object* v_stop_131_; uint8_t v___x_132_; 
v_array_129_ = lean_ctor_get(v_s_128_, 0);
v_start_130_ = lean_ctor_get(v_s_128_, 1);
v_stop_131_ = lean_ctor_get(v_s_128_, 2);
v___x_132_ = lean_nat_dec_lt(v_start_130_, v_stop_131_);
if (v___x_132_ == 0)
{
return v_s_128_;
}
else
{
lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_141_; 
lean_inc(v_stop_131_);
lean_inc(v_start_130_);
lean_inc_ref(v_array_129_);
v_isSharedCheck_141_ = !lean_is_exclusive(v_s_128_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; lean_object* v_unused_143_; lean_object* v_unused_144_; 
v_unused_142_ = lean_ctor_get(v_s_128_, 2);
lean_dec(v_unused_142_);
v_unused_143_ = lean_ctor_get(v_s_128_, 1);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_s_128_, 0);
lean_dec(v_unused_144_);
v___x_134_ = v_s_128_;
v_isShared_135_ = v_isSharedCheck_141_;
goto v_resetjp_133_;
}
else
{
lean_dec(v_s_128_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_141_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_start_130_, v___x_136_);
lean_dec(v_start_130_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_137_);
v___x_139_ = v___x_134_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_array_129_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_stop_131_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_popFront(lean_object* v_00_u03b1_145_, lean_object* v_s_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Subarray_popFront___redArg(v_s_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Subarray_empty___redArg(){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = ((lean_object*)(l_Subarray_empty___redArg___closed__1));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Subarray_empty___redArg___boxed(lean_object* v___dummy_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Subarray_empty___redArg();
return v_res_156_;
}
}
static lean_object* _init_l_Subarray_empty___closed__0(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Subarray_empty___redArg();
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Subarray_empty(lean_object* v_00_u03b1_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection___redArg___boxed(lean_object* v___dummy_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Subarray_instEmptyCollection___redArg();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection(lean_object* v_00_u03b1_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instInhabited___redArg(){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instInhabited___redArg___boxed(lean_object* v___dummy_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Subarray_instInhabited___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instInhabited(lean_object* v_00_u03b1_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM___redArg(lean_object* v_inst_172_, lean_object* v_f_173_, lean_object* v_init_174_, lean_object* v_as_175_){
_start:
{
lean_object* v_toApplicative_176_; lean_object* v_array_177_; lean_object* v_start_178_; lean_object* v_stop_179_; lean_object* v_toPure_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_toApplicative_176_ = lean_ctor_get(v_inst_172_, 0);
v_array_177_ = lean_ctor_get(v_as_175_, 0);
lean_inc_ref(v_array_177_);
v_start_178_ = lean_ctor_get(v_as_175_, 1);
lean_inc(v_start_178_);
v_stop_179_ = lean_ctor_get(v_as_175_, 2);
lean_inc(v_stop_179_);
lean_dec_ref(v_as_175_);
v_toPure_180_ = lean_ctor_get(v_toApplicative_176_, 1);
v___x_181_ = lean_array_get_size(v_array_177_);
v___x_182_ = lean_nat_dec_le(v_stop_179_, v___x_181_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; 
lean_dec(v_stop_179_);
v___x_183_ = lean_nat_dec_lt(v_start_178_, v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_inc(v_toPure_180_);
lean_dec(v_start_178_);
lean_dec_ref(v_array_177_);
lean_dec(v_f_173_);
lean_dec_ref(v_inst_172_);
v___x_184_ = lean_apply_2(v_toPure_180_, lean_box(0), v_init_174_);
return v___x_184_;
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_usize_of_nat(v___x_181_);
v___x_186_ = lean_usize_of_nat(v_start_178_);
lean_dec(v_start_178_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_172_, v_f_173_, v_array_177_, v___x_185_, v___x_186_, v_init_174_);
return v___x_187_;
}
}
else
{
uint8_t v___x_188_; 
v___x_188_ = lean_nat_dec_lt(v_start_178_, v_stop_179_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
lean_inc(v_toPure_180_);
lean_dec(v_stop_179_);
lean_dec(v_start_178_);
lean_dec_ref(v_array_177_);
lean_dec(v_f_173_);
lean_dec_ref(v_inst_172_);
v___x_189_ = lean_apply_2(v_toPure_180_, lean_box(0), v_init_174_);
return v___x_189_;
}
else
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_usize_of_nat(v_stop_179_);
lean_dec(v_stop_179_);
v___x_191_ = lean_usize_of_nat(v_start_178_);
lean_dec(v_start_178_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_172_, v_f_173_, v_array_177_, v___x_190_, v___x_191_, v_init_174_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_f_197_, lean_object* v_init_198_, lean_object* v_as_199_){
_start:
{
lean_object* v_toApplicative_200_; lean_object* v_array_201_; lean_object* v_start_202_; lean_object* v_stop_203_; lean_object* v_toPure_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_toApplicative_200_ = lean_ctor_get(v_inst_196_, 0);
v_array_201_ = lean_ctor_get(v_as_199_, 0);
lean_inc_ref(v_array_201_);
v_start_202_ = lean_ctor_get(v_as_199_, 1);
lean_inc(v_start_202_);
v_stop_203_ = lean_ctor_get(v_as_199_, 2);
lean_inc(v_stop_203_);
lean_dec_ref(v_as_199_);
v_toPure_204_ = lean_ctor_get(v_toApplicative_200_, 1);
v___x_205_ = lean_array_get_size(v_array_201_);
v___x_206_ = lean_nat_dec_le(v_stop_203_, v___x_205_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
lean_dec(v_stop_203_);
v___x_207_ = lean_nat_dec_lt(v_start_202_, v___x_205_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_inc(v_toPure_204_);
lean_dec(v_start_202_);
lean_dec_ref(v_array_201_);
lean_dec(v_f_197_);
lean_dec_ref(v_inst_196_);
v___x_208_ = lean_apply_2(v_toPure_204_, lean_box(0), v_init_198_);
return v___x_208_;
}
else
{
size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_usize_of_nat(v___x_205_);
v___x_210_ = lean_usize_of_nat(v_start_202_);
lean_dec(v_start_202_);
v___x_211_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_196_, v_f_197_, v_array_201_, v___x_209_, v___x_210_, v_init_198_);
return v___x_211_;
}
}
else
{
uint8_t v___x_212_; 
v___x_212_ = lean_nat_dec_lt(v_start_202_, v_stop_203_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_inc(v_toPure_204_);
lean_dec(v_stop_203_);
lean_dec(v_start_202_);
lean_dec_ref(v_array_201_);
lean_dec(v_f_197_);
lean_dec_ref(v_inst_196_);
v___x_213_ = lean_apply_2(v_toPure_204_, lean_box(0), v_init_198_);
return v___x_213_;
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_usize_of_nat(v_stop_203_);
lean_dec(v_stop_203_);
v___x_215_ = lean_usize_of_nat(v_start_202_);
lean_dec(v_start_202_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_196_, v_f_197_, v_array_201_, v___x_214_, v___x_215_, v_init_198_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM___redArg(lean_object* v_inst_217_, lean_object* v_p_218_, lean_object* v_as_219_){
_start:
{
lean_object* v_toApplicative_220_; lean_object* v_array_221_; lean_object* v_start_222_; lean_object* v_stop_223_; lean_object* v_toPure_224_; lean_object* v___y_226_; uint8_t v___x_233_; 
v_toApplicative_220_ = lean_ctor_get(v_inst_217_, 0);
v_array_221_ = lean_ctor_get(v_as_219_, 0);
lean_inc_ref(v_array_221_);
v_start_222_ = lean_ctor_get(v_as_219_, 1);
lean_inc(v_start_222_);
v_stop_223_ = lean_ctor_get(v_as_219_, 2);
lean_inc(v_stop_223_);
lean_dec_ref(v_as_219_);
v_toPure_224_ = lean_ctor_get(v_toApplicative_220_, 1);
v___x_233_ = lean_nat_dec_lt(v_start_222_, v_stop_223_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_inc(v_toPure_224_);
lean_dec(v_stop_223_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
lean_dec(v_p_218_);
lean_dec_ref(v_inst_217_);
v___x_234_ = lean_box(v___x_233_);
v___x_235_ = lean_apply_2(v_toPure_224_, lean_box(0), v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_array_get_size(v_array_221_);
v___x_237_ = lean_nat_dec_le(v_stop_223_, v___x_236_);
if (v___x_237_ == 0)
{
lean_dec(v_stop_223_);
v___y_226_ = v___x_236_;
goto v___jp_225_;
}
else
{
v___y_226_ = v_stop_223_;
goto v___jp_225_;
}
}
v___jp_225_:
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_lt(v_start_222_, v___y_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_inc(v_toPure_224_);
lean_dec(v___y_226_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
lean_dec(v_p_218_);
lean_dec_ref(v_inst_217_);
v___x_228_ = lean_box(v___x_227_);
v___x_229_ = lean_apply_2(v_toPure_224_, lean_box(0), v___x_228_);
return v___x_229_;
}
else
{
size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_usize_of_nat(v_start_222_);
lean_dec(v_start_222_);
v___x_231_ = lean_usize_of_nat(v___y_226_);
lean_dec(v___y_226_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_217_, v_p_218_, v_array_221_, v___x_230_, v___x_231_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM(lean_object* v_00_u03b1_238_, lean_object* v_m_239_, lean_object* v_inst_240_, lean_object* v_p_241_, lean_object* v_as_242_){
_start:
{
lean_object* v_toApplicative_243_; lean_object* v_array_244_; lean_object* v_start_245_; lean_object* v_stop_246_; lean_object* v_toPure_247_; lean_object* v___y_249_; uint8_t v___x_256_; 
v_toApplicative_243_ = lean_ctor_get(v_inst_240_, 0);
v_array_244_ = lean_ctor_get(v_as_242_, 0);
lean_inc_ref(v_array_244_);
v_start_245_ = lean_ctor_get(v_as_242_, 1);
lean_inc(v_start_245_);
v_stop_246_ = lean_ctor_get(v_as_242_, 2);
lean_inc(v_stop_246_);
lean_dec_ref(v_as_242_);
v_toPure_247_ = lean_ctor_get(v_toApplicative_243_, 1);
v___x_256_ = lean_nat_dec_lt(v_start_245_, v_stop_246_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_inc(v_toPure_247_);
lean_dec(v_stop_246_);
lean_dec(v_start_245_);
lean_dec_ref(v_array_244_);
lean_dec(v_p_241_);
lean_dec_ref(v_inst_240_);
v___x_257_ = lean_box(v___x_256_);
v___x_258_ = lean_apply_2(v_toPure_247_, lean_box(0), v___x_257_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_array_244_);
v___x_260_ = lean_nat_dec_le(v_stop_246_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v_stop_246_);
v___y_249_ = v___x_259_;
goto v___jp_248_;
}
else
{
v___y_249_ = v_stop_246_;
goto v___jp_248_;
}
}
v___jp_248_:
{
uint8_t v___x_250_; 
v___x_250_ = lean_nat_dec_lt(v_start_245_, v___y_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_inc(v_toPure_247_);
lean_dec(v___y_249_);
lean_dec(v_start_245_);
lean_dec_ref(v_array_244_);
lean_dec(v_p_241_);
lean_dec_ref(v_inst_240_);
v___x_251_ = lean_box(v___x_250_);
v___x_252_ = lean_apply_2(v_toPure_247_, lean_box(0), v___x_251_);
return v___x_252_;
}
else
{
size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_usize_of_nat(v_start_245_);
lean_dec(v_start_245_);
v___x_254_ = lean_usize_of_nat(v___y_249_);
lean_dec(v___y_249_);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_240_, v_p_241_, v_array_244_, v___x_253_, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0(lean_object* v_toPure_261_, uint8_t v_____do__lift_262_){
_start:
{
if (v_____do__lift_262_ == 0)
{
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = 1;
v___x_264_ = lean_box(v___x_263_);
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
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0___boxed(lean_object* v_toPure_269_, lean_object* v_____do__lift_270_){
_start:
{
uint8_t v_____do__lift_110__boxed_271_; lean_object* v_res_272_; 
v_____do__lift_110__boxed_271_ = lean_unbox(v_____do__lift_270_);
v_res_272_ = l_Subarray_allM___redArg___lam__0(v_toPure_269_, v_____do__lift_110__boxed_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1(lean_object* v_toPure_273_, uint8_t v___x_274_, uint8_t v_____do__lift_275_){
_start:
{
if (v_____do__lift_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(v___x_274_);
v___x_277_ = lean_apply_2(v_toPure_273_, lean_box(0), v___x_276_);
return v___x_277_;
}
else
{
uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = 0;
v___x_279_ = lean_box(v___x_278_);
v___x_280_ = lean_apply_2(v_toPure_273_, lean_box(0), v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1___boxed(lean_object* v_toPure_281_, lean_object* v___x_282_, lean_object* v_____do__lift_283_){
_start:
{
uint8_t v___x_125__boxed_284_; uint8_t v_____do__lift_126__boxed_285_; lean_object* v_res_286_; 
v___x_125__boxed_284_ = lean_unbox(v___x_282_);
v_____do__lift_126__boxed_285_ = lean_unbox(v_____do__lift_283_);
v_res_286_ = l_Subarray_allM___redArg___lam__1(v_toPure_281_, v___x_125__boxed_284_, v_____do__lift_126__boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__2(lean_object* v_p_287_, lean_object* v_toBind_288_, lean_object* v___f_289_, lean_object* v_v_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_apply_1(v_p_287_, v_v_290_);
v___x_292_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_291_, v___f_289_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg(lean_object* v_inst_293_, lean_object* v_p_294_, lean_object* v_as_295_){
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
lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v___y_311_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_307_ = lean_box(v___x_303_);
lean_inc(v_toPure_301_);
v___f_308_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_308_, 0, v_toPure_301_);
lean_closure_set(v___f_308_, 1, v___x_307_);
lean_inc(v_toBind_300_);
v___f_309_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_309_, 0, v_p_294_);
lean_closure_set(v___f_309_, 1, v_toBind_300_);
lean_closure_set(v___f_309_, 2, v___f_308_);
v___x_320_ = lean_array_get_size(v_array_297_);
v___x_321_ = lean_nat_dec_le(v_stop_299_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec(v_stop_299_);
v___y_311_ = v___x_320_;
goto v___jp_310_;
}
else
{
v___y_311_ = v_stop_299_;
goto v___jp_310_;
}
v___jp_310_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_nat_dec_lt(v_start_298_, v___y_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc(v_toPure_301_);
lean_dec(v___y_311_);
lean_dec_ref(v___f_309_);
lean_dec(v_start_298_);
lean_dec_ref(v_array_297_);
lean_dec_ref(v_inst_293_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_apply_2(v_toPure_301_, lean_box(0), v___x_313_);
v___x_315_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_314_, v___f_302_);
return v___x_315_;
}
else
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_usize_of_nat(v_start_298_);
lean_dec(v_start_298_);
v___x_317_ = lean_usize_of_nat(v___y_311_);
lean_dec(v___y_311_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_293_, v___f_309_, v_array_297_, v___x_316_, v___x_317_);
v___x_319_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_318_, v___f_302_);
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM(lean_object* v_00_u03b1_322_, lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_p_325_, lean_object* v_as_326_){
_start:
{
lean_object* v_toApplicative_327_; lean_object* v_array_328_; lean_object* v_start_329_; lean_object* v_stop_330_; lean_object* v_toBind_331_; lean_object* v_toPure_332_; lean_object* v___f_333_; uint8_t v___x_334_; 
v_toApplicative_327_ = lean_ctor_get(v_inst_324_, 0);
v_array_328_ = lean_ctor_get(v_as_326_, 0);
lean_inc_ref(v_array_328_);
v_start_329_ = lean_ctor_get(v_as_326_, 1);
lean_inc(v_start_329_);
v_stop_330_ = lean_ctor_get(v_as_326_, 2);
lean_inc(v_stop_330_);
lean_dec_ref(v_as_326_);
v_toBind_331_ = lean_ctor_get(v_inst_324_, 1);
lean_inc(v_toBind_331_);
v_toPure_332_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_toPure_332_);
v___f_333_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_333_, 0, v_toPure_332_);
v___x_334_ = lean_nat_dec_lt(v_start_329_, v_stop_330_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_inc(v_toPure_332_);
lean_dec(v_stop_330_);
lean_dec(v_start_329_);
lean_dec_ref(v_array_328_);
lean_dec(v_p_325_);
lean_dec_ref(v_inst_324_);
v___x_335_ = lean_box(v___x_334_);
v___x_336_ = lean_apply_2(v_toPure_332_, lean_box(0), v___x_335_);
v___x_337_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_336_, v___f_333_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___y_342_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_338_ = lean_box(v___x_334_);
lean_inc(v_toPure_332_);
v___f_339_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_339_, 0, v_toPure_332_);
lean_closure_set(v___f_339_, 1, v___x_338_);
lean_inc(v_toBind_331_);
v___f_340_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_340_, 0, v_p_325_);
lean_closure_set(v___f_340_, 1, v_toBind_331_);
lean_closure_set(v___f_340_, 2, v___f_339_);
v___x_351_ = lean_array_get_size(v_array_328_);
v___x_352_ = lean_nat_dec_le(v_stop_330_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_stop_330_);
v___y_342_ = v___x_351_;
goto v___jp_341_;
}
else
{
v___y_342_ = v_stop_330_;
goto v___jp_341_;
}
v___jp_341_:
{
uint8_t v___x_343_; 
v___x_343_ = lean_nat_dec_lt(v_start_329_, v___y_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc(v_toPure_332_);
lean_dec(v___y_342_);
lean_dec_ref(v___f_340_);
lean_dec(v_start_329_);
lean_dec_ref(v_array_328_);
lean_dec_ref(v_inst_324_);
v___x_344_ = lean_box(v___x_343_);
v___x_345_ = lean_apply_2(v_toPure_332_, lean_box(0), v___x_344_);
v___x_346_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_345_, v___f_333_);
return v___x_346_;
}
else
{
size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_usize_of_nat(v_start_329_);
lean_dec(v_start_329_);
v___x_348_ = lean_usize_of_nat(v___y_342_);
lean_dec(v___y_342_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_324_, v___f_340_, v_array_328_, v___x_347_, v___x_348_);
v___x_350_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_349_, v___f_333_);
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg___lam__0(lean_object* v_f_353_, lean_object* v_x_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_apply_1(v_f_353_, v___y_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg(lean_object* v_inst_357_, lean_object* v_f_358_, lean_object* v_as_359_){
_start:
{
lean_object* v_toApplicative_360_; lean_object* v_array_361_; lean_object* v_start_362_; lean_object* v_stop_363_; lean_object* v_toPure_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_toApplicative_360_ = lean_ctor_get(v_inst_357_, 0);
v_array_361_ = lean_ctor_get(v_as_359_, 0);
lean_inc_ref(v_array_361_);
v_start_362_ = lean_ctor_get(v_as_359_, 1);
lean_inc(v_start_362_);
v_stop_363_ = lean_ctor_get(v_as_359_, 2);
lean_inc(v_stop_363_);
lean_dec_ref(v_as_359_);
v_toPure_364_ = lean_ctor_get(v_toApplicative_360_, 1);
v___x_365_ = lean_box(0);
v___x_366_ = lean_nat_dec_lt(v_start_362_, v_stop_363_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_inc(v_toPure_364_);
lean_dec(v_stop_363_);
lean_dec(v_start_362_);
lean_dec_ref(v_array_361_);
lean_dec(v_f_358_);
lean_dec_ref(v_inst_357_);
v___x_367_ = lean_apply_2(v_toPure_364_, lean_box(0), v___x_365_);
return v___x_367_;
}
else
{
lean_object* v___f_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___f_368_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_368_, 0, v_f_358_);
v___x_369_ = lean_array_get_size(v_array_361_);
v___x_370_ = lean_nat_dec_le(v_stop_363_, v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
lean_dec(v_stop_363_);
v___x_371_ = lean_nat_dec_lt(v_start_362_, v___x_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_inc(v_toPure_364_);
lean_dec_ref(v___f_368_);
lean_dec(v_start_362_);
lean_dec_ref(v_array_361_);
lean_dec_ref(v_inst_357_);
v___x_372_ = lean_apply_2(v_toPure_364_, lean_box(0), v___x_365_);
return v___x_372_;
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_usize_of_nat(v_start_362_);
lean_dec(v_start_362_);
v___x_374_ = lean_usize_of_nat(v___x_369_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_357_, v___f_368_, v_array_361_, v___x_373_, v___x_374_, v___x_365_);
return v___x_375_;
}
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_usize_of_nat(v_start_362_);
lean_dec(v_start_362_);
v___x_377_ = lean_usize_of_nat(v_stop_363_);
lean_dec(v_stop_363_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_357_, v___f_368_, v_array_361_, v___x_376_, v___x_377_, v___x_365_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM(lean_object* v_00_u03b1_379_, lean_object* v_m_380_, lean_object* v_inst_381_, lean_object* v_f_382_, lean_object* v_as_383_){
_start:
{
lean_object* v_toApplicative_384_; lean_object* v_array_385_; lean_object* v_start_386_; lean_object* v_stop_387_; lean_object* v_toPure_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_toApplicative_384_ = lean_ctor_get(v_inst_381_, 0);
v_array_385_ = lean_ctor_get(v_as_383_, 0);
lean_inc_ref(v_array_385_);
v_start_386_ = lean_ctor_get(v_as_383_, 1);
lean_inc(v_start_386_);
v_stop_387_ = lean_ctor_get(v_as_383_, 2);
lean_inc(v_stop_387_);
lean_dec_ref(v_as_383_);
v_toPure_388_ = lean_ctor_get(v_toApplicative_384_, 1);
v___x_389_ = lean_box(0);
v___x_390_ = lean_nat_dec_lt(v_start_386_, v_stop_387_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_inc(v_toPure_388_);
lean_dec(v_stop_387_);
lean_dec(v_start_386_);
lean_dec_ref(v_array_385_);
lean_dec(v_f_382_);
lean_dec_ref(v_inst_381_);
v___x_391_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_389_);
return v___x_391_;
}
else
{
lean_object* v___f_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___f_392_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_392_, 0, v_f_382_);
v___x_393_ = lean_array_get_size(v_array_385_);
v___x_394_ = lean_nat_dec_le(v_stop_387_, v___x_393_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; 
lean_dec(v_stop_387_);
v___x_395_ = lean_nat_dec_lt(v_start_386_, v___x_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_inc(v_toPure_388_);
lean_dec_ref(v___f_392_);
lean_dec(v_start_386_);
lean_dec_ref(v_array_385_);
lean_dec_ref(v_inst_381_);
v___x_396_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_389_);
return v___x_396_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_usize_of_nat(v_start_386_);
lean_dec(v_start_386_);
v___x_398_ = lean_usize_of_nat(v___x_393_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_381_, v___f_392_, v_array_385_, v___x_397_, v___x_398_, v___x_389_);
return v___x_399_;
}
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_usize_of_nat(v_start_386_);
lean_dec(v_start_386_);
v___x_401_ = lean_usize_of_nat(v_stop_387_);
lean_dec(v_stop_387_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_381_, v___f_392_, v_array_385_, v___x_400_, v___x_401_, v___x_389_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg___lam__0(lean_object* v_f_403_, lean_object* v_a_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_apply_1(v_f_403_, v_a_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg(lean_object* v_inst_407_, lean_object* v_f_408_, lean_object* v_as_409_){
_start:
{
lean_object* v_toApplicative_410_; lean_object* v_array_411_; lean_object* v_start_412_; lean_object* v_stop_413_; lean_object* v_toPure_414_; lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_toApplicative_410_ = lean_ctor_get(v_inst_407_, 0);
v_array_411_ = lean_ctor_get(v_as_409_, 0);
lean_inc_ref(v_array_411_);
v_start_412_ = lean_ctor_get(v_as_409_, 1);
lean_inc(v_start_412_);
v_stop_413_ = lean_ctor_get(v_as_409_, 2);
lean_inc(v_stop_413_);
lean_dec_ref(v_as_409_);
v_toPure_414_ = lean_ctor_get(v_toApplicative_410_, 1);
v___f_415_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_415_, 0, v_f_408_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_array_get_size(v_array_411_);
v___x_418_ = lean_nat_dec_le(v_stop_413_, v___x_417_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; 
lean_dec(v_stop_413_);
v___x_419_ = lean_nat_dec_lt(v_start_412_, v___x_417_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_inc(v_toPure_414_);
lean_dec_ref(v___f_415_);
lean_dec(v_start_412_);
lean_dec_ref(v_array_411_);
lean_dec_ref(v_inst_407_);
v___x_420_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_416_);
return v___x_420_;
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_usize_of_nat(v___x_417_);
v___x_422_ = lean_usize_of_nat(v_start_412_);
lean_dec(v_start_412_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_407_, v___f_415_, v_array_411_, v___x_421_, v___x_422_, v___x_416_);
return v___x_423_;
}
}
else
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_lt(v_start_412_, v_stop_413_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_inc(v_toPure_414_);
lean_dec_ref(v___f_415_);
lean_dec(v_stop_413_);
lean_dec(v_start_412_);
lean_dec_ref(v_array_411_);
lean_dec_ref(v_inst_407_);
v___x_425_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_416_);
return v___x_425_;
}
else
{
size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_usize_of_nat(v_stop_413_);
lean_dec(v_stop_413_);
v___x_427_ = lean_usize_of_nat(v_start_412_);
lean_dec(v_start_412_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_407_, v___f_415_, v_array_411_, v___x_426_, v___x_427_, v___x_416_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM(lean_object* v_00_u03b1_429_, lean_object* v_m_430_, lean_object* v_inst_431_, lean_object* v_f_432_, lean_object* v_as_433_){
_start:
{
lean_object* v_toApplicative_434_; lean_object* v_array_435_; lean_object* v_start_436_; lean_object* v_stop_437_; lean_object* v_toPure_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_toApplicative_434_ = lean_ctor_get(v_inst_431_, 0);
v_array_435_ = lean_ctor_get(v_as_433_, 0);
lean_inc_ref(v_array_435_);
v_start_436_ = lean_ctor_get(v_as_433_, 1);
lean_inc(v_start_436_);
v_stop_437_ = lean_ctor_get(v_as_433_, 2);
lean_inc(v_stop_437_);
lean_dec_ref(v_as_433_);
v_toPure_438_ = lean_ctor_get(v_toApplicative_434_, 1);
v___f_439_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_439_, 0, v_f_432_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_array_get_size(v_array_435_);
v___x_442_ = lean_nat_dec_le(v_stop_437_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; 
lean_dec(v_stop_437_);
v___x_443_ = lean_nat_dec_lt(v_start_436_, v___x_441_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_inc(v_toPure_438_);
lean_dec_ref(v___f_439_);
lean_dec(v_start_436_);
lean_dec_ref(v_array_435_);
lean_dec_ref(v_inst_431_);
v___x_444_ = lean_apply_2(v_toPure_438_, lean_box(0), v___x_440_);
return v___x_444_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_usize_of_nat(v___x_441_);
v___x_446_ = lean_usize_of_nat(v_start_436_);
lean_dec(v_start_436_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_431_, v___f_439_, v_array_435_, v___x_445_, v___x_446_, v___x_440_);
return v___x_447_;
}
}
else
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_lt(v_start_436_, v_stop_437_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_inc(v_toPure_438_);
lean_dec_ref(v___f_439_);
lean_dec(v_stop_437_);
lean_dec(v_start_436_);
lean_dec_ref(v_array_435_);
lean_dec_ref(v_inst_431_);
v___x_449_ = lean_apply_2(v_toPure_438_, lean_box(0), v___x_440_);
return v___x_449_;
}
else
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_usize_of_nat(v_stop_437_);
lean_dec(v_stop_437_);
v___x_451_ = lean_usize_of_nat(v_start_436_);
lean_dec(v_start_436_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_431_, v___f_439_, v_array_435_, v___x_450_, v___x_451_, v___x_440_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg___lam__0(lean_object* v_f_453_, lean_object* v_x1_454_, lean_object* v_x2_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_apply_2(v_f_453_, v_x1_454_, v_x2_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg(lean_object* v_f_476_, lean_object* v_init_477_, lean_object* v_as_478_){
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
LEAN_EXPORT lean_object* l_Subarray_foldr(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_f_496_, lean_object* v_init_497_, lean_object* v_as_498_){
_start:
{
lean_object* v___x_499_; lean_object* v_array_500_; lean_object* v_start_501_; lean_object* v_stop_502_; lean_object* v___f_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_499_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_500_ = lean_ctor_get(v_as_498_, 0);
lean_inc_ref(v_array_500_);
v_start_501_ = lean_ctor_get(v_as_498_, 1);
lean_inc(v_start_501_);
v_stop_502_ = lean_ctor_get(v_as_498_, 2);
lean_inc(v_stop_502_);
lean_dec_ref(v_as_498_);
v___f_503_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_503_, 0, v_f_496_);
v___x_504_ = lean_array_get_size(v_array_500_);
v___x_505_ = lean_nat_dec_le(v_stop_502_, v___x_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
lean_dec(v_stop_502_);
v___x_506_ = lean_nat_dec_lt(v_start_501_, v___x_504_);
if (v___x_506_ == 0)
{
lean_dec_ref(v___f_503_);
lean_dec(v_start_501_);
lean_dec_ref(v_array_500_);
return v_init_497_;
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_usize_of_nat(v___x_504_);
v___x_508_ = lean_usize_of_nat(v_start_501_);
lean_dec(v_start_501_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_499_, v___f_503_, v_array_500_, v___x_507_, v___x_508_, v_init_497_);
return v___x_509_;
}
}
else
{
uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_lt(v_start_501_, v_stop_502_);
if (v___x_510_ == 0)
{
lean_dec_ref(v___f_503_);
lean_dec(v_stop_502_);
lean_dec(v_start_501_);
lean_dec_ref(v_array_500_);
return v_init_497_;
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_usize_of_nat(v_stop_502_);
lean_dec(v_stop_502_);
v___x_512_ = lean_usize_of_nat(v_start_501_);
lean_dec(v_start_501_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_499_, v___f_503_, v_array_500_, v___x_511_, v___x_512_, v_init_497_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg___lam__0(lean_object* v_p_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_apply_1(v_p_514_, v_x_515_);
v___x_517_ = lean_unbox(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___lam__0___boxed(lean_object* v_p_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Subarray_any___redArg___lam__0(v_p_518_, v_x_519_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any___redArg(lean_object* v_p_522_, lean_object* v_as_523_){
_start:
{
lean_object* v___x_524_; lean_object* v_array_525_; lean_object* v_start_526_; lean_object* v_stop_527_; uint8_t v___x_528_; 
v___x_524_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_525_ = lean_ctor_get(v_as_523_, 0);
lean_inc_ref(v_array_525_);
v_start_526_ = lean_ctor_get(v_as_523_, 1);
lean_inc(v_start_526_);
v_stop_527_ = lean_ctor_get(v_as_523_, 2);
lean_inc(v_stop_527_);
lean_dec_ref(v_as_523_);
v___x_528_ = lean_nat_dec_lt(v_start_526_, v_stop_527_);
if (v___x_528_ == 0)
{
lean_dec(v_stop_527_);
lean_dec(v_start_526_);
lean_dec_ref(v_array_525_);
lean_dec_ref(v_p_522_);
return v___x_528_;
}
else
{
lean_object* v___f_529_; lean_object* v___y_531_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___f_529_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_529_, 0, v_p_522_);
v___x_537_ = lean_array_get_size(v_array_525_);
v___x_538_ = lean_nat_dec_le(v_stop_527_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v_stop_527_);
v___y_531_ = v___x_537_;
goto v___jp_530_;
}
else
{
v___y_531_ = v_stop_527_;
goto v___jp_530_;
}
v___jp_530_:
{
uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_lt(v_start_526_, v___y_531_);
if (v___x_532_ == 0)
{
lean_dec(v___y_531_);
lean_dec_ref(v___f_529_);
lean_dec(v_start_526_);
lean_dec_ref(v_array_525_);
return v___x_532_;
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_533_ = lean_usize_of_nat(v_start_526_);
lean_dec(v_start_526_);
v___x_534_ = lean_usize_of_nat(v___y_531_);
lean_dec(v___y_531_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_524_, v___f_529_, v_array_525_, v___x_533_, v___x_534_);
v___x_536_ = lean_unbox(v___x_535_);
lean_dec(v___x_535_);
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___boxed(lean_object* v_p_539_, lean_object* v_as_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Subarray_any___redArg(v_p_539_, v_as_540_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint8_t l_Subarray_any(lean_object* v_00_u03b1_543_, lean_object* v_p_544_, lean_object* v_as_545_){
_start:
{
lean_object* v___x_546_; lean_object* v_array_547_; lean_object* v_start_548_; lean_object* v_stop_549_; uint8_t v___x_550_; 
v___x_546_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_547_ = lean_ctor_get(v_as_545_, 0);
lean_inc_ref(v_array_547_);
v_start_548_ = lean_ctor_get(v_as_545_, 1);
lean_inc(v_start_548_);
v_stop_549_ = lean_ctor_get(v_as_545_, 2);
lean_inc(v_stop_549_);
lean_dec_ref(v_as_545_);
v___x_550_ = lean_nat_dec_lt(v_start_548_, v_stop_549_);
if (v___x_550_ == 0)
{
lean_dec(v_stop_549_);
lean_dec(v_start_548_);
lean_dec_ref(v_array_547_);
lean_dec_ref(v_p_544_);
return v___x_550_;
}
else
{
lean_object* v___f_551_; lean_object* v___y_553_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___f_551_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_551_, 0, v_p_544_);
v___x_559_ = lean_array_get_size(v_array_547_);
v___x_560_ = lean_nat_dec_le(v_stop_549_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v_stop_549_);
v___y_553_ = v___x_559_;
goto v___jp_552_;
}
else
{
v___y_553_ = v_stop_549_;
goto v___jp_552_;
}
v___jp_552_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_nat_dec_lt(v_start_548_, v___y_553_);
if (v___x_554_ == 0)
{
lean_dec(v___y_553_);
lean_dec_ref(v___f_551_);
lean_dec(v_start_548_);
lean_dec_ref(v_array_547_);
return v___x_554_;
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_555_ = lean_usize_of_nat(v_start_548_);
lean_dec(v_start_548_);
v___x_556_ = lean_usize_of_nat(v___y_553_);
lean_dec(v___y_553_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_546_, v___f_551_, v_array_547_, v___x_555_, v___x_556_);
v___x_558_ = lean_unbox(v___x_557_);
lean_dec(v___x_557_);
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_any___boxed(lean_object* v_00_u03b1_561_, lean_object* v_p_562_, lean_object* v_as_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Subarray_any(v_00_u03b1_561_, v_p_562_, v_as_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg___lam__0(lean_object* v_p_566_, uint8_t v___x_567_, lean_object* v_v_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_apply_1(v_p_566_, v_v_568_);
v___x_570_ = lean_unbox(v___x_569_);
if (v___x_570_ == 0)
{
return v___x_567_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = 0;
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object* v_p_572_, lean_object* v___x_573_, lean_object* v_v_574_){
_start:
{
uint8_t v___x_337__boxed_575_; uint8_t v_res_576_; lean_object* v_r_577_; 
v___x_337__boxed_575_ = lean_unbox(v___x_573_);
v_res_576_ = l_Subarray_all___redArg___lam__0(v_p_572_, v___x_337__boxed_575_, v_v_574_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all___redArg(lean_object* v_p_578_, lean_object* v_as_579_){
_start:
{
lean_object* v___x_580_; lean_object* v_array_581_; lean_object* v_start_582_; lean_object* v_stop_583_; uint8_t v___x_584_; 
v___x_580_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_581_ = lean_ctor_get(v_as_579_, 0);
lean_inc_ref(v_array_581_);
v_start_582_ = lean_ctor_get(v_as_579_, 1);
lean_inc(v_start_582_);
v_stop_583_ = lean_ctor_get(v_as_579_, 2);
lean_inc(v_stop_583_);
lean_dec_ref(v_as_579_);
v___x_584_ = lean_nat_dec_lt(v_start_582_, v_stop_583_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
lean_dec(v_stop_583_);
lean_dec(v_start_582_);
lean_dec_ref(v_array_581_);
lean_dec_ref(v_p_578_);
v___x_585_ = 1;
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___y_589_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_586_ = lean_box(v___x_584_);
v___f_587_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_587_, 0, v_p_578_);
lean_closure_set(v___f_587_, 1, v___x_586_);
v___x_596_ = lean_array_get_size(v_array_581_);
v___x_597_ = lean_nat_dec_le(v_stop_583_, v___x_596_);
if (v___x_597_ == 0)
{
lean_dec(v_stop_583_);
v___y_589_ = v___x_596_;
goto v___jp_588_;
}
else
{
v___y_589_ = v_stop_583_;
goto v___jp_588_;
}
v___jp_588_:
{
uint8_t v___x_590_; 
v___x_590_ = lean_nat_dec_lt(v_start_582_, v___y_589_);
if (v___x_590_ == 0)
{
lean_dec(v___y_589_);
lean_dec_ref(v___f_587_);
lean_dec(v_start_582_);
lean_dec_ref(v_array_581_);
return v___x_584_;
}
else
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_591_ = lean_usize_of_nat(v_start_582_);
lean_dec(v_start_582_);
v___x_592_ = lean_usize_of_nat(v___y_589_);
lean_dec(v___y_589_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_580_, v___f_587_, v_array_581_, v___x_591_, v___x_592_);
v___x_594_ = lean_unbox(v___x_593_);
lean_dec(v___x_593_);
if (v___x_594_ == 0)
{
return v___x_590_;
}
else
{
uint8_t v___x_595_; 
v___x_595_ = 0;
return v___x_595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___boxed(lean_object* v_p_598_, lean_object* v_as_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Subarray_all___redArg(v_p_598_, v_as_599_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT uint8_t l_Subarray_all(lean_object* v_00_u03b1_602_, lean_object* v_p_603_, lean_object* v_as_604_){
_start:
{
lean_object* v___x_605_; lean_object* v_array_606_; lean_object* v_start_607_; lean_object* v_stop_608_; uint8_t v___x_609_; 
v___x_605_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_606_ = lean_ctor_get(v_as_604_, 0);
lean_inc_ref(v_array_606_);
v_start_607_ = lean_ctor_get(v_as_604_, 1);
lean_inc(v_start_607_);
v_stop_608_ = lean_ctor_get(v_as_604_, 2);
lean_inc(v_stop_608_);
lean_dec_ref(v_as_604_);
v___x_609_ = lean_nat_dec_lt(v_start_607_, v_stop_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
lean_dec(v_stop_608_);
lean_dec(v_start_607_);
lean_dec_ref(v_array_606_);
lean_dec_ref(v_p_603_);
v___x_610_ = 1;
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___f_612_; lean_object* v___y_614_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_611_ = lean_box(v___x_609_);
v___f_612_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_612_, 0, v_p_603_);
lean_closure_set(v___f_612_, 1, v___x_611_);
v___x_621_ = lean_array_get_size(v_array_606_);
v___x_622_ = lean_nat_dec_le(v_stop_608_, v___x_621_);
if (v___x_622_ == 0)
{
lean_dec(v_stop_608_);
v___y_614_ = v___x_621_;
goto v___jp_613_;
}
else
{
v___y_614_ = v_stop_608_;
goto v___jp_613_;
}
v___jp_613_:
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v_start_607_, v___y_614_);
if (v___x_615_ == 0)
{
lean_dec(v___y_614_);
lean_dec_ref(v___f_612_);
lean_dec(v_start_607_);
lean_dec_ref(v_array_606_);
return v___x_609_;
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_616_ = lean_usize_of_nat(v_start_607_);
lean_dec(v_start_607_);
v___x_617_ = lean_usize_of_nat(v___y_614_);
lean_dec(v___y_614_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_605_, v___f_612_, v_array_606_, v___x_616_, v___x_617_);
v___x_619_ = lean_unbox(v___x_618_);
lean_dec(v___x_618_);
if (v___x_619_ == 0)
{
return v___x_615_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_all___boxed(lean_object* v_00_u03b1_623_, lean_object* v_p_624_, lean_object* v_as_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_Subarray_all(v_00_u03b1_623_, v_p_624_, v_as_625_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_628_, lean_object* v_as_629_, lean_object* v_f_630_, lean_object* v_n_631_, lean_object* v_toPure_632_, lean_object* v_r_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(v_inst_628_, v_as_629_, v_f_630_, v_n_631_, v_toPure_632_, v_r_633_);
lean_dec(v_n_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(lean_object* v_inst_635_, lean_object* v_as_636_, lean_object* v_f_637_, lean_object* v_i_638_){
_start:
{
lean_object* v_toApplicative_639_; lean_object* v_toBind_640_; lean_object* v_toPure_641_; lean_object* v_zero_642_; uint8_t v_isZero_643_; 
v_toApplicative_639_ = lean_ctor_get(v_inst_635_, 0);
v_toBind_640_ = lean_ctor_get(v_inst_635_, 1);
lean_inc(v_toBind_640_);
v_toPure_641_ = lean_ctor_get(v_toApplicative_639_, 1);
lean_inc(v_toPure_641_);
v_zero_642_ = lean_unsigned_to_nat(0u);
v_isZero_643_ = lean_nat_dec_eq(v_i_638_, v_zero_642_);
if (v_isZero_643_ == 1)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_toBind_640_);
lean_dec(v_f_637_);
lean_dec_ref(v_as_636_);
lean_dec_ref(v_inst_635_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_apply_2(v_toPure_641_, lean_box(0), v___x_644_);
return v___x_645_;
}
else
{
lean_object* v_one_646_; lean_object* v_n_647_; lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_one_646_ = lean_unsigned_to_nat(1u);
v_n_647_ = lean_nat_sub(v_i_638_, v_one_646_);
lean_inc(v_n_647_);
lean_inc(v_f_637_);
lean_inc_ref(v_as_636_);
v___f_648_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_648_, 0, v_inst_635_);
lean_closure_set(v___f_648_, 1, v_as_636_);
lean_closure_set(v___f_648_, 2, v_f_637_);
lean_closure_set(v___f_648_, 3, v_n_647_);
lean_closure_set(v___f_648_, 4, v_toPure_641_);
v___x_649_ = l_Subarray_get___redArg(v_as_636_, v_n_647_);
lean_dec(v_n_647_);
lean_dec_ref(v_as_636_);
v___x_650_ = lean_apply_1(v_f_637_, v___x_649_);
v___x_651_ = lean_apply_4(v_toBind_640_, lean_box(0), lean_box(0), v___x_650_, v___f_648_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_652_, lean_object* v_as_653_, lean_object* v_f_654_, lean_object* v_n_655_, lean_object* v_toPure_656_, lean_object* v_r_657_){
_start:
{
if (lean_obj_tag(v_r_657_) == 0)
{
lean_object* v___x_658_; 
lean_dec(v_toPure_656_);
v___x_658_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_652_, v_as_653_, v_f_654_, v_n_655_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; 
lean_dec(v_f_654_);
lean_dec_ref(v_as_653_);
lean_dec_ref(v_inst_652_);
v___x_659_ = lean_apply_2(v_toPure_656_, lean_box(0), v_r_657_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_660_, lean_object* v_as_661_, lean_object* v_f_662_, lean_object* v_i_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_660_, v_as_661_, v_f_662_, v_i_663_);
lean_dec(v_i_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_m_667_, lean_object* v_inst_668_, lean_object* v_as_669_, lean_object* v_f_670_, lean_object* v_i_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_668_, v_as_669_, v_f_670_, v_i_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_m_676_, lean_object* v_inst_677_, lean_object* v_as_678_, lean_object* v_f_679_, lean_object* v_i_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(v_00_u03b1_674_, v_00_u03b2_675_, v_m_676_, v_inst_677_, v_as_678_, v_f_679_, v_i_680_, v_a_681_);
lean_dec(v_i_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f___redArg(lean_object* v_inst_683_, lean_object* v_as_684_, lean_object* v_f_685_){
_start:
{
lean_object* v_start_686_; lean_object* v_stop_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_start_686_ = lean_ctor_get(v_as_684_, 1);
v_stop_687_ = lean_ctor_get(v_as_684_, 2);
v___x_688_ = lean_nat_sub(v_stop_687_, v_start_686_);
v___x_689_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_683_, v_as_684_, v_f_685_, v___x_688_);
lean_dec(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b2_691_, lean_object* v_m_692_, lean_object* v_inst_693_, lean_object* v_as_694_, lean_object* v_f_695_){
_start:
{
lean_object* v_start_696_; lean_object* v_stop_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_start_696_ = lean_ctor_get(v_as_694_, 1);
v_stop_697_ = lean_ctor_get(v_as_694_, 2);
v___x_698_ = lean_nat_sub(v_stop_697_, v_start_696_);
v___x_699_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_693_, v_as_694_, v_f_695_, v___x_698_);
lean_dec(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_700_, lean_object* v_a_701_, uint8_t v_____do__lift_702_){
_start:
{
if (v_____do__lift_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_a_701_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v_a_701_);
v___x_706_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_705_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_707_, lean_object* v_a_708_, lean_object* v_____do__lift_709_){
_start:
{
uint8_t v_____do__lift_63__boxed_710_; lean_object* v_res_711_; 
v_____do__lift_63__boxed_710_ = lean_unbox(v_____do__lift_709_);
v_res_711_ = l_Subarray_findRevM_x3f___redArg___lam__0(v_toPure_707_, v_a_708_, v_____do__lift_63__boxed_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_712_, lean_object* v_p_713_, lean_object* v_toBind_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_inc(v_a_715_);
v___f_716_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_716_, 0, v_toPure_712_);
lean_closure_set(v___f_716_, 1, v_a_715_);
v___x_717_ = lean_apply_1(v_p_713_, v_a_715_);
v___x_718_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_717_, v___f_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg(lean_object* v_inst_719_, lean_object* v_as_720_, lean_object* v_p_721_){
_start:
{
lean_object* v_toApplicative_722_; lean_object* v_toBind_723_; lean_object* v_toPure_724_; lean_object* v_start_725_; lean_object* v_stop_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_toApplicative_722_ = lean_ctor_get(v_inst_719_, 0);
v_toBind_723_ = lean_ctor_get(v_inst_719_, 1);
v_toPure_724_ = lean_ctor_get(v_toApplicative_722_, 1);
v_start_725_ = lean_ctor_get(v_as_720_, 1);
v_stop_726_ = lean_ctor_get(v_as_720_, 2);
lean_inc(v_toBind_723_);
lean_inc(v_toPure_724_);
v___f_727_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_727_, 0, v_toPure_724_);
lean_closure_set(v___f_727_, 1, v_p_721_);
lean_closure_set(v___f_727_, 2, v_toBind_723_);
v___x_728_ = lean_nat_sub(v_stop_726_, v_start_725_);
v___x_729_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_719_, v_as_720_, v___f_727_, v___x_728_);
lean_dec(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f(lean_object* v_00_u03b1_730_, lean_object* v_m_731_, lean_object* v_inst_732_, lean_object* v_as_733_, lean_object* v_p_734_){
_start:
{
lean_object* v_toApplicative_735_; lean_object* v_toBind_736_; lean_object* v_toPure_737_; lean_object* v_start_738_; lean_object* v_stop_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_toApplicative_735_ = lean_ctor_get(v_inst_732_, 0);
v_toBind_736_ = lean_ctor_get(v_inst_732_, 1);
v_toPure_737_ = lean_ctor_get(v_toApplicative_735_, 1);
v_start_738_ = lean_ctor_get(v_as_733_, 1);
v_stop_739_ = lean_ctor_get(v_as_733_, 2);
lean_inc(v_toBind_736_);
lean_inc(v_toPure_737_);
v___f_740_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_740_, 0, v_toPure_737_);
lean_closure_set(v___f_740_, 1, v_p_734_);
lean_closure_set(v___f_740_, 2, v_toBind_736_);
v___x_741_ = lean_nat_sub(v_stop_739_, v_start_738_);
v___x_742_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_732_, v_as_733_, v___f_740_, v___x_741_);
lean_dec(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg___lam__0(lean_object* v_p_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
lean_inc(v_a_744_);
v___x_745_ = lean_apply_1(v_p_743_, v_a_744_);
v___x_746_ = lean_unbox(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_a_744_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
else
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_a_744_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg(lean_object* v_as_749_, lean_object* v_p_750_){
_start:
{
lean_object* v___x_751_; lean_object* v_start_752_; lean_object* v_stop_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_751_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_752_ = lean_ctor_get(v_as_749_, 1);
v_stop_753_ = lean_ctor_get(v_as_749_, 2);
v___f_754_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_754_, 0, v_p_750_);
v___x_755_ = lean_nat_sub(v_stop_753_, v_start_752_);
v___x_756_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_751_, v_as_749_, v___f_754_, v___x_755_);
lean_dec(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f(lean_object* v_00_u03b1_757_, lean_object* v_as_758_, lean_object* v_p_759_){
_start:
{
lean_object* v___x_760_; lean_object* v_start_761_; lean_object* v_stop_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_761_ = lean_ctor_get(v_as_758_, 1);
v_stop_762_ = lean_ctor_get(v_as_758_, 2);
v___f_763_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_763_, 0, v_p_759_);
v___x_764_ = lean_nat_sub(v_stop_762_, v_start_761_);
v___x_765_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_760_, v_as_758_, v___f_763_, v___x_764_);
lean_dec(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray___redArg(lean_object* v_as_766_, lean_object* v_start_767_, lean_object* v_stop_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_array_get_size(v_as_766_);
v___x_770_ = lean_nat_dec_le(v_stop_768_, v___x_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
lean_dec(v_stop_768_);
v___x_771_ = lean_nat_dec_le(v_start_767_, v___x_769_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec(v_start_767_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v_as_766_);
lean_ctor_set(v___x_772_, 1, v___x_769_);
lean_ctor_set(v___x_772_, 2, v___x_769_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_773_, 0, v_as_766_);
lean_ctor_set(v___x_773_, 1, v_start_767_);
lean_ctor_set(v___x_773_, 2, v___x_769_);
return v___x_773_;
}
}
else
{
uint8_t v___x_774_; 
v___x_774_ = lean_nat_dec_le(v_start_767_, v_stop_768_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_start_767_);
lean_inc(v_stop_768_);
v___x_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_775_, 0, v_as_766_);
lean_ctor_set(v___x_775_, 1, v_stop_768_);
lean_ctor_set(v___x_775_, 2, v_stop_768_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_776_, 0, v_as_766_);
lean_ctor_set(v___x_776_, 1, v_start_767_);
lean_ctor_set(v___x_776_, 2, v_stop_768_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray(lean_object* v_00_u03b1_777_, lean_object* v_as_778_, lean_object* v_start_779_, lean_object* v_stop_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Array_toSubarray___redArg(v_as_778_, v_start_779_, v_stop_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5));
v___x_899_ = l_String_toRawSubstring_x27(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(lean_object* v_x_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Array_term_____x5b___x3a___x5d___closed__2));
lean_inc(v_x_913_);
v___x_917_ = l_Lean_Syntax_isOfKind(v_x_913_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_x_913_);
v___x_918_ = lean_box(1);
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v_a_915_);
return v___x_919_;
}
else
{
lean_object* v_quotContext_920_; lean_object* v_currMacroScope_921_; lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_quotContext_920_ = lean_ctor_get(v_a_914_, 1);
v_currMacroScope_921_ = lean_ctor_get(v_a_914_, 2);
v_ref_922_ = lean_ctor_get(v_a_914_, 5);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = l_Lean_Syntax_getArg(v_x_913_, v___x_923_);
v___x_925_ = lean_unsigned_to_nat(2u);
v___x_926_ = l_Lean_Syntax_getArg(v_x_913_, v___x_925_);
v___x_927_ = lean_unsigned_to_nat(4u);
v___x_928_ = l_Lean_Syntax_getArg(v_x_913_, v___x_927_);
lean_dec(v_x_913_);
v___x_929_ = 0;
v___x_930_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_929_);
v___x_931_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_932_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_933_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_921_);
lean_inc(v_quotContext_920_);
v___x_934_ = l_Lean_addMacroScope(v_quotContext_920_, v___x_933_, v_currMacroScope_921_);
v___x_935_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_930_, 2);
v___x_936_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_936_, 0, v___x_930_);
lean_ctor_set(v___x_936_, 1, v___x_932_);
lean_ctor_set(v___x_936_, 2, v___x_934_);
lean_ctor_set(v___x_936_, 3, v___x_935_);
v___x_937_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_938_ = l_Lean_Syntax_node3(v___x_930_, v___x_937_, v___x_924_, v___x_926_, v___x_928_);
v___x_939_ = l_Lean_Syntax_node2(v___x_930_, v___x_931_, v___x_936_, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_a_915_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(lean_object* v_x_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(v_x_941_, v_a_942_, v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object* v_x_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = ((lean_object*)(l_Array_term_____x5b_x3a___x5d___closed__1));
lean_inc(v_x_949_);
v___x_953_ = l_Lean_Syntax_isOfKind(v_x_949_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_x_949_);
v___x_954_ = lean_box(1);
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_a_951_);
return v___x_955_;
}
else
{
lean_object* v_quotContext_956_; lean_object* v_currMacroScope_957_; lean_object* v_ref_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_quotContext_956_ = lean_ctor_get(v_a_950_, 1);
v_currMacroScope_957_ = lean_ctor_get(v_a_950_, 2);
v_ref_958_ = lean_ctor_get(v_a_950_, 5);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = l_Lean_Syntax_getArg(v_x_949_, v___x_959_);
v___x_961_ = lean_unsigned_to_nat(3u);
v___x_962_ = l_Lean_Syntax_getArg(v_x_949_, v___x_961_);
lean_dec(v_x_949_);
v___x_963_ = 0;
v___x_964_ = l_Lean_SourceInfo_fromRef(v_ref_958_, v___x_963_);
v___x_965_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_966_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_967_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_957_);
lean_inc(v_quotContext_956_);
v___x_968_ = l_Lean_addMacroScope(v_quotContext_956_, v___x_967_, v_currMacroScope_957_);
v___x_969_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_964_, 4);
v___x_970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_970_, 0, v___x_964_);
lean_ctor_set(v___x_970_, 1, v___x_966_);
lean_ctor_set(v___x_970_, 2, v___x_968_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
v___x_971_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_972_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1));
v___x_973_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2));
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_964_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_Syntax_node1(v___x_964_, v___x_972_, v___x_974_);
v___x_976_ = l_Lean_Syntax_node3(v___x_964_, v___x_971_, v___x_960_, v___x_975_, v___x_962_);
v___x_977_ = l_Lean_Syntax_node2(v___x_964_, v___x_965_, v___x_970_, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_951_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(v_x_979_, v_a_980_, v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_982_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Array_mkArray0___redArg();
return v___x_995_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11));
v___x_1016_ = l_String_toRawSubstring_x27(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18));
v___x_1029_ = l_String_toRawSubstring_x27(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(lean_object* v_x_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Array_term_____x5b___x3a_x5d___closed__1));
lean_inc(v_x_1034_);
v___x_1038_ = l_Lean_Syntax_isOfKind(v_x_1034_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v_x_1034_);
v___x_1039_ = lean_box(1);
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_a_1036_);
return v___x_1040_;
}
else
{
lean_object* v_quotContext_1041_; lean_object* v_currMacroScope_1042_; lean_object* v_ref_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_quotContext_1041_ = lean_ctor_get(v_a_1035_, 1);
v_currMacroScope_1042_ = lean_ctor_get(v_a_1035_, 2);
v_ref_1043_ = lean_ctor_get(v_a_1035_, 5);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_Lean_Syntax_getArg(v_x_1034_, v___x_1044_);
v___x_1046_ = lean_unsigned_to_nat(2u);
v___x_1047_ = l_Lean_Syntax_getArg(v_x_1034_, v___x_1046_);
lean_dec(v_x_1034_);
v___x_1048_ = 0;
v___x_1049_ = l_Lean_SourceInfo_fromRef(v_ref_1043_, v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0));
v___x_1051_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1));
lean_inc_n(v___x_1049_, 13);
v___x_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1050_);
v___x_1053_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3));
v___x_1054_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_1055_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
v___x_1056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1049_);
lean_ctor_set(v___x_1056_, 1, v___x_1054_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
lean_inc_ref_n(v___x_1056_, 2);
v___x_1057_ = l_Lean_Syntax_node1(v___x_1049_, v___x_1053_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6));
v___x_1059_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8));
v___x_1060_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10));
v___x_1061_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
v___x_1062_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13));
lean_inc_n(v_currMacroScope_1042_, 3);
lean_inc_n(v_quotContext_1041_, 3);
v___x_1063_ = l_Lean_addMacroScope(v_quotContext_1041_, v___x_1062_, v_currMacroScope_1042_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1049_);
lean_ctor_set(v___x_1065_, 1, v___x_1061_);
lean_ctor_set(v___x_1065_, 2, v___x_1063_);
lean_ctor_set(v___x_1065_, 3, v___x_1064_);
lean_inc_ref(v___x_1065_);
v___x_1066_ = l_Lean_Syntax_node1(v___x_1049_, v___x_1060_, v___x_1065_);
v___x_1067_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14));
v___x_1068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1049_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_Syntax_node5(v___x_1049_, v___x_1059_, v___x_1066_, v___x_1056_, v___x_1056_, v___x_1068_, v___x_1045_);
v___x_1070_ = l_Lean_Syntax_node1(v___x_1049_, v___x_1058_, v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15));
v___x_1072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1049_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_1074_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_1075_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
v___x_1076_ = l_Lean_addMacroScope(v_quotContext_1041_, v___x_1075_, v_currMacroScope_1042_);
v___x_1077_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17));
v___x_1078_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1049_);
lean_ctor_set(v___x_1078_, 1, v___x_1074_);
lean_ctor_set(v___x_1078_, 2, v___x_1076_);
lean_ctor_set(v___x_1078_, 3, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
v___x_1080_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21));
v___x_1081_ = l_Lean_addMacroScope(v_quotContext_1041_, v___x_1080_, v_currMacroScope_1042_);
v___x_1082_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1049_);
lean_ctor_set(v___x_1082_, 1, v___x_1079_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
lean_ctor_set(v___x_1082_, 3, v___x_1064_);
v___x_1083_ = l_Lean_Syntax_node3(v___x_1049_, v___x_1054_, v___x_1065_, v___x_1047_, v___x_1082_);
v___x_1084_ = l_Lean_Syntax_node2(v___x_1049_, v___x_1073_, v___x_1078_, v___x_1083_);
v___x_1085_ = l_Lean_Syntax_node5(v___x_1049_, v___x_1051_, v___x_1052_, v___x_1057_, v___x_1070_, v___x_1072_, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_a_1036_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(lean_object* v_x_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(v_x_1087_, v_a_1088_, v_a_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1090_;
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
