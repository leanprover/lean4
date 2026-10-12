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
lean_object* l_Subarray_instSliceSizeSubarrayData___redArg(){
_start:
{
lean_object* v___f_39_; 
v___f_39_ = ((lean_object*)(l_Subarray_instSliceSizeSubarrayData___redArg___closed__0));
return v___f_39_;
}
}
LEAN_EXPORT void l_Subarray_instSliceSizeSubarrayData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_40_;
v_res_40_ = l_Subarray_instSliceSizeSubarrayData___redArg();
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData___redArg___boxed(lean_object* v___dummy_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Subarray_instSliceSizeSubarrayData___redArg();
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instSliceSizeSubarrayData(lean_object* v_00_u03b1_43_){
_start:
{
lean_object* v___f_44_; 
v___f_44_ = ((lean_object*)(l_Subarray_instSliceSizeSubarrayData___redArg___closed__0));
return v___f_44_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___redArg(lean_object* v_s_45_, lean_object* v_i_46_){
_start:
{
lean_object* v_array_47_; lean_object* v_start_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_array_47_ = lean_ctor_get(v_s_45_, 0);
v_start_48_ = lean_ctor_get(v_s_45_, 1);
v___x_49_ = lean_nat_add(v_start_48_, v_i_46_);
v___x_50_ = lean_array_fget_borrowed(v_array_47_, v___x_49_);
lean_dec(v___x_49_);
lean_inc(v___x_50_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___redArg___boxed(lean_object* v_s_51_, lean_object* v_i_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Subarray_get___redArg(v_s_51_, v_i_52_);
lean_dec(v_i_52_);
lean_dec_ref(v_s_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get(lean_object* v_00_u03b1_54_, lean_object* v_s_55_, lean_object* v_i_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Subarray_get___redArg(v_s_55_, v_i_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get___boxed(lean_object* v_00_u03b1_58_, lean_object* v_s_59_, lean_object* v_i_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Subarray_get(v_00_u03b1_58_, v_s_59_, v_i_60_);
lean_dec(v_i_60_);
lean_dec_ref(v_s_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0(lean_object* v_xs_62_, lean_object* v_i_63_, lean_object* v_h_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Subarray_get___redArg(v_xs_62_, v_i_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0___boxed(lean_object* v_xs_66_, lean_object* v_i_67_, lean_object* v_h_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___lam__0(v_xs_66_, v_i_67_, v_h_68_);
lean_dec(v_i_67_);
lean_dec_ref(v_xs_66_);
return v_res_69_;
}
}
lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg(){
_start:
{
lean_object* v___f_72_; 
v___f_72_ = ((lean_object*)(l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0));
return v___f_72_;
}
}
LEAN_EXPORT void l_Subarray_instGetElemNatLtSizeSubarrayData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_73_;
v_res_73_ = l_Subarray_instGetElemNatLtSizeSubarrayData___redArg();
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___boxed(lean_object* v___dummy_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Subarray_instGetElemNatLtSizeSubarrayData___redArg();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instGetElemNatLtSizeSubarrayData(lean_object* v_00_u03b1_76_){
_start:
{
lean_object* v___f_77_; 
v___f_77_ = ((lean_object*)(l_Subarray_instGetElemNatLtSizeSubarrayData___redArg___closed__0));
return v___f_77_;
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___redArg(lean_object* v_s_78_, lean_object* v_i_79_, lean_object* v_v_u2080_80_){
_start:
{
lean_object* v_start_81_; lean_object* v_stop_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_start_81_ = lean_ctor_get(v_s_78_, 1);
v_stop_82_ = lean_ctor_get(v_s_78_, 2);
v___x_83_ = lean_nat_sub(v_stop_82_, v_start_81_);
v___x_84_ = lean_nat_dec_lt(v_i_79_, v___x_83_);
lean_dec(v___x_83_);
if (v___x_84_ == 0)
{
lean_inc(v_v_u2080_80_);
return v_v_u2080_80_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = l_Subarray_get___redArg(v_s_78_, v_i_79_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___redArg___boxed(lean_object* v_s_86_, lean_object* v_i_87_, lean_object* v_v_u2080_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Subarray_getD___redArg(v_s_86_, v_i_87_, v_v_u2080_88_);
lean_dec(v_v_u2080_88_);
lean_dec(v_i_87_);
lean_dec_ref(v_s_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Subarray_getD(lean_object* v_00_u03b1_90_, lean_object* v_s_91_, lean_object* v_i_92_, lean_object* v_v_u2080_93_){
_start:
{
lean_object* v_start_94_; lean_object* v_stop_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_start_94_ = lean_ctor_get(v_s_91_, 1);
v_stop_95_ = lean_ctor_get(v_s_91_, 2);
v___x_96_ = lean_nat_sub(v_stop_95_, v_start_94_);
v___x_97_ = lean_nat_dec_lt(v_i_92_, v___x_96_);
lean_dec(v___x_96_);
if (v___x_97_ == 0)
{
lean_inc(v_v_u2080_93_);
return v_v_u2080_93_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = l_Subarray_get___redArg(v_s_91_, v_i_92_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_getD___boxed(lean_object* v_00_u03b1_99_, lean_object* v_s_100_, lean_object* v_i_101_, lean_object* v_v_u2080_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Subarray_getD(v_00_u03b1_99_, v_s_100_, v_i_101_, v_v_u2080_102_);
lean_dec(v_v_u2080_102_);
lean_dec(v_i_101_);
lean_dec_ref(v_s_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg(lean_object* v_inst_104_, lean_object* v_s_105_, lean_object* v_i_106_){
_start:
{
lean_object* v_start_107_; lean_object* v_stop_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_start_107_ = lean_ctor_get(v_s_105_, 1);
v_stop_108_ = lean_ctor_get(v_s_105_, 2);
v___x_109_ = lean_nat_sub(v_stop_108_, v_start_107_);
v___x_110_ = lean_nat_dec_lt(v_i_106_, v___x_109_);
lean_dec(v___x_109_);
if (v___x_110_ == 0)
{
lean_inc(v_inst_104_);
return v_inst_104_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = l_Subarray_get___redArg(v_s_105_, v_i_106_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___redArg___boxed(lean_object* v_inst_112_, lean_object* v_s_113_, lean_object* v_i_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Subarray_get_x21___redArg(v_inst_112_, v_s_113_, v_i_114_);
lean_dec(v_i_114_);
lean_dec_ref(v_s_113_);
lean_dec(v_inst_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21(lean_object* v_00_u03b1_116_, lean_object* v_inst_117_, lean_object* v_s_118_, lean_object* v_i_119_){
_start:
{
lean_object* v_start_120_; lean_object* v_stop_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_start_120_ = lean_ctor_get(v_s_118_, 1);
v_stop_121_ = lean_ctor_get(v_s_118_, 2);
v___x_122_ = lean_nat_sub(v_stop_121_, v_start_120_);
v___x_123_ = lean_nat_dec_lt(v_i_119_, v___x_122_);
lean_dec(v___x_122_);
if (v___x_123_ == 0)
{
lean_inc(v_inst_117_);
return v_inst_117_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = l_Subarray_get___redArg(v_s_118_, v_i_119_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_get_x21___boxed(lean_object* v_00_u03b1_125_, lean_object* v_inst_126_, lean_object* v_s_127_, lean_object* v_i_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Subarray_get_x21(v_00_u03b1_125_, v_inst_126_, v_s_127_, v_i_128_);
lean_dec(v_i_128_);
lean_dec_ref(v_s_127_);
lean_dec(v_inst_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Subarray_popFront___redArg(lean_object* v_s_130_){
_start:
{
lean_object* v_array_131_; lean_object* v_start_132_; lean_object* v_stop_133_; uint8_t v___x_134_; 
v_array_131_ = lean_ctor_get(v_s_130_, 0);
v_start_132_ = lean_ctor_get(v_s_130_, 1);
v_stop_133_ = lean_ctor_get(v_s_130_, 2);
v___x_134_ = lean_nat_dec_lt(v_start_132_, v_stop_133_);
if (v___x_134_ == 0)
{
return v_s_130_;
}
else
{
lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_143_; 
lean_inc(v_stop_133_);
lean_inc(v_start_132_);
lean_inc_ref(v_array_131_);
v_isSharedCheck_143_ = !lean_is_exclusive(v_s_130_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_144_ = lean_ctor_get(v_s_130_, 2);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_s_130_, 1);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_s_130_, 0);
lean_dec(v_unused_146_);
v___x_136_ = v_s_130_;
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
else
{
lean_dec(v_s_130_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_start_132_, v___x_138_);
lean_dec(v_start_132_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_139_);
v___x_141_ = v___x_136_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_array_131_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_stop_133_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_popFront(lean_object* v_00_u03b1_147_, lean_object* v_s_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Subarray_popFront___redArg(v_s_148_);
return v___x_149_;
}
}
lean_object* l_Subarray_empty___redArg(){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = ((lean_object*)(l_Subarray_empty___redArg___closed__1));
return v___x_156_;
}
}
LEAN_EXPORT void l_Subarray_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_157_;
v_res_157_ = l_Subarray_empty___redArg();
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Subarray_empty___redArg___boxed(lean_object* v___dummy_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Subarray_empty___redArg();
return v_res_159_;
}
}
static lean_object* _init_l_Subarray_empty___closed__0(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Subarray_empty___redArg();
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Subarray_empty(lean_object* v_00_u03b1_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_162_;
}
}
lean_object* l_Subarray_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_164_;
}
}
LEAN_EXPORT void l_Subarray_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_165_;
v_res_165_ = l_Subarray_instEmptyCollection___redArg();
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection___redArg___boxed(lean_object* v___dummy_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Subarray_instEmptyCollection___redArg();
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instEmptyCollection(lean_object* v_00_u03b1_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_169_;
}
}
lean_object* l_Subarray_instInhabited___redArg(){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_171_;
}
}
LEAN_EXPORT void l_Subarray_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_172_;
v_res_172_ = l_Subarray_instInhabited___redArg();
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Subarray_instInhabited___redArg___boxed(lean_object* v___dummy_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Subarray_instInhabited___redArg();
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instInhabited(lean_object* v_00_u03b1_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Subarray_empty___closed__0, &l_Subarray_empty___closed__0_once, _init_l_Subarray_empty___closed__0);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM___redArg(lean_object* v_inst_177_, lean_object* v_f_178_, lean_object* v_init_179_, lean_object* v_as_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_array_182_; lean_object* v_start_183_; lean_object* v_stop_184_; lean_object* v_toPure_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_177_, 0);
v_array_182_ = lean_ctor_get(v_as_180_, 0);
lean_inc_ref(v_array_182_);
v_start_183_ = lean_ctor_get(v_as_180_, 1);
lean_inc(v_start_183_);
v_stop_184_ = lean_ctor_get(v_as_180_, 2);
lean_inc(v_stop_184_);
lean_dec_ref(v_as_180_);
v_toPure_185_ = lean_ctor_get(v_toApplicative_181_, 1);
v___x_186_ = lean_array_get_size(v_array_182_);
v___x_187_ = lean_nat_dec_le(v_stop_184_, v___x_186_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
lean_dec(v_stop_184_);
v___x_188_ = lean_nat_dec_lt(v_start_183_, v___x_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
lean_inc(v_toPure_185_);
lean_dec(v_start_183_);
lean_dec_ref(v_array_182_);
lean_dec(v_f_178_);
lean_dec_ref(v_inst_177_);
v___x_189_ = lean_apply_2(v_toPure_185_, lean_box(0), v_init_179_);
return v___x_189_;
}
else
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_usize_of_nat(v___x_186_);
v___x_191_ = lean_usize_of_nat(v_start_183_);
lean_dec(v_start_183_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_177_, v_f_178_, v_array_182_, v___x_190_, v___x_191_, v_init_179_);
return v___x_192_;
}
}
else
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_lt(v_start_183_, v_stop_184_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_inc(v_toPure_185_);
lean_dec(v_stop_184_);
lean_dec(v_start_183_);
lean_dec_ref(v_array_182_);
lean_dec(v_f_178_);
lean_dec_ref(v_inst_177_);
v___x_194_ = lean_apply_2(v_toPure_185_, lean_box(0), v_init_179_);
return v___x_194_;
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_usize_of_nat(v_stop_184_);
lean_dec(v_stop_184_);
v___x_196_ = lean_usize_of_nat(v_start_183_);
lean_dec(v_start_183_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_177_, v_f_178_, v_array_182_, v___x_195_, v___x_196_, v_init_179_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldrM(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_, lean_object* v_m_200_, lean_object* v_inst_201_, lean_object* v_f_202_, lean_object* v_init_203_, lean_object* v_as_204_){
_start:
{
lean_object* v_toApplicative_205_; lean_object* v_array_206_; lean_object* v_start_207_; lean_object* v_stop_208_; lean_object* v_toPure_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_toApplicative_205_ = lean_ctor_get(v_inst_201_, 0);
v_array_206_ = lean_ctor_get(v_as_204_, 0);
lean_inc_ref(v_array_206_);
v_start_207_ = lean_ctor_get(v_as_204_, 1);
lean_inc(v_start_207_);
v_stop_208_ = lean_ctor_get(v_as_204_, 2);
lean_inc(v_stop_208_);
lean_dec_ref(v_as_204_);
v_toPure_209_ = lean_ctor_get(v_toApplicative_205_, 1);
v___x_210_ = lean_array_get_size(v_array_206_);
v___x_211_ = lean_nat_dec_le(v_stop_208_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
lean_dec(v_stop_208_);
v___x_212_ = lean_nat_dec_lt(v_start_207_, v___x_210_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_inc(v_toPure_209_);
lean_dec(v_start_207_);
lean_dec_ref(v_array_206_);
lean_dec(v_f_202_);
lean_dec_ref(v_inst_201_);
v___x_213_ = lean_apply_2(v_toPure_209_, lean_box(0), v_init_203_);
return v___x_213_;
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_usize_of_nat(v___x_210_);
v___x_215_ = lean_usize_of_nat(v_start_207_);
lean_dec(v_start_207_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_201_, v_f_202_, v_array_206_, v___x_214_, v___x_215_, v_init_203_);
return v___x_216_;
}
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_lt(v_start_207_, v_stop_208_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_inc(v_toPure_209_);
lean_dec(v_stop_208_);
lean_dec(v_start_207_);
lean_dec_ref(v_array_206_);
lean_dec(v_f_202_);
lean_dec_ref(v_inst_201_);
v___x_218_ = lean_apply_2(v_toPure_209_, lean_box(0), v_init_203_);
return v___x_218_;
}
else
{
size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_usize_of_nat(v_stop_208_);
lean_dec(v_stop_208_);
v___x_220_ = lean_usize_of_nat(v_start_207_);
lean_dec(v_start_207_);
v___x_221_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_201_, v_f_202_, v_array_206_, v___x_219_, v___x_220_, v_init_203_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM___redArg(lean_object* v_inst_222_, lean_object* v_p_223_, lean_object* v_as_224_){
_start:
{
lean_object* v_toApplicative_225_; lean_object* v_array_226_; lean_object* v_start_227_; lean_object* v_stop_228_; lean_object* v_toPure_229_; lean_object* v___y_231_; uint8_t v___x_238_; 
v_toApplicative_225_ = lean_ctor_get(v_inst_222_, 0);
v_array_226_ = lean_ctor_get(v_as_224_, 0);
lean_inc_ref(v_array_226_);
v_start_227_ = lean_ctor_get(v_as_224_, 1);
lean_inc(v_start_227_);
v_stop_228_ = lean_ctor_get(v_as_224_, 2);
lean_inc(v_stop_228_);
lean_dec_ref(v_as_224_);
v_toPure_229_ = lean_ctor_get(v_toApplicative_225_, 1);
v___x_238_ = lean_nat_dec_lt(v_start_227_, v_stop_228_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_inc(v_toPure_229_);
lean_dec(v_stop_228_);
lean_dec(v_start_227_);
lean_dec_ref(v_array_226_);
lean_dec(v_p_223_);
lean_dec_ref(v_inst_222_);
v___x_239_ = lean_box(v___x_238_);
v___x_240_ = lean_apply_2(v_toPure_229_, lean_box(0), v___x_239_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_array_get_size(v_array_226_);
v___x_242_ = lean_nat_dec_le(v_stop_228_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec(v_stop_228_);
v___y_231_ = v___x_241_;
goto v___jp_230_;
}
else
{
v___y_231_ = v_stop_228_;
goto v___jp_230_;
}
}
v___jp_230_:
{
uint8_t v___x_232_; 
v___x_232_ = lean_nat_dec_lt(v_start_227_, v___y_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc(v_toPure_229_);
lean_dec(v___y_231_);
lean_dec(v_start_227_);
lean_dec_ref(v_array_226_);
lean_dec(v_p_223_);
lean_dec_ref(v_inst_222_);
v___x_233_ = lean_box(v___x_232_);
v___x_234_ = lean_apply_2(v_toPure_229_, lean_box(0), v___x_233_);
return v___x_234_;
}
else
{
size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_usize_of_nat(v_start_227_);
lean_dec(v_start_227_);
v___x_236_ = lean_usize_of_nat(v___y_231_);
lean_dec(v___y_231_);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_222_, v_p_223_, v_array_226_, v___x_235_, v___x_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_anyM(lean_object* v_00_u03b1_243_, lean_object* v_m_244_, lean_object* v_inst_245_, lean_object* v_p_246_, lean_object* v_as_247_){
_start:
{
lean_object* v_toApplicative_248_; lean_object* v_array_249_; lean_object* v_start_250_; lean_object* v_stop_251_; lean_object* v_toPure_252_; lean_object* v___y_254_; uint8_t v___x_261_; 
v_toApplicative_248_ = lean_ctor_get(v_inst_245_, 0);
v_array_249_ = lean_ctor_get(v_as_247_, 0);
lean_inc_ref(v_array_249_);
v_start_250_ = lean_ctor_get(v_as_247_, 1);
lean_inc(v_start_250_);
v_stop_251_ = lean_ctor_get(v_as_247_, 2);
lean_inc(v_stop_251_);
lean_dec_ref(v_as_247_);
v_toPure_252_ = lean_ctor_get(v_toApplicative_248_, 1);
v___x_261_ = lean_nat_dec_lt(v_start_250_, v_stop_251_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc(v_toPure_252_);
lean_dec(v_stop_251_);
lean_dec(v_start_250_);
lean_dec_ref(v_array_249_);
lean_dec(v_p_246_);
lean_dec_ref(v_inst_245_);
v___x_262_ = lean_box(v___x_261_);
v___x_263_ = lean_apply_2(v_toPure_252_, lean_box(0), v___x_262_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_array_get_size(v_array_249_);
v___x_265_ = lean_nat_dec_le(v_stop_251_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v_stop_251_);
v___y_254_ = v___x_264_;
goto v___jp_253_;
}
else
{
v___y_254_ = v_stop_251_;
goto v___jp_253_;
}
}
v___jp_253_:
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_lt(v_start_250_, v___y_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_inc(v_toPure_252_);
lean_dec(v___y_254_);
lean_dec(v_start_250_);
lean_dec_ref(v_array_249_);
lean_dec(v_p_246_);
lean_dec_ref(v_inst_245_);
v___x_256_ = lean_box(v___x_255_);
v___x_257_ = lean_apply_2(v_toPure_252_, lean_box(0), v___x_256_);
return v___x_257_;
}
else
{
size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_usize_of_nat(v_start_250_);
lean_dec(v_start_250_);
v___x_259_ = lean_usize_of_nat(v___y_254_);
lean_dec(v___y_254_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_245_, v_p_246_, v_array_249_, v___x_258_, v___x_259_);
return v___x_260_;
}
}
}
}
lean_object* l_Subarray_allM___redArg___lam__0(lean_object* v_toPure_266_, uint8_t v_____do__lift_267_){
_start:
{
if (v_____do__lift_267_ == 0)
{
uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = 1;
v___x_269_ = lean_box(v___x_268_);
v___x_270_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_269_);
return v___x_270_;
}
else
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = 0;
v___x_272_ = lean_box(v___x_271_);
v___x_273_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT void l_Subarray_allM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_266_ = stack[0].m_obj;
uint8_t v_____do__lift_267_ = stack[1].m_num;
lean_object* v_res_274_;
v_res_274_ = l_Subarray_allM___redArg___lam__0(v_toPure_266_, v_____do__lift_267_);
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__0___boxed(lean_object* v_toPure_275_, lean_object* v_____do__lift_276_){
_start:
{
uint8_t v_____do__lift_110__boxed_277_; lean_object* v_res_278_; 
v_____do__lift_110__boxed_277_ = lean_unbox(v_____do__lift_276_);
v_res_278_ = l_Subarray_allM___redArg___lam__0(v_toPure_275_, v_____do__lift_110__boxed_277_);
return v_res_278_;
}
}
lean_object* l_Subarray_allM___redArg___lam__1(lean_object* v_toPure_279_, uint8_t v___x_280_, uint8_t v_____do__lift_281_){
_start:
{
if (v_____do__lift_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_box(v___x_280_);
v___x_283_ = lean_apply_2(v_toPure_279_, lean_box(0), v___x_282_);
return v___x_283_;
}
else
{
uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = 0;
v___x_285_ = lean_box(v___x_284_);
v___x_286_ = lean_apply_2(v_toPure_279_, lean_box(0), v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT void l_Subarray_allM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_279_ = stack[0].m_obj;
uint8_t v___x_280_ = stack[1].m_num;
uint8_t v_____do__lift_281_ = stack[2].m_num;
lean_object* v_res_287_;
v_res_287_ = l_Subarray_allM___redArg___lam__1(v_toPure_279_, v___x_280_, v_____do__lift_281_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__1___boxed(lean_object* v_toPure_288_, lean_object* v___x_289_, lean_object* v_____do__lift_290_){
_start:
{
uint8_t v___x_133__boxed_291_; uint8_t v_____do__lift_134__boxed_292_; lean_object* v_res_293_; 
v___x_133__boxed_291_ = lean_unbox(v___x_289_);
v_____do__lift_134__boxed_292_ = lean_unbox(v_____do__lift_290_);
v_res_293_ = l_Subarray_allM___redArg___lam__1(v_toPure_288_, v___x_133__boxed_291_, v_____do__lift_134__boxed_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg___lam__2(lean_object* v_p_294_, lean_object* v_toBind_295_, lean_object* v___f_296_, lean_object* v_v_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_apply_1(v_p_294_, v_v_297_);
v___x_299_ = lean_apply_4(v_toBind_295_, lean_box(0), lean_box(0), v___x_298_, v___f_296_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Subarray_allM___redArg(lean_object* v_inst_300_, lean_object* v_p_301_, lean_object* v_as_302_){
_start:
{
lean_object* v_toApplicative_303_; lean_object* v_array_304_; lean_object* v_start_305_; lean_object* v_stop_306_; lean_object* v_toBind_307_; lean_object* v_toPure_308_; lean_object* v___f_309_; uint8_t v___x_310_; 
v_toApplicative_303_ = lean_ctor_get(v_inst_300_, 0);
v_array_304_ = lean_ctor_get(v_as_302_, 0);
lean_inc_ref(v_array_304_);
v_start_305_ = lean_ctor_get(v_as_302_, 1);
lean_inc(v_start_305_);
v_stop_306_ = lean_ctor_get(v_as_302_, 2);
lean_inc(v_stop_306_);
lean_dec_ref(v_as_302_);
v_toBind_307_ = lean_ctor_get(v_inst_300_, 1);
lean_inc(v_toBind_307_);
v_toPure_308_ = lean_ctor_get(v_toApplicative_303_, 1);
lean_inc(v_toPure_308_);
v___f_309_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_309_, 0, v_toPure_308_);
v___x_310_ = lean_nat_dec_lt(v_start_305_, v_stop_306_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc(v_toPure_308_);
lean_dec(v_stop_306_);
lean_dec(v_start_305_);
lean_dec_ref(v_array_304_);
lean_dec(v_p_301_);
lean_dec_ref(v_inst_300_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_apply_2(v_toPure_308_, lean_box(0), v___x_311_);
v___x_313_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_312_, v___f_309_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___y_318_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_314_ = lean_box(v___x_310_);
lean_inc(v_toPure_308_);
v___f_315_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_315_, 0, v_toPure_308_);
lean_closure_set(v___f_315_, 1, v___x_314_);
lean_inc(v_toBind_307_);
v___f_316_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_316_, 0, v_p_301_);
lean_closure_set(v___f_316_, 1, v_toBind_307_);
lean_closure_set(v___f_316_, 2, v___f_315_);
v___x_327_ = lean_array_get_size(v_array_304_);
v___x_328_ = lean_nat_dec_le(v_stop_306_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec(v_stop_306_);
v___y_318_ = v___x_327_;
goto v___jp_317_;
}
else
{
v___y_318_ = v_stop_306_;
goto v___jp_317_;
}
v___jp_317_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_lt(v_start_305_, v___y_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc(v_toPure_308_);
lean_dec(v___y_318_);
lean_dec_ref(v___f_316_);
lean_dec(v_start_305_);
lean_dec_ref(v_array_304_);
lean_dec_ref(v_inst_300_);
v___x_320_ = lean_box(v___x_319_);
v___x_321_ = lean_apply_2(v_toPure_308_, lean_box(0), v___x_320_);
v___x_322_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_321_, v___f_309_);
return v___x_322_;
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_usize_of_nat(v_start_305_);
lean_dec(v_start_305_);
v___x_324_ = lean_usize_of_nat(v___y_318_);
lean_dec(v___y_318_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_300_, v___f_316_, v_array_304_, v___x_323_, v___x_324_);
v___x_326_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_325_, v___f_309_);
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_allM(lean_object* v_00_u03b1_329_, lean_object* v_m_330_, lean_object* v_inst_331_, lean_object* v_p_332_, lean_object* v_as_333_){
_start:
{
lean_object* v_toApplicative_334_; lean_object* v_array_335_; lean_object* v_start_336_; lean_object* v_stop_337_; lean_object* v_toBind_338_; lean_object* v_toPure_339_; lean_object* v___f_340_; uint8_t v___x_341_; 
v_toApplicative_334_ = lean_ctor_get(v_inst_331_, 0);
v_array_335_ = lean_ctor_get(v_as_333_, 0);
lean_inc_ref(v_array_335_);
v_start_336_ = lean_ctor_get(v_as_333_, 1);
lean_inc(v_start_336_);
v_stop_337_ = lean_ctor_get(v_as_333_, 2);
lean_inc(v_stop_337_);
lean_dec_ref(v_as_333_);
v_toBind_338_ = lean_ctor_get(v_inst_331_, 1);
lean_inc(v_toBind_338_);
v_toPure_339_ = lean_ctor_get(v_toApplicative_334_, 1);
lean_inc(v_toPure_339_);
v___f_340_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_340_, 0, v_toPure_339_);
v___x_341_ = lean_nat_dec_lt(v_start_336_, v_stop_337_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_inc(v_toPure_339_);
lean_dec(v_stop_337_);
lean_dec(v_start_336_);
lean_dec_ref(v_array_335_);
lean_dec(v_p_332_);
lean_dec_ref(v_inst_331_);
v___x_342_ = lean_box(v___x_341_);
v___x_343_ = lean_apply_2(v_toPure_339_, lean_box(0), v___x_342_);
v___x_344_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_343_, v___f_340_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___y_349_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_345_ = lean_box(v___x_341_);
lean_inc(v_toPure_339_);
v___f_346_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_346_, 0, v_toPure_339_);
lean_closure_set(v___f_346_, 1, v___x_345_);
lean_inc(v_toBind_338_);
v___f_347_ = lean_alloc_closure((void*)(l_Subarray_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_347_, 0, v_p_332_);
lean_closure_set(v___f_347_, 1, v_toBind_338_);
lean_closure_set(v___f_347_, 2, v___f_346_);
v___x_358_ = lean_array_get_size(v_array_335_);
v___x_359_ = lean_nat_dec_le(v_stop_337_, v___x_358_);
if (v___x_359_ == 0)
{
lean_dec(v_stop_337_);
v___y_349_ = v___x_358_;
goto v___jp_348_;
}
else
{
v___y_349_ = v_stop_337_;
goto v___jp_348_;
}
v___jp_348_:
{
uint8_t v___x_350_; 
v___x_350_ = lean_nat_dec_lt(v_start_336_, v___y_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
lean_inc(v_toPure_339_);
lean_dec(v___y_349_);
lean_dec_ref(v___f_347_);
lean_dec(v_start_336_);
lean_dec_ref(v_array_335_);
lean_dec_ref(v_inst_331_);
v___x_351_ = lean_box(v___x_350_);
v___x_352_ = lean_apply_2(v_toPure_339_, lean_box(0), v___x_351_);
v___x_353_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_352_, v___f_340_);
return v___x_353_;
}
else
{
size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_usize_of_nat(v_start_336_);
lean_dec(v_start_336_);
v___x_355_ = lean_usize_of_nat(v___y_349_);
lean_dec(v___y_349_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_331_, v___f_347_, v_array_335_, v___x_354_, v___x_355_);
v___x_357_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_356_, v___f_340_);
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg___lam__0(lean_object* v_f_360_, lean_object* v_x_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_apply_1(v_f_360_, v___y_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forM___redArg(lean_object* v_inst_364_, lean_object* v_f_365_, lean_object* v_as_366_){
_start:
{
lean_object* v_toApplicative_367_; lean_object* v_array_368_; lean_object* v_start_369_; lean_object* v_stop_370_; lean_object* v_toPure_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_toApplicative_367_ = lean_ctor_get(v_inst_364_, 0);
v_array_368_ = lean_ctor_get(v_as_366_, 0);
lean_inc_ref(v_array_368_);
v_start_369_ = lean_ctor_get(v_as_366_, 1);
lean_inc(v_start_369_);
v_stop_370_ = lean_ctor_get(v_as_366_, 2);
lean_inc(v_stop_370_);
lean_dec_ref(v_as_366_);
v_toPure_371_ = lean_ctor_get(v_toApplicative_367_, 1);
v___x_372_ = lean_box(0);
v___x_373_ = lean_nat_dec_lt(v_start_369_, v_stop_370_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_inc(v_toPure_371_);
lean_dec(v_stop_370_);
lean_dec(v_start_369_);
lean_dec_ref(v_array_368_);
lean_dec(v_f_365_);
lean_dec_ref(v_inst_364_);
v___x_374_ = lean_apply_2(v_toPure_371_, lean_box(0), v___x_372_);
return v___x_374_;
}
else
{
lean_object* v___f_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___f_375_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_375_, 0, v_f_365_);
v___x_376_ = lean_array_get_size(v_array_368_);
v___x_377_ = lean_nat_dec_le(v_stop_370_, v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
lean_dec(v_stop_370_);
v___x_378_ = lean_nat_dec_lt(v_start_369_, v___x_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_inc(v_toPure_371_);
lean_dec_ref(v___f_375_);
lean_dec(v_start_369_);
lean_dec_ref(v_array_368_);
lean_dec_ref(v_inst_364_);
v___x_379_ = lean_apply_2(v_toPure_371_, lean_box(0), v___x_372_);
return v___x_379_;
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_usize_of_nat(v_start_369_);
lean_dec(v_start_369_);
v___x_381_ = lean_usize_of_nat(v___x_376_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_364_, v___f_375_, v_array_368_, v___x_380_, v___x_381_, v___x_372_);
return v___x_382_;
}
}
else
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_usize_of_nat(v_start_369_);
lean_dec(v_start_369_);
v___x_384_ = lean_usize_of_nat(v_stop_370_);
lean_dec(v_stop_370_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_364_, v___f_375_, v_array_368_, v___x_383_, v___x_384_, v___x_372_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forM(lean_object* v_00_u03b1_386_, lean_object* v_m_387_, lean_object* v_inst_388_, lean_object* v_f_389_, lean_object* v_as_390_){
_start:
{
lean_object* v_toApplicative_391_; lean_object* v_array_392_; lean_object* v_start_393_; lean_object* v_stop_394_; lean_object* v_toPure_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_toApplicative_391_ = lean_ctor_get(v_inst_388_, 0);
v_array_392_ = lean_ctor_get(v_as_390_, 0);
lean_inc_ref(v_array_392_);
v_start_393_ = lean_ctor_get(v_as_390_, 1);
lean_inc(v_start_393_);
v_stop_394_ = lean_ctor_get(v_as_390_, 2);
lean_inc(v_stop_394_);
lean_dec_ref(v_as_390_);
v_toPure_395_ = lean_ctor_get(v_toApplicative_391_, 1);
v___x_396_ = lean_box(0);
v___x_397_ = lean_nat_dec_lt(v_start_393_, v_stop_394_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_inc(v_toPure_395_);
lean_dec(v_stop_394_);
lean_dec(v_start_393_);
lean_dec_ref(v_array_392_);
lean_dec(v_f_389_);
lean_dec_ref(v_inst_388_);
v___x_398_ = lean_apply_2(v_toPure_395_, lean_box(0), v___x_396_);
return v___x_398_;
}
else
{
lean_object* v___f_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___f_399_ = lean_alloc_closure((void*)(l_Subarray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_399_, 0, v_f_389_);
v___x_400_ = lean_array_get_size(v_array_392_);
v___x_401_ = lean_nat_dec_le(v_stop_394_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; 
lean_dec(v_stop_394_);
v___x_402_ = lean_nat_dec_lt(v_start_393_, v___x_400_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
lean_inc(v_toPure_395_);
lean_dec_ref(v___f_399_);
lean_dec(v_start_393_);
lean_dec_ref(v_array_392_);
lean_dec_ref(v_inst_388_);
v___x_403_ = lean_apply_2(v_toPure_395_, lean_box(0), v___x_396_);
return v___x_403_;
}
else
{
size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_usize_of_nat(v_start_393_);
lean_dec(v_start_393_);
v___x_405_ = lean_usize_of_nat(v___x_400_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_388_, v___f_399_, v_array_392_, v___x_404_, v___x_405_, v___x_396_);
return v___x_406_;
}
}
else
{
size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_usize_of_nat(v_start_393_);
lean_dec(v_start_393_);
v___x_408_ = lean_usize_of_nat(v_stop_394_);
lean_dec(v_stop_394_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_388_, v___f_399_, v_array_392_, v___x_407_, v___x_408_, v___x_396_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg___lam__0(lean_object* v_f_410_, lean_object* v_a_411_, lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_apply_1(v_f_410_, v_a_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM___redArg(lean_object* v_inst_414_, lean_object* v_f_415_, lean_object* v_as_416_){
_start:
{
lean_object* v_toApplicative_417_; lean_object* v_array_418_; lean_object* v_start_419_; lean_object* v_stop_420_; lean_object* v_toPure_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_toApplicative_417_ = lean_ctor_get(v_inst_414_, 0);
v_array_418_ = lean_ctor_get(v_as_416_, 0);
lean_inc_ref(v_array_418_);
v_start_419_ = lean_ctor_get(v_as_416_, 1);
lean_inc(v_start_419_);
v_stop_420_ = lean_ctor_get(v_as_416_, 2);
lean_inc(v_stop_420_);
lean_dec_ref(v_as_416_);
v_toPure_421_ = lean_ctor_get(v_toApplicative_417_, 1);
v___f_422_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_422_, 0, v_f_415_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_array_get_size(v_array_418_);
v___x_425_ = lean_nat_dec_le(v_stop_420_, v___x_424_);
if (v___x_425_ == 0)
{
uint8_t v___x_426_; 
lean_dec(v_stop_420_);
v___x_426_ = lean_nat_dec_lt(v_start_419_, v___x_424_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_inc(v_toPure_421_);
lean_dec_ref(v___f_422_);
lean_dec(v_start_419_);
lean_dec_ref(v_array_418_);
lean_dec_ref(v_inst_414_);
v___x_427_ = lean_apply_2(v_toPure_421_, lean_box(0), v___x_423_);
return v___x_427_;
}
else
{
size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_usize_of_nat(v___x_424_);
v___x_429_ = lean_usize_of_nat(v_start_419_);
lean_dec(v_start_419_);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_414_, v___f_422_, v_array_418_, v___x_428_, v___x_429_, v___x_423_);
return v___x_430_;
}
}
else
{
uint8_t v___x_431_; 
v___x_431_ = lean_nat_dec_lt(v_start_419_, v_stop_420_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_inc(v_toPure_421_);
lean_dec_ref(v___f_422_);
lean_dec(v_stop_420_);
lean_dec(v_start_419_);
lean_dec_ref(v_array_418_);
lean_dec_ref(v_inst_414_);
v___x_432_ = lean_apply_2(v_toPure_421_, lean_box(0), v___x_423_);
return v___x_432_;
}
else
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_usize_of_nat(v_stop_420_);
lean_dec(v_stop_420_);
v___x_434_ = lean_usize_of_nat(v_start_419_);
lean_dec(v_start_419_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_414_, v___f_422_, v_array_418_, v___x_433_, v___x_434_, v___x_423_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forRevM(lean_object* v_00_u03b1_436_, lean_object* v_m_437_, lean_object* v_inst_438_, lean_object* v_f_439_, lean_object* v_as_440_){
_start:
{
lean_object* v_toApplicative_441_; lean_object* v_array_442_; lean_object* v_start_443_; lean_object* v_stop_444_; lean_object* v_toPure_445_; lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_toApplicative_441_ = lean_ctor_get(v_inst_438_, 0);
v_array_442_ = lean_ctor_get(v_as_440_, 0);
lean_inc_ref(v_array_442_);
v_start_443_ = lean_ctor_get(v_as_440_, 1);
lean_inc(v_start_443_);
v_stop_444_ = lean_ctor_get(v_as_440_, 2);
lean_inc(v_stop_444_);
lean_dec_ref(v_as_440_);
v_toPure_445_ = lean_ctor_get(v_toApplicative_441_, 1);
v___f_446_ = lean_alloc_closure((void*)(l_Subarray_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_446_, 0, v_f_439_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_array_get_size(v_array_442_);
v___x_449_ = lean_nat_dec_le(v_stop_444_, v___x_448_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
lean_dec(v_stop_444_);
v___x_450_ = lean_nat_dec_lt(v_start_443_, v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_inc(v_toPure_445_);
lean_dec_ref(v___f_446_);
lean_dec(v_start_443_);
lean_dec_ref(v_array_442_);
lean_dec_ref(v_inst_438_);
v___x_451_ = lean_apply_2(v_toPure_445_, lean_box(0), v___x_447_);
return v___x_451_;
}
else
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_usize_of_nat(v___x_448_);
v___x_453_ = lean_usize_of_nat(v_start_443_);
lean_dec(v_start_443_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_438_, v___f_446_, v_array_442_, v___x_452_, v___x_453_, v___x_447_);
return v___x_454_;
}
}
else
{
uint8_t v___x_455_; 
v___x_455_ = lean_nat_dec_lt(v_start_443_, v_stop_444_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_inc(v_toPure_445_);
lean_dec_ref(v___f_446_);
lean_dec(v_stop_444_);
lean_dec(v_start_443_);
lean_dec_ref(v_array_442_);
lean_dec_ref(v_inst_438_);
v___x_456_ = lean_apply_2(v_toPure_445_, lean_box(0), v___x_447_);
return v___x_456_;
}
else
{
size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_usize_of_nat(v_stop_444_);
lean_dec(v_stop_444_);
v___x_458_ = lean_usize_of_nat(v_start_443_);
lean_dec(v_start_443_);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_438_, v___f_446_, v_array_442_, v___x_457_, v___x_458_, v___x_447_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg___lam__0(lean_object* v_f_460_, lean_object* v_x1_461_, lean_object* v_x2_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_apply_2(v_f_460_, v_x1_461_, v_x2_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr___redArg(lean_object* v_f_483_, lean_object* v_init_484_, lean_object* v_as_485_){
_start:
{
lean_object* v___x_486_; lean_object* v_array_487_; lean_object* v_start_488_; lean_object* v_stop_489_; lean_object* v___f_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_486_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_487_ = lean_ctor_get(v_as_485_, 0);
lean_inc_ref(v_array_487_);
v_start_488_ = lean_ctor_get(v_as_485_, 1);
lean_inc(v_start_488_);
v_stop_489_ = lean_ctor_get(v_as_485_, 2);
lean_inc(v_stop_489_);
lean_dec_ref(v_as_485_);
v___f_490_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_490_, 0, v_f_483_);
v___x_491_ = lean_array_get_size(v_array_487_);
v___x_492_ = lean_nat_dec_le(v_stop_489_, v___x_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
lean_dec(v_stop_489_);
v___x_493_ = lean_nat_dec_lt(v_start_488_, v___x_491_);
if (v___x_493_ == 0)
{
lean_dec_ref(v___f_490_);
lean_dec(v_start_488_);
lean_dec_ref(v_array_487_);
return v_init_484_;
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_usize_of_nat(v___x_491_);
v___x_495_ = lean_usize_of_nat(v_start_488_);
lean_dec(v_start_488_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_486_, v___f_490_, v_array_487_, v___x_494_, v___x_495_, v_init_484_);
return v___x_496_;
}
}
else
{
uint8_t v___x_497_; 
v___x_497_ = lean_nat_dec_lt(v_start_488_, v_stop_489_);
if (v___x_497_ == 0)
{
lean_dec_ref(v___f_490_);
lean_dec(v_stop_489_);
lean_dec(v_start_488_);
lean_dec_ref(v_array_487_);
return v_init_484_;
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_usize_of_nat(v_stop_489_);
lean_dec(v_stop_489_);
v___x_499_ = lean_usize_of_nat(v_start_488_);
lean_dec(v_start_488_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_486_, v___f_490_, v_array_487_, v___x_498_, v___x_499_, v_init_484_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldr(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_f_503_, lean_object* v_init_504_, lean_object* v_as_505_){
_start:
{
lean_object* v___x_506_; lean_object* v_array_507_; lean_object* v_start_508_; lean_object* v_stop_509_; lean_object* v___f_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_506_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_507_ = lean_ctor_get(v_as_505_, 0);
lean_inc_ref(v_array_507_);
v_start_508_ = lean_ctor_get(v_as_505_, 1);
lean_inc(v_start_508_);
v_stop_509_ = lean_ctor_get(v_as_505_, 2);
lean_inc(v_stop_509_);
lean_dec_ref(v_as_505_);
v___f_510_ = lean_alloc_closure((void*)(l_Subarray_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_510_, 0, v_f_503_);
v___x_511_ = lean_array_get_size(v_array_507_);
v___x_512_ = lean_nat_dec_le(v_stop_509_, v___x_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
lean_dec(v_stop_509_);
v___x_513_ = lean_nat_dec_lt(v_start_508_, v___x_511_);
if (v___x_513_ == 0)
{
lean_dec_ref(v___f_510_);
lean_dec(v_start_508_);
lean_dec_ref(v_array_507_);
return v_init_504_;
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_usize_of_nat(v___x_511_);
v___x_515_ = lean_usize_of_nat(v_start_508_);
lean_dec(v_start_508_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_506_, v___f_510_, v_array_507_, v___x_514_, v___x_515_, v_init_504_);
return v___x_516_;
}
}
else
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v_start_508_, v_stop_509_);
if (v___x_517_ == 0)
{
lean_dec_ref(v___f_510_);
lean_dec(v_stop_509_);
lean_dec(v_start_508_);
lean_dec_ref(v_array_507_);
return v_init_504_;
}
else
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_usize_of_nat(v_stop_509_);
lean_dec(v_stop_509_);
v___x_519_ = lean_usize_of_nat(v_start_508_);
lean_dec(v_start_508_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_506_, v___f_510_, v_array_507_, v___x_518_, v___x_519_, v_init_504_);
return v___x_520_;
}
}
}
}
uint8_t l_Subarray_any___redArg___lam__0(lean_object* v_p_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_apply_1(v_p_521_, v_x_522_);
v___x_524_ = lean_unbox(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT void l_Subarray_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_521_ = stack[0].m_obj;
lean_object* v_x_522_ = stack[1].m_obj;
uint8_t v_res_525_;
v_res_525_ = l_Subarray_any___redArg___lam__0(v_p_521_, v_x_522_);
stack->m_num = v_res_525_;
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___lam__0___boxed(lean_object* v_p_526_, lean_object* v_x_527_){
_start:
{
uint8_t v_res_528_; lean_object* v_r_529_; 
v_res_528_ = l_Subarray_any___redArg___lam__0(v_p_526_, v_x_527_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
uint8_t l_Subarray_any___redArg(lean_object* v_p_530_, lean_object* v_as_531_){
_start:
{
lean_object* v___x_532_; lean_object* v_array_533_; lean_object* v_start_534_; lean_object* v_stop_535_; uint8_t v___x_536_; 
v___x_532_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_533_ = lean_ctor_get(v_as_531_, 0);
lean_inc_ref(v_array_533_);
v_start_534_ = lean_ctor_get(v_as_531_, 1);
lean_inc(v_start_534_);
v_stop_535_ = lean_ctor_get(v_as_531_, 2);
lean_inc(v_stop_535_);
lean_dec_ref(v_as_531_);
v___x_536_ = lean_nat_dec_lt(v_start_534_, v_stop_535_);
if (v___x_536_ == 0)
{
lean_dec(v_stop_535_);
lean_dec(v_start_534_);
lean_dec_ref(v_array_533_);
lean_dec_ref(v_p_530_);
return v___x_536_;
}
else
{
lean_object* v___f_537_; lean_object* v___y_539_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___f_537_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_537_, 0, v_p_530_);
v___x_545_ = lean_array_get_size(v_array_533_);
v___x_546_ = lean_nat_dec_le(v_stop_535_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v_stop_535_);
v___y_539_ = v___x_545_;
goto v___jp_538_;
}
else
{
v___y_539_ = v_stop_535_;
goto v___jp_538_;
}
v___jp_538_:
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_lt(v_start_534_, v___y_539_);
if (v___x_540_ == 0)
{
lean_dec(v___y_539_);
lean_dec_ref(v___f_537_);
lean_dec(v_start_534_);
lean_dec_ref(v_array_533_);
return v___x_540_;
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_541_ = lean_usize_of_nat(v_start_534_);
lean_dec(v_start_534_);
v___x_542_ = lean_usize_of_nat(v___y_539_);
lean_dec(v___y_539_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_532_, v___f_537_, v_array_533_, v___x_541_, v___x_542_);
v___x_544_ = lean_unbox(v___x_543_);
lean_dec(v___x_543_);
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT void l_Subarray_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_530_ = stack[0].m_obj;
lean_object* v_as_531_ = stack[1].m_obj;
uint8_t v_res_547_;
v_res_547_ = l_Subarray_any___redArg(v_p_530_, v_as_531_);
stack->m_num = v_res_547_;
}
LEAN_EXPORT lean_object* l_Subarray_any___redArg___boxed(lean_object* v_p_548_, lean_object* v_as_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Subarray_any___redArg(v_p_548_, v_as_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
uint8_t l_Subarray_any(lean_object* v_00_u03b1_552_, lean_object* v_p_553_, lean_object* v_as_554_){
_start:
{
lean_object* v___x_555_; lean_object* v_array_556_; lean_object* v_start_557_; lean_object* v_stop_558_; uint8_t v___x_559_; 
v___x_555_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_556_ = lean_ctor_get(v_as_554_, 0);
lean_inc_ref(v_array_556_);
v_start_557_ = lean_ctor_get(v_as_554_, 1);
lean_inc(v_start_557_);
v_stop_558_ = lean_ctor_get(v_as_554_, 2);
lean_inc(v_stop_558_);
lean_dec_ref(v_as_554_);
v___x_559_ = lean_nat_dec_lt(v_start_557_, v_stop_558_);
if (v___x_559_ == 0)
{
lean_dec(v_stop_558_);
lean_dec(v_start_557_);
lean_dec_ref(v_array_556_);
lean_dec_ref(v_p_553_);
return v___x_559_;
}
else
{
lean_object* v___f_560_; lean_object* v___y_562_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___f_560_ = lean_alloc_closure((void*)(l_Subarray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_560_, 0, v_p_553_);
v___x_568_ = lean_array_get_size(v_array_556_);
v___x_569_ = lean_nat_dec_le(v_stop_558_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v_stop_558_);
v___y_562_ = v___x_568_;
goto v___jp_561_;
}
else
{
v___y_562_ = v_stop_558_;
goto v___jp_561_;
}
v___jp_561_:
{
uint8_t v___x_563_; 
v___x_563_ = lean_nat_dec_lt(v_start_557_, v___y_562_);
if (v___x_563_ == 0)
{
lean_dec(v___y_562_);
lean_dec_ref(v___f_560_);
lean_dec(v_start_557_);
lean_dec_ref(v_array_556_);
return v___x_563_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_564_ = lean_usize_of_nat(v_start_557_);
lean_dec(v_start_557_);
v___x_565_ = lean_usize_of_nat(v___y_562_);
lean_dec(v___y_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_555_, v___f_560_, v_array_556_, v___x_564_, v___x_565_);
v___x_567_ = lean_unbox(v___x_566_);
lean_dec(v___x_566_);
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT void l_Subarray_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_553_ = stack[1].m_obj;
lean_object* v_as_554_ = stack[2].m_obj;
uint8_t v_res_570_;
v_res_570_ = l_Subarray_any(lean_box(0), v_p_553_, v_as_554_);
stack->m_num = v_res_570_;
}
LEAN_EXPORT lean_object* l_Subarray_any___boxed(lean_object* v_00_u03b1_571_, lean_object* v_p_572_, lean_object* v_as_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Subarray_any(v_00_u03b1_571_, v_p_572_, v_as_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
uint8_t l_Subarray_all___redArg___lam__0(lean_object* v_p_576_, uint8_t v___x_577_, lean_object* v_v_578_){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_apply_1(v_p_576_, v_v_578_);
v___x_580_ = lean_unbox(v___x_579_);
if (v___x_580_ == 0)
{
return v___x_577_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = 0;
return v___x_581_;
}
}
}
LEAN_EXPORT void l_Subarray_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_576_ = stack[0].m_obj;
uint8_t v___x_577_ = stack[1].m_num;
lean_object* v_v_578_ = stack[2].m_obj;
uint8_t v_res_582_;
v_res_582_ = l_Subarray_all___redArg___lam__0(v_p_576_, v___x_577_, v_v_578_);
stack->m_num = v_res_582_;
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___lam__0___boxed(lean_object* v_p_583_, lean_object* v___x_584_, lean_object* v_v_585_){
_start:
{
uint8_t v___x_337__boxed_586_; uint8_t v_res_587_; lean_object* v_r_588_; 
v___x_337__boxed_586_ = lean_unbox(v___x_584_);
v_res_587_ = l_Subarray_all___redArg___lam__0(v_p_583_, v___x_337__boxed_586_, v_v_585_);
v_r_588_ = lean_box(v_res_587_);
return v_r_588_;
}
}
uint8_t l_Subarray_all___redArg(lean_object* v_p_589_, lean_object* v_as_590_){
_start:
{
lean_object* v___x_591_; lean_object* v_array_592_; lean_object* v_start_593_; lean_object* v_stop_594_; uint8_t v___x_595_; 
v___x_591_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_592_ = lean_ctor_get(v_as_590_, 0);
lean_inc_ref(v_array_592_);
v_start_593_ = lean_ctor_get(v_as_590_, 1);
lean_inc(v_start_593_);
v_stop_594_ = lean_ctor_get(v_as_590_, 2);
lean_inc(v_stop_594_);
lean_dec_ref(v_as_590_);
v___x_595_ = lean_nat_dec_lt(v_start_593_, v_stop_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
lean_dec(v_stop_594_);
lean_dec(v_start_593_);
lean_dec_ref(v_array_592_);
lean_dec_ref(v_p_589_);
v___x_596_ = 1;
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___y_600_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_597_ = lean_box(v___x_595_);
v___f_598_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_598_, 0, v_p_589_);
lean_closure_set(v___f_598_, 1, v___x_597_);
v___x_607_ = lean_array_get_size(v_array_592_);
v___x_608_ = lean_nat_dec_le(v_stop_594_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_stop_594_);
v___y_600_ = v___x_607_;
goto v___jp_599_;
}
else
{
v___y_600_ = v_stop_594_;
goto v___jp_599_;
}
v___jp_599_:
{
uint8_t v___x_601_; 
v___x_601_ = lean_nat_dec_lt(v_start_593_, v___y_600_);
if (v___x_601_ == 0)
{
lean_dec(v___y_600_);
lean_dec_ref(v___f_598_);
lean_dec(v_start_593_);
lean_dec_ref(v_array_592_);
return v___x_595_;
}
else
{
size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_602_ = lean_usize_of_nat(v_start_593_);
lean_dec(v_start_593_);
v___x_603_ = lean_usize_of_nat(v___y_600_);
lean_dec(v___y_600_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_591_, v___f_598_, v_array_592_, v___x_602_, v___x_603_);
v___x_605_ = lean_unbox(v___x_604_);
lean_dec(v___x_604_);
if (v___x_605_ == 0)
{
return v___x_601_;
}
else
{
uint8_t v___x_606_; 
v___x_606_ = 0;
return v___x_606_;
}
}
}
}
}
}
LEAN_EXPORT void l_Subarray_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_589_ = stack[0].m_obj;
lean_object* v_as_590_ = stack[1].m_obj;
uint8_t v_res_609_;
v_res_609_ = l_Subarray_all___redArg(v_p_589_, v_as_590_);
stack->m_num = v_res_609_;
}
LEAN_EXPORT lean_object* l_Subarray_all___redArg___boxed(lean_object* v_p_610_, lean_object* v_as_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Subarray_all___redArg(v_p_610_, v_as_611_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
uint8_t l_Subarray_all(lean_object* v_00_u03b1_614_, lean_object* v_p_615_, lean_object* v_as_616_){
_start:
{
lean_object* v___x_617_; lean_object* v_array_618_; lean_object* v_start_619_; lean_object* v_stop_620_; uint8_t v___x_621_; 
v___x_617_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_array_618_ = lean_ctor_get(v_as_616_, 0);
lean_inc_ref(v_array_618_);
v_start_619_ = lean_ctor_get(v_as_616_, 1);
lean_inc(v_start_619_);
v_stop_620_ = lean_ctor_get(v_as_616_, 2);
lean_inc(v_stop_620_);
lean_dec_ref(v_as_616_);
v___x_621_ = lean_nat_dec_lt(v_start_619_, v_stop_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
lean_dec(v_stop_620_);
lean_dec(v_start_619_);
lean_dec_ref(v_array_618_);
lean_dec_ref(v_p_615_);
v___x_622_ = 1;
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___f_624_; lean_object* v___y_626_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_623_ = lean_box(v___x_621_);
v___f_624_ = lean_alloc_closure((void*)(l_Subarray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_624_, 0, v_p_615_);
lean_closure_set(v___f_624_, 1, v___x_623_);
v___x_633_ = lean_array_get_size(v_array_618_);
v___x_634_ = lean_nat_dec_le(v_stop_620_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec(v_stop_620_);
v___y_626_ = v___x_633_;
goto v___jp_625_;
}
else
{
v___y_626_ = v_stop_620_;
goto v___jp_625_;
}
v___jp_625_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_lt(v_start_619_, v___y_626_);
if (v___x_627_ == 0)
{
lean_dec(v___y_626_);
lean_dec_ref(v___f_624_);
lean_dec(v_start_619_);
lean_dec_ref(v_array_618_);
return v___x_621_;
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_628_ = lean_usize_of_nat(v_start_619_);
lean_dec(v_start_619_);
v___x_629_ = lean_usize_of_nat(v___y_626_);
lean_dec(v___y_626_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_617_, v___f_624_, v_array_618_, v___x_628_, v___x_629_);
v___x_631_ = lean_unbox(v___x_630_);
lean_dec(v___x_630_);
if (v___x_631_ == 0)
{
return v___x_627_;
}
else
{
uint8_t v___x_632_; 
v___x_632_ = 0;
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT void l_Subarray_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_615_ = stack[1].m_obj;
lean_object* v_as_616_ = stack[2].m_obj;
uint8_t v_res_635_;
v_res_635_ = l_Subarray_all(lean_box(0), v_p_615_, v_as_616_);
stack->m_num = v_res_635_;
}
LEAN_EXPORT lean_object* l_Subarray_all___boxed(lean_object* v_00_u03b1_636_, lean_object* v_p_637_, lean_object* v_as_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Subarray_all(v_00_u03b1_636_, v_p_637_, v_as_638_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_641_, lean_object* v_as_642_, lean_object* v_f_643_, lean_object* v_n_644_, lean_object* v_toPure_645_, lean_object* v_r_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(v_inst_641_, v_as_642_, v_f_643_, v_n_644_, v_toPure_645_, v_r_646_);
lean_dec(v_n_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(lean_object* v_inst_648_, lean_object* v_as_649_, lean_object* v_f_650_, lean_object* v_i_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_toBind_653_; lean_object* v_toPure_654_; lean_object* v_zero_655_; uint8_t v_isZero_656_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_648_, 0);
v_toBind_653_ = lean_ctor_get(v_inst_648_, 1);
lean_inc(v_toBind_653_);
v_toPure_654_ = lean_ctor_get(v_toApplicative_652_, 1);
lean_inc(v_toPure_654_);
v_zero_655_ = lean_unsigned_to_nat(0u);
v_isZero_656_ = lean_nat_dec_eq(v_i_651_, v_zero_655_);
if (v_isZero_656_ == 1)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v_toBind_653_);
lean_dec(v_f_650_);
lean_dec_ref(v_as_649_);
lean_dec_ref(v_inst_648_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_apply_2(v_toPure_654_, lean_box(0), v___x_657_);
return v___x_658_;
}
else
{
lean_object* v_one_659_; lean_object* v_n_660_; lean_object* v___f_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_one_659_ = lean_unsigned_to_nat(1u);
v_n_660_ = lean_nat_sub(v_i_651_, v_one_659_);
lean_inc(v_n_660_);
lean_inc(v_f_650_);
lean_inc_ref(v_as_649_);
v___f_661_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_661_, 0, v_inst_648_);
lean_closure_set(v___f_661_, 1, v_as_649_);
lean_closure_set(v___f_661_, 2, v_f_650_);
lean_closure_set(v___f_661_, 3, v_n_660_);
lean_closure_set(v___f_661_, 4, v_toPure_654_);
v___x_662_ = l_Subarray_get___redArg(v_as_649_, v_n_660_);
lean_dec(v_n_660_);
lean_dec_ref(v_as_649_);
v___x_663_ = lean_apply_1(v_f_650_, v___x_662_);
v___x_664_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_663_, v___f_661_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_665_, lean_object* v_as_666_, lean_object* v_f_667_, lean_object* v_n_668_, lean_object* v_toPure_669_, lean_object* v_r_670_){
_start:
{
if (lean_obj_tag(v_r_670_) == 0)
{
lean_object* v___x_671_; 
lean_dec(v_toPure_669_);
v___x_671_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_665_, v_as_666_, v_f_667_, v_n_668_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
lean_dec(v_f_667_);
lean_dec_ref(v_as_666_);
lean_dec_ref(v_inst_665_);
v___x_672_ = lean_apply_2(v_toPure_669_, lean_box(0), v_r_670_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_673_, lean_object* v_as_674_, lean_object* v_f_675_, lean_object* v_i_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_673_, v_as_674_, v_f_675_, v_i_676_);
lean_dec(v_i_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_m_680_, lean_object* v_inst_681_, lean_object* v_as_682_, lean_object* v_f_683_, lean_object* v_i_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_681_, v_as_682_, v_f_683_, v_i_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_m_689_, lean_object* v_inst_690_, lean_object* v_as_691_, lean_object* v_f_692_, lean_object* v_i_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(v_00_u03b1_687_, v_00_u03b2_688_, v_m_689_, v_inst_690_, v_as_691_, v_f_692_, v_i_693_, v_a_694_);
lean_dec(v_i_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f___redArg(lean_object* v_inst_696_, lean_object* v_as_697_, lean_object* v_f_698_){
_start:
{
lean_object* v_start_699_; lean_object* v_stop_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_start_699_ = lean_ctor_get(v_as_697_, 1);
v_stop_700_ = lean_ctor_get(v_as_697_, 2);
v___x_701_ = lean_nat_sub(v_stop_700_, v_start_699_);
v___x_702_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_696_, v_as_697_, v_f_698_, v___x_701_);
lean_dec(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_m_705_, lean_object* v_inst_706_, lean_object* v_as_707_, lean_object* v_f_708_){
_start:
{
lean_object* v_start_709_; lean_object* v_stop_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_start_709_ = lean_ctor_get(v_as_707_, 1);
v_stop_710_ = lean_ctor_get(v_as_707_, 2);
v___x_711_ = lean_nat_sub(v_stop_710_, v_start_709_);
v___x_712_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_706_, v_as_707_, v_f_708_, v___x_711_);
lean_dec(v___x_711_);
return v___x_712_;
}
}
lean_object* l_Subarray_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_713_, lean_object* v_a_714_, uint8_t v_____do__lift_715_){
_start:
{
if (v_____do__lift_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_a_714_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_apply_2(v_toPure_713_, lean_box(0), v___x_716_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v_a_714_);
v___x_719_ = lean_apply_2(v_toPure_713_, lean_box(0), v___x_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT void l_Subarray_findRevM_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_713_ = stack[0].m_obj;
lean_object* v_a_714_ = stack[1].m_obj;
uint8_t v_____do__lift_715_ = stack[2].m_num;
lean_object* v_res_720_;
v_res_720_ = l_Subarray_findRevM_x3f___redArg___lam__0(v_toPure_713_, v_a_714_, v_____do__lift_715_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_721_, lean_object* v_a_722_, lean_object* v_____do__lift_723_){
_start:
{
uint8_t v_____do__lift_63__boxed_724_; lean_object* v_res_725_; 
v_____do__lift_63__boxed_724_ = lean_unbox(v_____do__lift_723_);
v_res_725_ = l_Subarray_findRevM_x3f___redArg___lam__0(v_toPure_721_, v_a_722_, v_____do__lift_63__boxed_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_726_, lean_object* v_p_727_, lean_object* v_toBind_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_inc(v_a_729_);
v___f_730_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_730_, 0, v_toPure_726_);
lean_closure_set(v___f_730_, 1, v_a_729_);
v___x_731_ = lean_apply_1(v_p_727_, v_a_729_);
v___x_732_ = lean_apply_4(v_toBind_728_, lean_box(0), lean_box(0), v___x_731_, v___f_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f___redArg(lean_object* v_inst_733_, lean_object* v_as_734_, lean_object* v_p_735_){
_start:
{
lean_object* v_toApplicative_736_; lean_object* v_toBind_737_; lean_object* v_toPure_738_; lean_object* v_start_739_; lean_object* v_stop_740_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_toApplicative_736_ = lean_ctor_get(v_inst_733_, 0);
v_toBind_737_ = lean_ctor_get(v_inst_733_, 1);
v_toPure_738_ = lean_ctor_get(v_toApplicative_736_, 1);
v_start_739_ = lean_ctor_get(v_as_734_, 1);
v_stop_740_ = lean_ctor_get(v_as_734_, 2);
lean_inc(v_toBind_737_);
lean_inc(v_toPure_738_);
v___f_741_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_741_, 0, v_toPure_738_);
lean_closure_set(v___f_741_, 1, v_p_735_);
lean_closure_set(v___f_741_, 2, v_toBind_737_);
v___x_742_ = lean_nat_sub(v_stop_740_, v_start_739_);
v___x_743_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_733_, v_as_734_, v___f_741_, v___x_742_);
lean_dec(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRevM_x3f(lean_object* v_00_u03b1_744_, lean_object* v_m_745_, lean_object* v_inst_746_, lean_object* v_as_747_, lean_object* v_p_748_){
_start:
{
lean_object* v_toApplicative_749_; lean_object* v_toBind_750_; lean_object* v_toPure_751_; lean_object* v_start_752_; lean_object* v_stop_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_toApplicative_749_ = lean_ctor_get(v_inst_746_, 0);
v_toBind_750_ = lean_ctor_get(v_inst_746_, 1);
v_toPure_751_ = lean_ctor_get(v_toApplicative_749_, 1);
v_start_752_ = lean_ctor_get(v_as_747_, 1);
v_stop_753_ = lean_ctor_get(v_as_747_, 2);
lean_inc(v_toBind_750_);
lean_inc(v_toPure_751_);
v___f_754_ = lean_alloc_closure((void*)(l_Subarray_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_754_, 0, v_toPure_751_);
lean_closure_set(v___f_754_, 1, v_p_748_);
lean_closure_set(v___f_754_, 2, v_toBind_750_);
v___x_755_ = lean_nat_sub(v_stop_753_, v_start_752_);
v___x_756_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v_inst_746_, v_as_747_, v___f_754_, v___x_755_);
lean_dec(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg___lam__0(lean_object* v_p_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
lean_inc(v_a_758_);
v___x_759_ = lean_apply_1(v_p_757_, v_a_758_);
v___x_760_ = lean_unbox(v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v_a_758_);
v___x_761_ = lean_box(0);
return v___x_761_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_a_758_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f___redArg(lean_object* v_as_763_, lean_object* v_p_764_){
_start:
{
lean_object* v___x_765_; lean_object* v_start_766_; lean_object* v_stop_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_765_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_766_ = lean_ctor_get(v_as_763_, 1);
v_stop_767_ = lean_ctor_get(v_as_763_, 2);
v___f_768_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_768_, 0, v_p_764_);
v___x_769_ = lean_nat_sub(v_stop_767_, v_start_766_);
v___x_770_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_765_, v_as_763_, v___f_768_, v___x_769_);
lean_dec(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Subarray_findRev_x3f(lean_object* v_00_u03b1_771_, lean_object* v_as_772_, lean_object* v_p_773_){
_start:
{
lean_object* v___x_774_; lean_object* v_start_775_; lean_object* v_stop_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = ((lean_object*)(l_Subarray_foldr___redArg___closed__9));
v_start_775_ = lean_ctor_get(v_as_772_, 1);
v_stop_776_ = lean_ctor_get(v_as_772_, 2);
v___f_777_ = lean_alloc_closure((void*)(l_Subarray_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_777_, 0, v_p_773_);
v___x_778_ = lean_nat_sub(v_stop_776_, v_start_775_);
v___x_779_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(v___x_774_, v_as_772_, v___f_777_, v___x_778_);
lean_dec(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray___redArg(lean_object* v_as_780_, lean_object* v_start_781_, lean_object* v_stop_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_as_780_);
v___x_784_ = lean_nat_dec_le(v_stop_782_, v___x_783_);
if (v___x_784_ == 0)
{
uint8_t v___x_785_; 
lean_dec(v_stop_782_);
v___x_785_ = lean_nat_dec_le(v_start_781_, v___x_783_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec(v_start_781_);
v___x_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_786_, 0, v_as_780_);
lean_ctor_set(v___x_786_, 1, v___x_783_);
lean_ctor_set(v___x_786_, 2, v___x_783_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_787_, 0, v_as_780_);
lean_ctor_set(v___x_787_, 1, v_start_781_);
lean_ctor_set(v___x_787_, 2, v___x_783_);
return v___x_787_;
}
}
else
{
uint8_t v___x_788_; 
v___x_788_ = lean_nat_dec_le(v_start_781_, v_stop_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v_start_781_);
lean_inc(v_stop_782_);
v___x_789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_789_, 0, v_as_780_);
lean_ctor_set(v___x_789_, 1, v_stop_782_);
lean_ctor_set(v___x_789_, 2, v_stop_782_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_790_, 0, v_as_780_);
lean_ctor_set(v___x_790_, 1, v_start_781_);
lean_ctor_set(v___x_790_, 2, v_stop_782_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toSubarray(lean_object* v_00_u03b1_791_, lean_object* v_as_792_, lean_object* v_start_793_, lean_object* v_stop_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Array_toSubarray___redArg(v_as_792_, v_start_793_, v_stop_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5));
v___x_913_ = l_String_toRawSubstring_x27(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(lean_object* v_x_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = ((lean_object*)(l_Array_term_____x5b___x3a___x5d___closed__2));
lean_inc(v_x_927_);
v___x_931_ = l_Lean_Syntax_isOfKind(v_x_927_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_x_927_);
v___x_932_ = lean_box(1);
v___x_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_a_929_);
return v___x_933_;
}
else
{
lean_object* v_quotContext_934_; lean_object* v_currMacroScope_935_; lean_object* v_ref_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_quotContext_934_ = lean_ctor_get(v_a_928_, 1);
v_currMacroScope_935_ = lean_ctor_get(v_a_928_, 2);
v_ref_936_ = lean_ctor_get(v_a_928_, 5);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = l_Lean_Syntax_getArg(v_x_927_, v___x_937_);
v___x_939_ = lean_unsigned_to_nat(2u);
v___x_940_ = l_Lean_Syntax_getArg(v_x_927_, v___x_939_);
v___x_941_ = lean_unsigned_to_nat(4u);
v___x_942_ = l_Lean_Syntax_getArg(v_x_927_, v___x_941_);
lean_dec(v_x_927_);
v___x_943_ = 0;
v___x_944_ = l_Lean_SourceInfo_fromRef(v_ref_936_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_946_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_947_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_935_);
lean_inc(v_quotContext_934_);
v___x_948_ = l_Lean_addMacroScope(v_quotContext_934_, v___x_947_, v_currMacroScope_935_);
v___x_949_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_944_, 2);
v___x_950_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_950_, 0, v___x_944_);
lean_ctor_set(v___x_950_, 1, v___x_946_);
lean_ctor_set(v___x_950_, 2, v___x_948_);
lean_ctor_set(v___x_950_, 3, v___x_949_);
v___x_951_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_952_ = l_Lean_Syntax_node3(v___x_944_, v___x_951_, v___x_938_, v___x_940_, v___x_942_);
v___x_953_ = l_Lean_Syntax_node2(v___x_944_, v___x_945_, v___x_950_, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v_a_929_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(lean_object* v_x_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(v_x_955_, v_a_956_, v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(lean_object* v_x_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = ((lean_object*)(l_Array_term_____x5b_x3a___x5d___closed__1));
lean_inc(v_x_963_);
v___x_967_ = l_Lean_Syntax_isOfKind(v_x_963_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_x_963_);
v___x_968_ = lean_box(1);
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_a_965_);
return v___x_969_;
}
else
{
lean_object* v_quotContext_970_; lean_object* v_currMacroScope_971_; lean_object* v_ref_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_quotContext_970_ = lean_ctor_get(v_a_964_, 1);
v_currMacroScope_971_ = lean_ctor_get(v_a_964_, 2);
v_ref_972_ = lean_ctor_get(v_a_964_, 5);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = l_Lean_Syntax_getArg(v_x_963_, v___x_973_);
v___x_975_ = lean_unsigned_to_nat(3u);
v___x_976_ = l_Lean_Syntax_getArg(v_x_963_, v___x_975_);
lean_dec(v_x_963_);
v___x_977_ = 0;
v___x_978_ = l_Lean_SourceInfo_fromRef(v_ref_972_, v___x_977_);
v___x_979_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_980_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_981_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
lean_inc(v_currMacroScope_971_);
lean_inc(v_quotContext_970_);
v___x_982_ = l_Lean_addMacroScope(v_quotContext_970_, v___x_981_, v_currMacroScope_971_);
v___x_983_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10));
lean_inc_n(v___x_978_, 4);
v___x_984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_984_, 0, v___x_978_);
lean_ctor_set(v___x_984_, 1, v___x_980_);
lean_ctor_set(v___x_984_, 2, v___x_982_);
lean_ctor_set(v___x_984_, 3, v___x_983_);
v___x_985_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_986_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1));
v___x_987_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2));
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_978_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_Syntax_node1(v___x_978_, v___x_986_, v___x_988_);
v___x_990_ = l_Lean_Syntax_node3(v___x_978_, v___x_985_, v___x_974_, v___x_989_, v___x_976_);
v___x_991_ = l_Lean_Syntax_node2(v___x_978_, v___x_979_, v___x_984_, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v_a_965_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(lean_object* v_x_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(v_x_993_, v_a_994_, v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_996_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Array_mkArray0___redArg();
return v___x_1009_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11));
v___x_1030_ = l_String_toRawSubstring_x27(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18));
v___x_1043_ = l_String_toRawSubstring_x27(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(lean_object* v_x_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Array_term_____x5b___x3a_x5d___closed__1));
lean_inc(v_x_1048_);
v___x_1052_ = l_Lean_Syntax_isOfKind(v_x_1048_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_x_1048_);
v___x_1053_ = lean_box(1);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_a_1050_);
return v___x_1054_;
}
else
{
lean_object* v_quotContext_1055_; lean_object* v_currMacroScope_1056_; lean_object* v_ref_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_quotContext_1055_ = lean_ctor_get(v_a_1049_, 1);
v_currMacroScope_1056_ = lean_ctor_get(v_a_1049_, 2);
v_ref_1057_ = lean_ctor_get(v_a_1049_, 5);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = l_Lean_Syntax_getArg(v_x_1048_, v___x_1058_);
v___x_1060_ = lean_unsigned_to_nat(2u);
v___x_1061_ = l_Lean_Syntax_getArg(v_x_1048_, v___x_1060_);
lean_dec(v_x_1048_);
v___x_1062_ = 0;
v___x_1063_ = l_Lean_SourceInfo_fromRef(v_ref_1057_, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0));
v___x_1065_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1));
lean_inc_n(v___x_1063_, 13);
v___x_1066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1064_);
v___x_1067_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3));
v___x_1068_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12));
v___x_1069_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
v___x_1070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1063_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_inc_ref_n(v___x_1070_, 2);
v___x_1071_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1067_, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6));
v___x_1073_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8));
v___x_1074_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10));
v___x_1075_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
v___x_1076_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13));
lean_inc_n(v_currMacroScope_1056_, 3);
lean_inc_n(v_quotContext_1055_, 3);
v___x_1077_ = l_Lean_addMacroScope(v_quotContext_1055_, v___x_1076_, v_currMacroScope_1056_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1063_);
lean_ctor_set(v___x_1079_, 1, v___x_1075_);
lean_ctor_set(v___x_1079_, 2, v___x_1077_);
lean_ctor_set(v___x_1079_, 3, v___x_1078_);
lean_inc_ref(v___x_1079_);
v___x_1080_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1074_, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14));
v___x_1082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1063_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_Syntax_node5(v___x_1063_, v___x_1073_, v___x_1080_, v___x_1070_, v___x_1070_, v___x_1082_, v___x_1059_);
v___x_1084_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1072_, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15));
v___x_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1063_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4));
v___x_1088_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
v___x_1089_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8));
v___x_1090_ = l_Lean_addMacroScope(v_quotContext_1055_, v___x_1089_, v_currMacroScope_1056_);
v___x_1091_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17));
v___x_1092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1063_);
lean_ctor_set(v___x_1092_, 1, v___x_1088_);
lean_ctor_set(v___x_1092_, 2, v___x_1090_);
lean_ctor_set(v___x_1092_, 3, v___x_1091_);
v___x_1093_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19, &l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once, _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
v___x_1094_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21));
v___x_1095_ = l_Lean_addMacroScope(v_quotContext_1055_, v___x_1094_, v_currMacroScope_1056_);
v___x_1096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1063_);
lean_ctor_set(v___x_1096_, 1, v___x_1093_);
lean_ctor_set(v___x_1096_, 2, v___x_1095_);
lean_ctor_set(v___x_1096_, 3, v___x_1078_);
v___x_1097_ = l_Lean_Syntax_node3(v___x_1063_, v___x_1068_, v___x_1079_, v___x_1061_, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1087_, v___x_1092_, v___x_1097_);
v___x_1099_ = l_Lean_Syntax_node5(v___x_1063_, v___x_1065_, v___x_1066_, v___x_1071_, v___x_1084_, v___x_1086_, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_a_1050_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(lean_object* v_x_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(v_x_1101_, v_a_1102_, v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1104_;
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
