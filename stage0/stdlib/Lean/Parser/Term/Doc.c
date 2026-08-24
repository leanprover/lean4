// Lean compiler output
// Module: Lean.Parser.Term.Doc
// Imports: public import Lean.Parser.Extension
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "recommendedSpellingByNameExt"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 37, 190, 246, 145, 148, 24, 135)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 208, 209, 98, 233, 154, 255, 115)}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "recommendedSpellingExt"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 37, 190, 246, 145, 148, 24, 135)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 98, 124, 104, 70, 9, 210, 178)}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_recommendedSpellingExt;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_addRecommendedSpelling(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "   "};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " * The recommended spelling of `"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` in identifiers is `"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ".\n\n"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3_value;
static const lean_array_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ").\n\n"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7_value;
static const lean_string_object l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8 = (const lean_object*)&l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n\nConventions for notations in identifiers:\n\n"};
static const lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0 = (const lean_object*)&l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_1_, lean_object* v_k_2_, lean_object* v_fallback_3_){
_start:
{
if (lean_obj_tag(v_t_1_) == 0)
{
lean_object* v_k_4_; lean_object* v_v_5_; lean_object* v_l_6_; lean_object* v_r_7_; uint8_t v___x_8_; 
v_k_4_ = lean_ctor_get(v_t_1_, 1);
v_v_5_ = lean_ctor_get(v_t_1_, 2);
v_l_6_ = lean_ctor_get(v_t_1_, 3);
v_r_7_ = lean_ctor_get(v_t_1_, 4);
v___x_8_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2_, v_k_4_);
switch(v___x_8_)
{
case 0:
{
v_t_1_ = v_l_6_;
goto _start;
}
case 1:
{
lean_inc(v_v_5_);
return v_v_5_;
}
default: 
{
v_t_1_ = v_r_7_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3_);
return v_fallback_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_11_, lean_object* v_k_12_, lean_object* v_fallback_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_11_, v_k_12_, v_fallback_13_);
lean_dec(v_fallback_13_);
lean_dec(v_k_12_);
lean_dec(v_t_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(lean_object* v_fst_17_, lean_object* v_as_18_, size_t v_i_19_, size_t v_stop_20_, lean_object* v_b_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_usize_dec_eq(v_i_19_, v_stop_20_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; size_t v___x_28_; size_t v___x_29_; 
v___x_23_ = lean_array_uget_borrowed(v_as_18_, v_i_19_);
v___x_24_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
v___x_25_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_b_21_, v___x_23_, v___x_24_);
lean_inc_ref(v_fst_17_);
v___x_26_ = lean_array_push(v___x_25_, v_fst_17_);
lean_inc(v___x_23_);
v___x_27_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_23_, v___x_26_, v_b_21_);
v___x_28_ = ((size_t)1ULL);
v___x_29_ = lean_usize_add(v_i_19_, v___x_28_);
v_i_19_ = v___x_29_;
v_b_21_ = v___x_27_;
goto _start;
}
else
{
lean_dec_ref(v_fst_17_);
return v_b_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___boxed(lean_object* v_fst_31_, lean_object* v_as_32_, lean_object* v_i_33_, lean_object* v_stop_34_, lean_object* v_b_35_){
_start:
{
size_t v_i_boxed_36_; size_t v_stop_boxed_37_; lean_object* v_res_38_; 
v_i_boxed_36_ = lean_unbox_usize(v_i_33_);
lean_dec(v_i_33_);
v_stop_boxed_37_ = lean_unbox_usize(v_stop_34_);
lean_dec(v_stop_34_);
v_res_38_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_31_, v_as_32_, v_i_boxed_36_, v_stop_boxed_37_, v_b_35_);
lean_dec_ref(v_as_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_es_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_fst_41_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_fst_41_);
v_snd_42_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_snd_42_);
lean_dec_ref(v_x_40_);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_array_get_size(v_snd_42_);
v___x_45_ = lean_nat_dec_lt(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec(v_snd_42_);
lean_dec(v_fst_41_);
return v_es_39_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_le(v___x_44_, v___x_44_);
if (v___x_46_ == 0)
{
if (v___x_45_ == 0)
{
lean_dec(v_snd_42_);
lean_dec(v_fst_41_);
return v_es_39_;
}
else
{
size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_44_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_41_, v_snd_42_, v___x_47_, v___x_48_, v_es_39_);
lean_dec(v_snd_42_);
return v___x_49_;
}
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_44_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_41_, v_snd_42_, v___x_50_, v___x_51_, v_es_39_);
lean_dec(v_snd_42_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_k_55_; lean_object* v_v_56_; lean_object* v_l_57_; lean_object* v_r_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_k_55_ = lean_ctor_get(v_x_54_, 1);
v_v_56_ = lean_ctor_get(v_x_54_, 2);
v_l_57_ = lean_ctor_get(v_x_54_, 3);
v_r_58_ = lean_ctor_get(v_x_54_, 4);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_53_, v_l_57_);
lean_inc(v_v_56_);
lean_inc(v_k_55_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v_k_55_);
lean_ctor_set(v___x_60_, 1, v_v_56_);
v___x_61_ = lean_array_push(v___x_59_, v___x_60_);
v_init_53_ = v___x_61_;
v_x_54_ = v_r_58_;
goto _start;
}
else
{
return v_init_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_63_, v_x_64_);
lean_dec(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_66_, lean_object* v_pivot_67_, lean_object* v_as_68_, lean_object* v_i_69_, lean_object* v_k_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_lt(v_k_70_, v_hi_66_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_k_70_);
v___x_72_ = lean_array_fswap(v_as_68_, v_i_69_, v_hi_66_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_i_69_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v_fst_75_; lean_object* v_fst_76_; uint8_t v___x_77_; 
v___x_74_ = lean_array_fget_borrowed(v_as_68_, v_k_70_);
v_fst_75_ = lean_ctor_get(v___x_74_, 0);
v_fst_76_ = lean_ctor_get(v_pivot_67_, 0);
v___x_77_ = l_Lean_Name_quickLt(v_fst_75_, v_fst_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_k_70_, v___x_78_);
lean_dec(v_k_70_);
v_k_70_ = v___x_79_;
goto _start;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = lean_array_fswap(v_as_68_, v_i_69_, v_k_70_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_i_69_, v___x_82_);
lean_dec(v_i_69_);
v___x_84_ = lean_nat_add(v_k_70_, v___x_82_);
lean_dec(v_k_70_);
v_as_68_ = v___x_81_;
v_i_69_ = v___x_83_;
v_k_70_ = v___x_84_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_86_, lean_object* v_pivot_87_, lean_object* v_as_88_, lean_object* v_i_89_, lean_object* v_k_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_86_, v_pivot_87_, v_as_88_, v_i_89_, v_k_90_);
lean_dec_ref(v_pivot_87_);
lean_dec(v_hi_86_);
return v_res_91_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_92_, lean_object* v_x2_93_){
_start:
{
lean_object* v_fst_94_; lean_object* v_fst_95_; uint8_t v___x_96_; 
v_fst_94_ = lean_ctor_get(v_x1_92_, 0);
v_fst_95_ = lean_ctor_get(v_x2_93_, 0);
v___x_96_ = l_Lean_Name_quickLt(v_fst_94_, v_fst_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_97_, lean_object* v_x2_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_97_, v_x2_98_);
lean_dec_ref(v_x2_98_);
lean_dec_ref(v_x1_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_101_, lean_object* v_as_102_, lean_object* v_lo_103_, lean_object* v_hi_104_){
_start:
{
lean_object* v___y_106_; uint8_t v___x_116_; 
v___x_116_ = lean_nat_dec_lt(v_lo_103_, v_hi_104_);
if (v___x_116_ == 0)
{
lean_dec(v_lo_103_);
return v_as_102_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_mid_119_; lean_object* v___y_121_; lean_object* v___y_127_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_117_ = lean_nat_add(v_lo_103_, v_hi_104_);
v___x_118_ = lean_unsigned_to_nat(1u);
v_mid_119_ = lean_nat_shiftr(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v___x_132_ = lean_array_fget_borrowed(v_as_102_, v_mid_119_);
v___x_133_ = lean_array_fget_borrowed(v_as_102_, v_lo_103_);
v___x_134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
v___y_127_ = v_as_102_;
goto v___jp_126_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_array_fswap(v_as_102_, v_lo_103_, v_mid_119_);
v___y_127_ = v___x_135_;
goto v___jp_126_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_122_ = lean_array_fget_borrowed(v___y_121_, v_mid_119_);
v___x_123_ = lean_array_fget_borrowed(v___y_121_, v_hi_104_);
v___x_124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec(v_mid_119_);
v___y_106_ = v___y_121_;
goto v___jp_105_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_array_fswap(v___y_121_, v_mid_119_, v_hi_104_);
lean_dec(v_mid_119_);
v___y_106_ = v___x_125_;
goto v___jp_105_;
}
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_array_fget_borrowed(v___y_127_, v_hi_104_);
v___x_129_ = lean_array_fget_borrowed(v___y_127_, v_lo_103_);
v___x_130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
v___y_121_ = v___y_127_;
goto v___jp_120_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_array_fswap(v___y_127_, v_lo_103_, v_hi_104_);
v___y_121_ = v___x_131_;
goto v___jp_120_;
}
}
}
v___jp_105_:
{
lean_object* v_pivot_107_; lean_object* v___x_108_; lean_object* v_fst_109_; lean_object* v_snd_110_; uint8_t v___x_111_; 
v_pivot_107_ = lean_array_fget(v___y_106_, v_hi_104_);
lean_inc_n(v_lo_103_, 2);
v___x_108_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_104_, v_pivot_107_, v___y_106_, v_lo_103_, v_lo_103_);
lean_dec(v_pivot_107_);
v_fst_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_fst_109_);
v_snd_110_ = lean_ctor_get(v___x_108_, 1);
lean_inc(v_snd_110_);
lean_dec_ref(v___x_108_);
v___x_111_ = lean_nat_dec_le(v_hi_104_, v_fst_109_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_n_101_, v_snd_110_, v_lo_103_, v_fst_109_);
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v_fst_109_, v___x_113_);
lean_dec(v_fst_109_);
v_as_102_ = v___x_112_;
v_lo_103_ = v___x_114_;
goto _start;
}
else
{
lean_dec(v_fst_109_);
lean_dec(v_lo_103_);
return v_snd_110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_136_, lean_object* v_as_137_, lean_object* v_lo_138_, lean_object* v_hi_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_n_136_, v_as_137_, v_lo_138_, v_hi_139_);
lean_dec(v_hi_139_);
lean_dec(v_n_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_x_143_, lean_object* v_s_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___y_150_; lean_object* v___y_151_; uint8_t v___x_154_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_147_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_146_, v_s_144_);
v___x_148_ = lean_array_get_size(v___x_147_);
v___x_154_ = lean_nat_dec_eq(v___x_148_, v___x_145_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___y_158_; uint8_t v___x_160_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_sub(v___x_148_, v___x_155_);
v___x_160_ = lean_nat_dec_le(v___x_145_, v___x_156_);
if (v___x_160_ == 0)
{
lean_inc(v___x_156_);
v___y_158_ = v___x_156_;
goto v___jp_157_;
}
else
{
v___y_158_ = v___x_145_;
goto v___jp_157_;
}
v___jp_157_:
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_le(v___y_158_, v___x_156_);
if (v___x_159_ == 0)
{
lean_dec(v___x_156_);
lean_inc(v___y_158_);
v___y_150_ = v___y_158_;
v___y_151_ = v___y_158_;
goto v___jp_149_;
}
else
{
v___y_150_ = v___y_158_;
v___y_151_ = v___x_156_;
goto v___jp_149_;
}
}
}
else
{
lean_object* v___x_161_; 
lean_inc_ref_n(v___x_147_, 2);
v___x_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_147_);
lean_ctor_set(v___x_161_, 1, v___x_147_);
lean_ctor_set(v___x_161_, 2, v___x_147_);
return v___x_161_;
}
v___jp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_148_, v___x_147_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_inc_ref_n(v___x_152_, 2);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_x_162_, lean_object* v_s_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_162_, v_s_163_);
lean_dec(v_s_163_);
lean_dec_ref(v_x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_x_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_167_);
lean_dec(v_x_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_es_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_172_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_171_, v_es_169_);
v___x_173_ = lean_array_get_size(v___x_172_);
v___x_174_ = lean_nat_dec_eq(v___x_173_, v___x_170_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___y_178_; uint8_t v___x_182_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_sub(v___x_173_, v___x_175_);
v___x_182_ = lean_nat_dec_le(v___x_170_, v___x_176_);
if (v___x_182_ == 0)
{
lean_inc(v___x_176_);
v___y_178_ = v___x_176_;
goto v___jp_177_;
}
else
{
v___y_178_ = v___x_170_;
goto v___jp_177_;
}
v___jp_177_:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_le(v___y_178_, v___x_176_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec(v___x_176_);
lean_inc(v___y_178_);
v___x_180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_173_, v___x_172_, v___y_178_, v___y_178_);
lean_dec(v___y_178_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_173_, v___x_172_, v___y_178_, v___x_176_);
lean_dec(v___x_176_);
return v___x_181_;
}
}
}
else
{
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_es_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_es_183_);
lean_dec(v_es_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v___x_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v___x_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v___x_191_, lean_object* v_x_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_191_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v___x_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_196_, v_x_197_, v___y_198_);
lean_dec_ref(v___y_198_);
lean_dec_ref(v_x_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_234_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(lean_object* v_init_237_, lean_object* v_t_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_237_, v_t_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_240_, lean_object* v_t_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(v_init_240_, v_t_241_);
lean_dec(v_t_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(lean_object* v_n_243_, lean_object* v_as_244_, lean_object* v_lo_245_, lean_object* v_hi_246_, lean_object* v_w_247_, lean_object* v_hlo_248_, lean_object* v_hhi_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_n_243_, v_as_244_, v_lo_245_, v_hi_246_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_251_, lean_object* v_as_252_, lean_object* v_lo_253_, lean_object* v_hi_254_, lean_object* v_w_255_, lean_object* v_hlo_256_, lean_object* v_hhi_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(v_n_251_, v_as_252_, v_lo_253_, v_hi_254_, v_w_255_, v_hlo_256_, v_hhi_257_);
lean_dec(v_hi_254_);
lean_dec(v_n_251_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_259_, lean_object* v_t_260_, lean_object* v_k_261_, lean_object* v_fallback_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_260_, v_k_261_, v_fallback_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_264_, lean_object* v_t_265_, lean_object* v_k_266_, lean_object* v_fallback_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(v_00_u03b4_264_, v_t_265_, v_k_266_, v_fallback_267_);
lean_dec(v_fallback_267_);
lean_dec(v_k_266_);
lean_dec(v_t_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_269_, lean_object* v_lo_270_, lean_object* v_hi_271_, lean_object* v_hhi_272_, lean_object* v_pivot_273_, lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_k_276_, lean_object* v_ilo_277_, lean_object* v_ik_278_, lean_object* v_w_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_271_, v_pivot_273_, v_as_274_, v_i_275_, v_k_276_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_281_, lean_object* v_lo_282_, lean_object* v_hi_283_, lean_object* v_hhi_284_, lean_object* v_pivot_285_, lean_object* v_as_286_, lean_object* v_i_287_, lean_object* v_k_288_, lean_object* v_ilo_289_, lean_object* v_ik_290_, lean_object* v_w_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1_spec__2(v_n_281_, v_lo_282_, v_hi_283_, v_hhi_284_, v_pivot_285_, v_as_286_, v_i_287_, v_k_288_, v_ilo_289_, v_ik_290_, v_w_291_);
lean_dec_ref(v_pivot_285_);
lean_dec(v_hi_283_);
lean_dec(v_lo_282_);
lean_dec(v_n_281_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___y_293_){
_start:
{
lean_inc_ref(v___y_293_);
return v___y_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___y_294_);
lean_dec_ref(v___y_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v_x_296_, lean_object* v_s_297_){
_start:
{
lean_object* v___x_298_; 
lean_inc_ref_n(v_s_297_, 2);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v_s_297_);
lean_ctor_set(v___x_298_, 1, v_s_297_);
lean_ctor_set(v___x_298_, 2, v_s_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_x_299_, lean_object* v_s_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_299_, v_s_300_);
lean_dec_ref(v_x_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(0);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_304_);
lean_dec_ref(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___x_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___x_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___x_312_, lean_object* v_x_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_312_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___x_317_, lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_317_, v_x_318_, v___y_319_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v_x_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_));
v___x_353_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_addRecommendedSpelling(lean_object* v_env_356_, lean_object* v_rec_357_, lean_object* v_names_358_){
_start:
{
lean_object* v___x_359_; lean_object* v_toEnvExtension_360_; lean_object* v_asyncMode_361_; lean_object* v___x_362_; lean_object* v_toEnvExtension_363_; lean_object* v_asyncMode_364_; lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_359_ = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
v_toEnvExtension_360_ = lean_ctor_get(v___x_359_, 0);
v_asyncMode_361_ = lean_ctor_get(v_toEnvExtension_360_, 2);
v___x_362_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
v_toEnvExtension_363_ = lean_ctor_get(v___x_362_, 0);
v_asyncMode_364_ = lean_ctor_get(v_toEnvExtension_363_, 2);
v___x_365_ = lean_box(0);
lean_inc_ref(v_rec_357_);
v_env_366_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_359_, v_env_356_, v_rec_357_, v_asyncMode_361_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_rec_357_);
lean_ctor_set(v___x_367_, 1, v_names_358_);
v___x_368_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_362_, v_env_366_, v___x_367_, v_asyncMode_364_, v___x_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(lean_object* v_as_369_, lean_object* v_k_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_m_375_; lean_object* v_a_376_; uint8_t v___x_377_; 
v___x_373_ = lean_nat_add(v_x_371_, v_x_372_);
v___x_374_ = lean_unsigned_to_nat(1u);
v_m_375_ = lean_nat_shiftr(v___x_373_, v___x_374_);
lean_dec(v___x_373_);
v_a_376_ = lean_array_fget_borrowed(v_as_369_, v_m_375_);
v___x_377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_376_, v_k_370_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
lean_dec(v_x_372_);
v___x_378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_370_, v_a_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_m_375_);
lean_dec(v_x_371_);
lean_inc(v_a_376_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_a_376_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; uint8_t v___x_381_; lean_object* v___x_382_; uint8_t v___y_384_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_nat_dec_eq(v_m_375_, v___x_380_);
v___x_382_ = lean_nat_sub(v_m_375_, v___x_374_);
lean_dec(v_m_375_);
if (v___x_381_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_lt(v___x_382_, v_x_371_);
v___y_384_ = v___x_387_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___x_381_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
v_x_372_ = v___x_382_;
goto _start;
}
else
{
lean_object* v___x_386_; 
lean_dec(v___x_382_);
lean_dec(v_x_371_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
}
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
lean_dec(v_x_371_);
v___x_388_ = lean_nat_add(v_m_375_, v___x_374_);
lean_dec(v_m_375_);
v___x_389_ = lean_nat_dec_le(v___x_388_, v_x_372_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec(v___x_388_);
lean_dec(v_x_372_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
else
{
v_x_371_ = v___x_388_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg___boxed(lean_object* v_as_392_, lean_object* v_k_393_, lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_392_, v_k_393_, v_x_394_, v_x_395_);
lean_dec_ref(v_k_393_);
lean_dec_ref(v_as_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(lean_object* v_declName_397_, lean_object* v_as_398_, size_t v_sz_399_, size_t v_i_400_, lean_object* v_b_401_){
_start:
{
lean_object* v_a_403_; uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_lt(v_i_400_, v_sz_399_);
if (v___x_407_ == 0)
{
lean_dec(v_declName_397_);
return v_b_401_;
}
else
{
lean_object* v___x_408_; lean_object* v_a_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v_a_409_ = lean_array_uget_borrowed(v_as_398_, v_i_400_);
v___x_410_ = lean_array_get_size(v_a_409_);
v___x_411_ = lean_nat_dec_lt(v___x_408_, v___x_410_);
if (v___x_411_ == 0)
{
v_a_403_ = v_b_401_;
goto v___jp_402_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_sub(v___x_410_, v___x_412_);
v___x_414_ = lean_nat_dec_le(v___x_408_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec(v___x_413_);
v_a_403_ = v_b_401_;
goto v___jp_402_;
}
else
{
lean_object* v_spellings_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_spellings_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
lean_inc(v_declName_397_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_declName_397_);
lean_ctor_set(v___x_416_, 1, v_spellings_415_);
v___x_417_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_a_409_, v___x_416_, v___x_408_, v___x_413_);
lean_dec_ref_known(v___x_416_, 2);
if (lean_obj_tag(v___x_417_) == 1)
{
lean_object* v_val_418_; lean_object* v_snd_419_; lean_object* v___x_420_; 
v_val_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v___x_417_, 1);
v_snd_419_ = lean_ctor_get(v_val_418_, 1);
lean_inc(v_snd_419_);
lean_dec(v_val_418_);
v___x_420_ = l_Array_append___redArg(v_b_401_, v_snd_419_);
lean_dec(v_snd_419_);
v_a_403_ = v___x_420_;
goto v___jp_402_;
}
else
{
lean_dec(v___x_417_);
v_a_403_ = v_b_401_;
goto v___jp_402_;
}
}
}
}
v___jp_402_:
{
size_t v___x_404_; size_t v___x_405_; 
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_400_, v___x_404_);
v_i_400_ = v___x_405_;
v_b_401_ = v_a_403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1___boxed(lean_object* v_declName_421_, lean_object* v_as_422_, lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_b_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_421_, v_as_422_, v_sz_boxed_426_, v_i_boxed_427_, v_b_425_);
lean_dec_ref(v_as_422_);
return v_res_428_;
}
}
static lean_object* _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(1);
v___x_430_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(lean_object* v_env_431_, lean_object* v_declName_432_){
_start:
{
lean_object* v___x_433_; lean_object* v_toEnvExtension_434_; lean_object* v_asyncMode_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_importedEntries_440_; lean_object* v_spellings_441_; size_t v_sz_442_; size_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_433_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
v_toEnvExtension_434_ = lean_ctor_get(v___x_433_, 0);
v_asyncMode_435_ = lean_ctor_get(v_toEnvExtension_434_, 2);
v___x_436_ = lean_box(1);
v___x_437_ = lean_obj_once(&l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0, &l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0_once, _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0);
v___x_438_ = lean_box(0);
lean_inc_ref(v_env_431_);
v___x_439_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_437_, v_toEnvExtension_434_, v_env_431_, v_asyncMode_435_, v___x_438_);
v_importedEntries_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc_ref(v_importedEntries_440_);
lean_dec(v___x_439_);
v_spellings_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
v_sz_442_ = lean_array_size(v_importedEntries_440_);
v___x_443_ = ((size_t)0ULL);
lean_inc(v_declName_432_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_432_, v_importedEntries_440_, v_sz_442_, v___x_443_, v_spellings_441_);
lean_dec_ref(v_importedEntries_440_);
v___x_445_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_436_, v___x_433_, v_env_431_, v_asyncMode_435_, v___x_438_);
v___x_446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_445_, v_declName_432_);
lean_dec(v_declName_432_);
lean_dec(v___x_445_);
if (lean_obj_tag(v___x_446_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; 
v_val_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = l_Array_append___redArg(v___x_444_, v_val_447_);
lean_dec(v_val_447_);
return v___x_448_;
}
else
{
lean_dec(v___x_446_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(lean_object* v_as_449_, lean_object* v_k_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_449_, v_k_450_, v_x_451_, v_x_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___boxed(lean_object* v_as_455_, lean_object* v_k_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(v_as_455_, v_k_456_, v_x_457_, v_x_458_, v_x_459_);
lean_dec_ref(v_k_456_);
lean_dec_ref(v_as_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(lean_object* v_s_461_, lean_object* v_pos_462_){
_start:
{
lean_object* v_str_463_; lean_object* v_startInclusive_464_; lean_object* v_endExclusive_465_; lean_object* v___x_466_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v_decide_477_; 
v_str_463_ = lean_ctor_get(v_s_461_, 0);
v_startInclusive_464_ = lean_ctor_get(v_s_461_, 1);
v_endExclusive_465_ = lean_ctor_get(v_s_461_, 2);
v___x_466_ = lean_nat_add(v_startInclusive_464_, v_pos_462_);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_nat_sub(v_endExclusive_465_, v___x_466_);
v_decide_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
lean_dec(v___x_476_);
if (v_decide_477_ == 0)
{
uint32_t v___x_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_string_utf8_get_fast(v_str_463_, v___x_466_);
v___x_479_ = 32;
v___x_480_ = lean_uint32_dec_eq(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 9;
v___x_482_ = lean_uint32_dec_eq(v___x_478_, v___x_481_);
if (v___x_482_ == 0)
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 13;
v___x_484_ = lean_uint32_dec_eq(v___x_478_, v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 10;
v___x_486_ = lean_uint32_dec_eq(v___x_478_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v___x_466_);
return v_pos_462_;
}
else
{
goto v___jp_467_;
}
}
else
{
goto v___jp_467_;
}
}
else
{
goto v___jp_467_;
}
}
else
{
goto v___jp_467_;
}
}
else
{
lean_dec(v___x_466_);
return v_pos_462_;
}
v___jp_467_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_468_ = lean_string_utf8_next_fast(v_str_463_, v___x_466_);
v___x_469_ = lean_nat_sub(v___x_468_, v___x_466_);
lean_dec(v___x_466_);
v___x_470_ = lean_nat_add(v_pos_462_, v___x_469_);
lean_dec(v___x_469_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_pos_462_, v___x_471_);
v___x_473_ = lean_nat_dec_le(v___x_472_, v___x_470_);
lean_dec(v___x_472_);
if (v___x_473_ == 0)
{
lean_dec(v___x_470_);
return v_pos_462_;
}
else
{
lean_dec(v_pos_462_);
v_pos_462_ = v___x_470_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0___boxed(lean_object* v_s_487_, lean_object* v_pos_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v_s_487_, v_pos_488_);
lean_dec_ref(v_s_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(lean_object* v_str_492_){
_start:
{
lean_object* v___y_494_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v_decide_501_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_string_utf8_byte_size(v_str_492_);
lean_inc_ref(v_str_492_);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v_str_492_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
v___x_500_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v___x_499_, v___x_497_);
lean_dec_ref_known(v___x_499_, 3);
v_decide_501_ = lean_nat_dec_eq(v___x_500_, v___x_498_);
lean_dec(v___x_500_);
if (v_decide_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1));
v___x_503_ = lean_string_append(v___x_502_, v_str_492_);
lean_dec_ref(v_str_492_);
v___y_494_ = v___x_503_;
goto v___jp_493_;
}
else
{
v___y_494_ = v_str_492_;
goto v___jp_493_;
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0));
v___x_496_ = lean_string_append(v___y_494_, v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(lean_object* v_s_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0));
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___boxed(lean_object* v_s_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v_s_508_);
lean_dec_ref(v_s_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(lean_object* v_val_510_, lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v_a_513_, lean_object* v_b_514_){
_start:
{
lean_object* v_it_516_; lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; 
if (lean_obj_tag(v_a_513_) == 0)
{
lean_object* v_currPos_523_; lean_object* v_searcher_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_547_; 
v_currPos_523_ = lean_ctor_get(v_a_513_, 0);
v_searcher_524_ = lean_ctor_get(v_a_513_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_547_ == 0)
{
v___x_526_ = v_a_513_;
v_isShared_527_ = v_isSharedCheck_547_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_searcher_524_);
lean_inc(v_currPos_523_);
lean_dec(v_a_513_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_547_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v_decide_528_; 
v_decide_528_ = lean_nat_dec_eq(v_searcher_524_, v___x_512_);
if (v_decide_528_ == 0)
{
uint32_t v___x_529_; uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_529_ = 10;
v___x_530_ = lean_string_utf8_get_fast(v_val_510_, v_searcher_524_);
v___x_531_ = lean_uint32_dec_eq(v___x_530_, v___x_529_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_string_utf8_next_fast(v_val_510_, v_searcher_524_);
lean_dec(v_searcher_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_532_);
v___x_534_ = v___x_526_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_currPos_523_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
v_a_513_ = v___x_534_;
goto _start;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_slice_540_; lean_object* v_nextIt_542_; 
v___x_537_ = lean_string_utf8_next_fast(v_val_510_, v_searcher_524_);
v___x_538_ = lean_nat_sub(v___x_537_, v_searcher_524_);
v___x_539_ = lean_nat_add(v_searcher_524_, v___x_538_);
lean_dec(v___x_538_);
v_slice_540_ = l_String_Slice_subslice_x21(v___x_511_, v_currPos_523_, v_searcher_524_);
lean_inc(v___x_539_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_539_);
lean_ctor_set(v___x_526_, 0, v___x_539_);
v_nextIt_542_ = v___x_526_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_539_);
v_nextIt_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v_startInclusive_543_; lean_object* v_endExclusive_544_; 
v_startInclusive_543_ = lean_ctor_get(v_slice_540_, 0);
lean_inc(v_startInclusive_543_);
v_endExclusive_544_ = lean_ctor_get(v_slice_540_, 1);
lean_inc(v_endExclusive_544_);
lean_dec_ref(v_slice_540_);
v_it_516_ = v_nextIt_542_;
v_startInclusive_517_ = v_startInclusive_543_;
v_endExclusive_518_ = v_endExclusive_544_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v___x_546_; 
lean_del_object(v___x_526_);
lean_dec(v_searcher_524_);
v___x_546_ = lean_box(1);
lean_inc(v___x_512_);
v_it_516_ = v___x_546_;
v_startInclusive_517_ = v_currPos_523_;
v_endExclusive_518_ = v___x_512_;
goto v___jp_515_;
}
}
}
else
{
lean_dec(v___x_512_);
lean_dec_ref(v_val_510_);
return v_b_514_;
}
v___jp_515_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_inc_ref(v_val_510_);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v_val_510_);
lean_ctor_set(v___x_519_, 1, v_startInclusive_517_);
lean_ctor_set(v___x_519_, 2, v_endExclusive_518_);
v___x_520_ = l_String_Slice_toString(v___x_519_);
lean_dec_ref_known(v___x_519_, 3);
v___x_521_ = lean_array_push(v_b_514_, v___x_520_);
v_a_513_ = v_it_516_;
v_b_514_ = v___x_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg___boxed(lean_object* v_val_548_, lean_object* v___x_549_, lean_object* v___x_550_, lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_548_, v___x_549_, v___x_550_, v_a_551_, v_b_552_);
lean_dec_ref(v___x_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
if (lean_obj_tag(v_a_554_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = l_List_reverse___redArg(v_a_555_);
return v___x_556_;
}
else
{
lean_object* v_head_557_; lean_object* v_tail_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_567_; 
v_head_557_ = lean_ctor_get(v_a_554_, 0);
v_tail_558_ = lean_ctor_get(v_a_554_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_567_ == 0)
{
v___x_560_ = v_a_554_;
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_tail_558_);
lean_inc(v_head_557_);
lean_dec(v_a_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(v_head_557_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_a_555_);
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_555_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v_a_554_ = v_tail_558_;
v_a_555_ = v___x_564_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(lean_object* v_s_568_, lean_object* v_pos_569_){
_start:
{
lean_object* v_str_570_; lean_object* v_startInclusive_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v_decide_575_; 
v_str_570_ = lean_ctor_get(v_s_568_, 0);
v_startInclusive_571_ = lean_ctor_get(v_s_568_, 1);
v___x_572_ = lean_nat_add(v_startInclusive_571_, v_pos_569_);
v___x_573_ = lean_nat_sub(v___x_572_, v_startInclusive_571_);
v___x_574_ = lean_unsigned_to_nat(0u);
v_decide_575_ = lean_nat_dec_eq(v___x_573_, v___x_574_);
if (v_decide_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_584_; uint32_t v___x_585_; uint32_t v___x_586_; uint8_t v___x_587_; 
lean_inc(v_startInclusive_571_);
lean_inc_ref(v_str_570_);
v___x_576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_576_, 0, v_str_570_);
lean_ctor_set(v___x_576_, 1, v_startInclusive_571_);
lean_ctor_set(v___x_576_, 2, v___x_572_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_sub(v___x_573_, v___x_577_);
lean_dec(v___x_573_);
v___x_579_ = l_String_Slice_posLE(v___x_576_, v___x_578_);
lean_dec_ref_known(v___x_576_, 3);
v___x_584_ = lean_nat_add(v_startInclusive_571_, v___x_579_);
v___x_585_ = lean_string_utf8_get_fast(v_str_570_, v___x_584_);
lean_dec(v___x_584_);
v___x_586_ = 32;
v___x_587_ = lean_uint32_dec_eq(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
uint32_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = 9;
v___x_589_ = lean_uint32_dec_eq(v___x_585_, v___x_588_);
if (v___x_589_ == 0)
{
uint32_t v___x_590_; uint8_t v___x_591_; 
v___x_590_ = 13;
v___x_591_ = lean_uint32_dec_eq(v___x_585_, v___x_590_);
if (v___x_591_ == 0)
{
uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 10;
v___x_593_ = lean_uint32_dec_eq(v___x_585_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v___x_579_);
return v_pos_569_;
}
else
{
goto v___jp_580_;
}
}
else
{
goto v___jp_580_;
}
}
else
{
goto v___jp_580_;
}
}
else
{
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_nat_add(v___x_579_, v___x_577_);
v___x_582_ = lean_nat_dec_le(v___x_581_, v_pos_569_);
lean_dec(v___x_581_);
if (v___x_582_ == 0)
{
lean_dec(v___x_579_);
return v_pos_569_;
}
else
{
lean_dec(v_pos_569_);
v_pos_569_ = v___x_579_;
goto _start;
}
}
}
else
{
lean_dec(v___x_573_);
lean_dec(v___x_572_);
return v_pos_569_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2___boxed(lean_object* v_s_594_, lean_object* v_pos_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v_s_594_, v_pos_595_);
lean_dec_ref(v_s_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
return v_x_597_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v___x_601_; 
v_head_599_ = lean_ctor_get(v_x_598_, 0);
v_tail_600_ = lean_ctor_get(v_x_598_, 1);
v___x_601_ = lean_string_append(v_x_597_, v_head_599_);
v_x_597_ = v___x_601_;
v_x_598_ = v_tail_600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4___boxed(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v_x_603_, v_x_604_);
lean_dec(v_x_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(lean_object* v_spelling_616_){
_start:
{
lean_object* v_notation_617_; lean_object* v_recommendedSpelling_618_; lean_object* v_additionalInformation_x3f_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_664_; 
v_notation_617_ = lean_ctor_get(v_spelling_616_, 0);
v_recommendedSpelling_618_ = lean_ctor_get(v_spelling_616_, 1);
v_additionalInformation_x3f_619_ = lean_ctor_get(v_spelling_616_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_spelling_616_);
if (v_isSharedCheck_664_ == 0)
{
v___x_621_ = v_spelling_616_;
v_isShared_622_ = v_isSharedCheck_664_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_additionalInformation_x3f_619_);
lean_inc(v_recommendedSpelling_618_);
lean_inc(v_notation_617_);
lean_dec(v_spelling_616_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_664_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_firstLine_629_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0));
v___x_624_ = lean_string_append(v___x_623_, v_notation_617_);
lean_dec_ref(v_notation_617_);
v___x_625_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1));
v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
v___x_627_ = lean_string_append(v___x_626_, v_recommendedSpelling_618_);
lean_dec_ref(v_recommendedSpelling_618_);
v___x_628_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2));
v_firstLine_629_ = lean_string_append(v___x_627_, v___x_628_);
if (lean_obj_tag(v_additionalInformation_x3f_619_) == 0)
{
lean_del_object(v___x_621_);
goto v___jp_630_;
}
else
{
lean_object* v_val_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v_val_633_ = lean_ctor_get(v_additionalInformation_x3f_619_, 0);
lean_inc_n(v_val_633_, 2);
lean_dec_ref_known(v_additionalInformation_x3f_619_, 1);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_string_utf8_byte_size(v_val_633_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 2, v___x_635_);
lean_ctor_set(v___x_621_, 1, v___x_634_);
lean_ctor_set(v___x_621_, 0, v_val_633_);
v___x_637_ = v___x_621_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_val_633_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v___x_635_);
v___x_637_ = v_reuseFailAlloc_663_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v___x_637_);
v___x_639_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4));
v___x_640_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_633_, v___x_637_, v___x_635_, v___x_638_, v___x_639_);
lean_dec_ref(v___x_637_);
v___x_641_ = lean_array_to_list(v___x_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
goto v___jp_630_;
}
else
{
lean_object* v_tail_642_; 
v_tail_642_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_tail_642_);
if (lean_obj_tag(v_tail_642_) == 0)
{
lean_object* v_head_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_head_643_ = lean_ctor_get(v___x_641_, 0);
lean_inc_n(v_head_643_, 2);
lean_dec_ref_known(v___x_641_, 2);
v___x_644_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5));
v___x_645_ = lean_string_utf8_byte_size(v_head_643_);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v_head_643_);
lean_ctor_set(v___x_646_, 1, v___x_634_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
v___x_647_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_646_, v___x_645_);
lean_dec_ref_known(v___x_646_, 3);
v___x_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_648_, 0, v_head_643_);
lean_ctor_set(v___x_648_, 1, v___x_634_);
lean_ctor_set(v___x_648_, 2, v___x_647_);
v___x_649_ = l_String_Slice_toString(v___x_648_);
lean_dec_ref_known(v___x_648_, 3);
v___x_650_ = lean_string_append(v___x_644_, v___x_649_);
lean_dec_ref(v___x_649_);
v___x_651_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6));
v___x_652_ = lean_string_append(v___x_650_, v___x_651_);
v___x_653_ = lean_string_append(v_firstLine_629_, v___x_652_);
lean_dec_ref(v___x_652_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v_tail_642_);
v___x_654_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3));
v___x_655_ = lean_string_append(v_firstLine_629_, v___x_654_);
v___x_656_ = lean_box(0);
v___x_657_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(v___x_641_, v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
v___x_659_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_658_, v___x_657_);
lean_dec(v___x_657_);
v___x_660_ = lean_string_append(v___x_655_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8));
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
return v___x_662_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3));
v___x_632_ = lean_string_append(v_firstLine_629_, v___x_631_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(lean_object* v_val_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_inst_668_, lean_object* v_R_669_, lean_object* v_a_670_, lean_object* v_b_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_665_, v___x_666_, v___x_667_, v_a_670_, v_b_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___boxed(lean_object* v_val_673_, lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v_inst_676_, lean_object* v_R_677_, lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(v_val_673_, v___x_674_, v___x_675_, v_inst_676_, v_R_677_, v_a_678_, v_b_679_);
lean_dec_ref(v___x_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = l_List_reverse___redArg(v_a_682_);
return v___x_683_;
}
else
{
lean_object* v_head_684_; lean_object* v_tail_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
v_head_684_ = lean_ctor_get(v_a_681_, 0);
v_tail_685_ = lean_ctor_get(v_a_681_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_694_ == 0)
{
v___x_687_ = v_a_681_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_tail_685_);
lean_inc(v_head_684_);
lean_dec(v_a_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(v_head_684_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_a_682_);
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_a_682_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_a_681_ = v_tail_685_;
v_a_682_ = v___x_691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object* v_env_696_, lean_object* v_declName_697_){
_start:
{
lean_object* v_spellings_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_spellings_698_ = l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(v_env_696_, v_declName_697_);
v___x_699_ = lean_array_get_size(v_spellings_698_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_702_ = ((lean_object*)(l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0));
v___x_703_ = lean_array_to_list(v_spellings_698_);
v___x_704_ = lean_box(0);
v___x_705_ = l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(v___x_703_, v___x_704_);
v___x_706_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
v___x_707_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_706_, v___x_705_);
lean_dec(v___x_705_);
v___x_708_ = lean_string_append(v___x_702_, v___x_707_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_string_utf8_byte_size(v___x_708_);
lean_inc_ref(v___x_708_);
v___x_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_700_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
v___x_711_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_710_, v___x_709_);
lean_dec_ref_known(v___x_710_, 3);
v___x_712_ = lean_string_utf8_extract_fast(v___x_708_, v___x_700_, v___x_711_);
lean_dec(v___x_711_);
lean_dec_ref(v___x_708_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
lean_dec_ref(v_spellings_698_);
v___x_713_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
return v___x_713_;
}
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt);
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Term_Doc_recommendedSpellingExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Term_Doc_recommendedSpellingExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Term_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Term_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Term_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
