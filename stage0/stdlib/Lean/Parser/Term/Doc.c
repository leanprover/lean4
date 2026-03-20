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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "recommendedSpellingByNameExt"};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 37, 190, 246, 145, 148, 24, 135)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 208, 209, 98, 233, 154, 255, 115)}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__11_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__12_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "recommendedSpellingExt"};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 37, 190, 246, 145, 148, 24, 135)}};
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 98, 124, 104, 70, 9, 210, 178)}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__5_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__6_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__7_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__8_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__9_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_1_, lean_object* v_k_2_, lean_object* v_fallback_3_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_11_, lean_object* v_k_12_, lean_object* v_fallback_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_11_, v_k_12_, v_fallback_13_);
lean_dec(v_fallback_13_);
lean_dec(v_k_12_);
lean_dec(v_t_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(lean_object* v_fst_17_, lean_object* v_as_18_, size_t v_i_19_, size_t v_stop_20_, lean_object* v_b_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_usize_dec_eq(v_i_19_, v_stop_20_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; size_t v___x_28_; size_t v___x_29_; 
v___x_23_ = lean_array_uget_borrowed(v_as_18_, v_i_19_);
v___x_24_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
v___x_25_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_b_21_, v___x_23_, v___x_24_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___boxed(lean_object* v_fst_31_, lean_object* v_as_32_, lean_object* v_i_33_, lean_object* v_stop_34_, lean_object* v_b_35_){
_start:
{
size_t v_i_boxed_36_; size_t v_stop_boxed_37_; lean_object* v_res_38_; 
v_i_boxed_36_ = lean_unbox_usize(v_i_33_);
lean_dec(v_i_33_);
v_stop_boxed_37_ = lean_unbox_usize(v_stop_34_);
lean_dec(v_stop_34_);
v_res_38_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_31_, v_as_32_, v_i_boxed_36_, v_stop_boxed_37_, v_b_35_);
lean_dec_ref(v_as_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_es_39_, lean_object* v_x_40_){
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
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_41_, v_snd_42_, v___x_47_, v___x_48_, v_es_39_);
lean_dec(v_snd_42_);
return v___x_49_;
}
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_44_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3(v_fst_41_, v_snd_42_, v___x_50_, v___x_51_, v_es_39_);
lean_dec(v_snd_42_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_k_55_; lean_object* v_v_56_; lean_object* v_l_57_; lean_object* v_r_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_k_55_ = lean_ctor_get(v_x_54_, 1);
v_v_56_ = lean_ctor_get(v_x_54_, 2);
v_l_57_ = lean_ctor_get(v_x_54_, 3);
v_r_58_ = lean_ctor_get(v_x_54_, 4);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_53_, v_l_57_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_63_, v_x_64_);
lean_dec(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_66_, lean_object* v_x2_67_){
_start:
{
lean_object* v_fst_68_; lean_object* v_fst_69_; uint8_t v___x_70_; 
v_fst_68_ = lean_ctor_get(v_x1_66_, 0);
v_fst_69_ = lean_ctor_get(v_x2_67_, 0);
v___x_70_ = l_Lean_Name_quickLt(v_fst_68_, v_fst_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_71_, lean_object* v_x2_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_71_, v_x2_72_);
lean_dec_ref(v_x2_72_);
lean_dec_ref(v_x1_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_76_, lean_object* v_lo_77_, lean_object* v_hi_78_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = lean_nat_dec_lt(v_lo_77_, v_hi_78_);
if (v___x_79_ == 0)
{
lean_dec(v_lo_77_);
return v_as_76_;
}
else
{
lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v_fst_82_; lean_object* v_snd_83_; uint8_t v___x_84_; 
v___f_80_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_77_);
v___x_81_ = l_Array_qpartition___redArg(v_as_76_, v___f_80_, v_lo_77_, v_hi_78_);
v_fst_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_fst_82_);
v_snd_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc(v_snd_83_);
lean_dec_ref(v___x_81_);
v___x_84_ = lean_nat_dec_le(v_hi_78_, v_fst_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_snd_83_, v_lo_77_, v_fst_82_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_fst_82_, v___x_86_);
lean_dec(v_fst_82_);
v_as_76_ = v___x_85_;
v_lo_77_ = v___x_87_;
goto _start;
}
else
{
lean_dec(v_fst_82_);
lean_dec(v_lo_77_);
return v_snd_83_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_89_, lean_object* v_lo_90_, lean_object* v_hi_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_as_89_, v_lo_90_, v_hi_91_);
lean_dec(v_hi_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_x_95_, lean_object* v_s_96_, uint8_t v_x_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_100_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_99_, v_s_96_);
v___x_101_ = lean_array_get_size(v___x_100_);
v___x_102_ = lean_nat_dec_eq(v___x_101_, v___x_98_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___y_106_; uint8_t v___x_110_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_sub(v___x_101_, v___x_103_);
v___x_110_ = lean_nat_dec_le(v___x_98_, v___x_104_);
if (v___x_110_ == 0)
{
lean_inc(v___x_104_);
v___y_106_ = v___x_104_;
goto v___jp_105_;
}
else
{
v___y_106_ = v___x_98_;
goto v___jp_105_;
}
v___jp_105_:
{
uint8_t v___x_107_; 
v___x_107_ = lean_nat_dec_le(v___y_106_, v___x_104_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec(v___x_104_);
lean_inc(v___y_106_);
v___x_108_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_100_, v___y_106_, v___y_106_);
lean_dec(v___y_106_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_100_, v___y_106_, v___x_104_);
lean_dec(v___x_104_);
return v___x_109_;
}
}
}
else
{
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_x_111_, lean_object* v_s_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_x_1044__boxed_114_; lean_object* v_res_115_; 
v_x_1044__boxed_114_ = lean_unbox(v_x_113_);
v_res_115_ = l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_111_, v_s_112_, v_x_1044__boxed_114_);
lean_dec(v_s_112_);
lean_dec_ref(v_x_111_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_x_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_118_);
lean_dec(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_es_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_123_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_122_, v_es_120_);
v___x_124_ = lean_array_get_size(v___x_123_);
v___x_125_ = lean_nat_dec_eq(v___x_124_, v___x_121_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___y_129_; uint8_t v___x_133_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_sub(v___x_124_, v___x_126_);
v___x_133_ = lean_nat_dec_le(v___x_121_, v___x_127_);
if (v___x_133_ == 0)
{
lean_inc(v___x_127_);
v___y_129_ = v___x_127_;
goto v___jp_128_;
}
else
{
v___y_129_ = v___x_121_;
goto v___jp_128_;
}
v___jp_128_:
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_le(v___y_129_, v___x_127_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec(v___x_127_);
lean_inc(v___y_129_);
v___x_131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_123_, v___y_129_, v___y_129_);
lean_dec(v___y_129_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_123_, v___y_129_, v___x_127_);
lean_dec(v___x_127_);
return v___x_132_;
}
}
}
else
{
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_es_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_es_134_);
lean_dec(v_es_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v___x_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v___x_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v___x_142_, lean_object* v_x_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v___x_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_147_, v_x_148_, v___y_149_);
lean_dec_ref(v___y_149_);
lean_dec_ref(v_x_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_185_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(lean_object* v_init_188_, lean_object* v_t_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_188_, v_t_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_191_, lean_object* v_t_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(v_init_191_, v_t_192_);
lean_dec(v_t_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(lean_object* v_n_194_, lean_object* v_as_195_, lean_object* v_lo_196_, lean_object* v_hi_197_, lean_object* v_w_198_, lean_object* v_hlo_199_, lean_object* v_hhi_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_as_195_, v_lo_196_, v_hi_197_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_202_, lean_object* v_as_203_, lean_object* v_lo_204_, lean_object* v_hi_205_, lean_object* v_w_206_, lean_object* v_hlo_207_, lean_object* v_hhi_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(v_n_202_, v_as_203_, v_lo_204_, v_hi_205_, v_w_206_, v_hlo_207_, v_hhi_208_);
lean_dec(v_hi_205_);
lean_dec(v_n_202_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_210_, lean_object* v_t_211_, lean_object* v_k_212_, lean_object* v_fallback_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_211_, v_k_212_, v_fallback_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_215_, lean_object* v_t_216_, lean_object* v_k_217_, lean_object* v_fallback_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(v_00_u03b4_215_, v_t_216_, v_k_217_, v_fallback_218_);
lean_dec(v_fallback_218_);
lean_dec(v_k_217_);
lean_dec(v_t_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___y_220_){
_start:
{
lean_inc_ref(v___y_220_);
return v___y_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___y_221_);
lean_dec_ref(v___y_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v_x_223_, lean_object* v_s_224_, uint8_t v_x_225_){
_start:
{
lean_inc_ref(v_s_224_);
return v_s_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_x_226_, lean_object* v_s_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_x_291__boxed_229_; lean_object* v_res_230_; 
v_x_291__boxed_229_ = lean_unbox(v_x_228_);
v_res_230_ = l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_226_, v_s_227_, v_x_291__boxed_229_);
lean_dec_ref(v_s_227_);
lean_dec_ref(v_x_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(0);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_233_);
lean_dec_ref(v_x_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___x_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___x_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___x_241_, lean_object* v_x_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_241_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___x_246_, lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_246_, v_x_247_, v___y_248_);
lean_dec_ref(v___y_248_);
lean_dec_ref(v_x_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_));
v___x_282_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_addRecommendedSpelling(lean_object* v_env_285_, lean_object* v_rec_286_, lean_object* v_names_287_){
_start:
{
lean_object* v___x_288_; lean_object* v_toEnvExtension_289_; lean_object* v_asyncMode_290_; lean_object* v___x_291_; lean_object* v_toEnvExtension_292_; lean_object* v_asyncMode_293_; lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_288_ = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
v_toEnvExtension_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_toEnvExtension_289_);
v_asyncMode_290_ = lean_ctor_get(v_toEnvExtension_289_, 2);
lean_inc(v_asyncMode_290_);
lean_dec_ref(v_toEnvExtension_289_);
v___x_291_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
v_toEnvExtension_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_toEnvExtension_292_);
v_asyncMode_293_ = lean_ctor_get(v_toEnvExtension_292_, 2);
lean_inc(v_asyncMode_293_);
lean_dec_ref(v_toEnvExtension_292_);
v___x_294_ = lean_box(0);
lean_inc_ref(v_rec_286_);
v_env_295_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_288_, v_env_285_, v_rec_286_, v_asyncMode_290_, v___x_294_);
lean_dec(v_asyncMode_290_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_rec_286_);
lean_ctor_set(v___x_296_, 1, v_names_287_);
v___x_297_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_291_, v_env_295_, v___x_296_, v_asyncMode_293_, v___x_294_);
lean_dec(v_asyncMode_293_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(lean_object* v_as_298_, lean_object* v_k_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_m_304_; lean_object* v_a_305_; uint8_t v___x_306_; 
v___x_302_ = lean_nat_add(v_x_300_, v_x_301_);
v___x_303_ = lean_unsigned_to_nat(1u);
v_m_304_ = lean_nat_shiftr(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
v_a_305_ = lean_array_fget_borrowed(v_as_298_, v_m_304_);
v___x_306_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_305_, v_k_299_);
if (v___x_306_ == 0)
{
uint8_t v___x_307_; 
lean_dec(v_x_301_);
v___x_307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_299_, v_a_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec(v_m_304_);
lean_dec(v_x_300_);
lean_inc(v_a_305_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_a_305_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_nat_dec_eq(v_m_304_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_nat_sub(v_m_304_, v___x_303_);
lean_dec(v_m_304_);
v___x_312_ = lean_nat_dec_lt(v___x_311_, v_x_300_);
if (v___x_312_ == 0)
{
v_x_301_ = v___x_311_;
goto _start;
}
else
{
lean_object* v___x_314_; 
lean_dec(v___x_311_);
lean_dec(v_x_300_);
v___x_314_ = lean_box(0);
return v___x_314_;
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v_m_304_);
lean_dec(v_x_300_);
v___x_315_ = lean_box(0);
return v___x_315_;
}
}
}
else
{
lean_object* v___x_316_; uint8_t v___x_317_; 
lean_dec(v_x_300_);
v___x_316_ = lean_nat_add(v_m_304_, v___x_303_);
lean_dec(v_m_304_);
v___x_317_ = lean_nat_dec_le(v___x_316_, v_x_301_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
lean_dec(v___x_316_);
lean_dec(v_x_301_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
else
{
v_x_300_ = v___x_316_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg___boxed(lean_object* v_as_320_, lean_object* v_k_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_320_, v_k_321_, v_x_322_, v_x_323_);
lean_dec_ref(v_k_321_);
lean_dec_ref(v_as_320_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(lean_object* v_declName_325_, lean_object* v_as_326_, size_t v_sz_327_, size_t v_i_328_, lean_object* v_b_329_){
_start:
{
lean_object* v_a_331_; uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_lt(v_i_328_, v_sz_327_);
if (v___x_335_ == 0)
{
lean_dec(v_declName_325_);
return v_b_329_;
}
else
{
lean_object* v___x_336_; lean_object* v_a_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v_a_337_ = lean_array_uget_borrowed(v_as_326_, v_i_328_);
v___x_338_ = lean_array_get_size(v_a_337_);
v___x_339_ = lean_nat_dec_lt(v___x_336_, v___x_338_);
if (v___x_339_ == 0)
{
v_a_331_ = v_b_329_;
goto v___jp_330_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_sub(v___x_338_, v___x_340_);
v___x_342_ = lean_nat_dec_le(v___x_336_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec(v___x_341_);
v_a_331_ = v_b_329_;
goto v___jp_330_;
}
else
{
lean_object* v_spellings_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_spellings_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
lean_inc(v_declName_325_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_declName_325_);
lean_ctor_set(v___x_344_, 1, v_spellings_343_);
v___x_345_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_a_337_, v___x_344_, v___x_336_, v___x_341_);
lean_dec_ref(v___x_344_);
if (lean_obj_tag(v___x_345_) == 1)
{
lean_object* v_val_346_; lean_object* v_snd_347_; lean_object* v___x_348_; 
v_val_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_346_);
lean_dec_ref(v___x_345_);
v_snd_347_ = lean_ctor_get(v_val_346_, 1);
lean_inc(v_snd_347_);
lean_dec(v_val_346_);
v___x_348_ = l_Array_append___redArg(v_b_329_, v_snd_347_);
lean_dec(v_snd_347_);
v_a_331_ = v___x_348_;
goto v___jp_330_;
}
else
{
lean_dec(v___x_345_);
v_a_331_ = v_b_329_;
goto v___jp_330_;
}
}
}
}
v___jp_330_:
{
size_t v___x_332_; size_t v___x_333_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_328_, v___x_332_);
v_i_328_ = v___x_333_;
v_b_329_ = v_a_331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1___boxed(lean_object* v_declName_349_, lean_object* v_as_350_, lean_object* v_sz_351_, lean_object* v_i_352_, lean_object* v_b_353_){
_start:
{
size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v_sz_boxed_354_ = lean_unbox_usize(v_sz_351_);
lean_dec(v_sz_351_);
v_i_boxed_355_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_349_, v_as_350_, v_sz_boxed_354_, v_i_boxed_355_, v_b_353_);
lean_dec_ref(v_as_350_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_box(1);
v___x_358_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(lean_object* v_env_359_, lean_object* v_declName_360_){
_start:
{
lean_object* v___x_361_; lean_object* v_toEnvExtension_362_; lean_object* v_asyncMode_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_importedEntries_368_; lean_object* v_spellings_369_; size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_361_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
v_toEnvExtension_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_toEnvExtension_362_);
v_asyncMode_363_ = lean_ctor_get(v_toEnvExtension_362_, 2);
lean_inc(v_asyncMode_363_);
v___x_364_ = lean_box(1);
v___x_365_ = lean_obj_once(&l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0, &l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0_once, _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0);
v___x_366_ = lean_box(0);
lean_inc_ref(v_env_359_);
v___x_367_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_365_, v_toEnvExtension_362_, v_env_359_, v_asyncMode_363_, v___x_366_);
lean_dec_ref(v_toEnvExtension_362_);
v_importedEntries_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_importedEntries_368_);
lean_dec(v___x_367_);
v_spellings_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
v_sz_370_ = lean_array_size(v_importedEntries_368_);
v___x_371_ = ((size_t)0ULL);
lean_inc(v_declName_360_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_360_, v_importedEntries_368_, v_sz_370_, v___x_371_, v_spellings_369_);
lean_dec_ref(v_importedEntries_368_);
v___x_373_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_364_, v___x_361_, v_env_359_, v_asyncMode_363_, v___x_366_);
lean_dec(v_asyncMode_363_);
v___x_374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_373_, v_declName_360_);
lean_dec(v_declName_360_);
lean_dec(v___x_373_);
if (lean_obj_tag(v___x_374_) == 1)
{
lean_object* v_val_375_; lean_object* v___x_376_; 
v_val_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_val_375_);
lean_dec_ref(v___x_374_);
v___x_376_ = l_Array_append___redArg(v___x_372_, v_val_375_);
lean_dec(v_val_375_);
return v___x_376_;
}
else
{
lean_dec(v___x_374_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(lean_object* v_as_377_, lean_object* v_k_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_377_, v_k_378_, v_x_379_, v_x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___boxed(lean_object* v_as_383_, lean_object* v_k_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(v_as_383_, v_k_384_, v_x_385_, v_x_386_, v_x_387_);
lean_dec_ref(v_k_384_);
lean_dec_ref(v_as_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(lean_object* v_s_389_, lean_object* v_pos_390_){
_start:
{
lean_object* v_str_391_; lean_object* v_startInclusive_392_; lean_object* v_endExclusive_393_; lean_object* v___x_394_; uint8_t v___y_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_str_391_ = lean_ctor_get(v_s_389_, 0);
v_startInclusive_392_ = lean_ctor_get(v_s_389_, 1);
v_endExclusive_393_ = lean_ctor_get(v_s_389_, 2);
v___x_394_ = lean_nat_add(v_startInclusive_392_, v_pos_390_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_nat_sub(v_endExclusive_393_, v___x_394_);
v___x_405_ = lean_nat_dec_eq(v___x_403_, v___x_404_);
lean_dec(v___x_404_);
if (v___x_405_ == 0)
{
uint32_t v___x_406_; uint8_t v___y_408_; uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_406_ = lean_string_utf8_get_fast(v_str_391_, v___x_394_);
v___x_413_ = 32;
v___x_414_ = lean_uint32_dec_eq(v___x_406_, v___x_413_);
if (v___x_414_ == 0)
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 9;
v___x_416_ = lean_uint32_dec_eq(v___x_406_, v___x_415_);
v___y_408_ = v___x_416_;
goto v___jp_407_;
}
else
{
v___y_408_ = v___x_414_;
goto v___jp_407_;
}
v___jp_407_:
{
if (v___y_408_ == 0)
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 13;
v___x_410_ = lean_uint32_dec_eq(v___x_406_, v___x_409_);
if (v___x_410_ == 0)
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 10;
v___x_412_ = lean_uint32_dec_eq(v___x_406_, v___x_411_);
v___y_402_ = v___x_412_;
goto v___jp_401_;
}
else
{
v___y_402_ = v___x_410_;
goto v___jp_401_;
}
}
else
{
goto v___jp_395_;
}
}
}
else
{
lean_dec(v___x_394_);
return v_pos_390_;
}
v___jp_395_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_396_ = lean_string_utf8_next_fast(v_str_391_, v___x_394_);
v___x_397_ = lean_nat_sub(v___x_396_, v___x_394_);
lean_dec(v___x_394_);
v___x_398_ = lean_nat_add(v_pos_390_, v___x_397_);
lean_dec(v___x_397_);
v___x_399_ = lean_nat_dec_lt(v_pos_390_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec(v___x_398_);
return v_pos_390_;
}
else
{
lean_dec(v_pos_390_);
v_pos_390_ = v___x_398_;
goto _start;
}
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
lean_dec(v___x_394_);
return v_pos_390_;
}
else
{
goto v___jp_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0___boxed(lean_object* v_s_417_, lean_object* v_pos_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v_s_417_, v_pos_418_);
lean_dec_ref(v_s_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(lean_object* v_str_422_){
_start:
{
lean_object* v___y_424_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_string_utf8_byte_size(v_str_422_);
lean_inc_ref(v_str_422_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v_str_422_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
v___x_430_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v___x_429_, v___x_427_);
lean_dec_ref(v___x_429_);
v___x_431_ = lean_nat_sub(v___x_428_, v___x_430_);
lean_dec(v___x_430_);
v___x_432_ = lean_nat_dec_eq(v___x_431_, v___x_427_);
lean_dec(v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1));
v___x_434_ = lean_string_append(v___x_433_, v_str_422_);
lean_dec_ref(v_str_422_);
v___y_424_ = v___x_434_;
goto v___jp_423_;
}
else
{
v___y_424_ = v_str_422_;
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0));
v___x_426_ = lean_string_append(v___y_424_, v___x_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(lean_object* v_s_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0));
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___boxed(lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v_s_439_);
lean_dec_ref(v_s_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(lean_object* v_val_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v_a_444_, lean_object* v_b_445_){
_start:
{
lean_object* v_it_447_; lean_object* v_startInclusive_448_; lean_object* v_endExclusive_449_; 
if (lean_obj_tag(v_a_444_) == 0)
{
lean_object* v_currPos_454_; lean_object* v_searcher_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_481_; 
v_currPos_454_ = lean_ctor_get(v_a_444_, 0);
v_searcher_455_ = lean_ctor_get(v_a_444_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_481_ == 0)
{
v___x_457_ = v_a_444_;
v_isShared_458_ = v_isSharedCheck_481_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_searcher_455_);
lean_inc(v_currPos_454_);
lean_dec(v_a_444_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_481_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_startInclusive_459_; lean_object* v_endExclusive_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_startInclusive_459_ = lean_ctor_get(v___x_442_, 1);
v_endExclusive_460_ = lean_ctor_get(v___x_442_, 2);
v___x_461_ = lean_nat_sub(v_endExclusive_460_, v_startInclusive_459_);
v___x_462_ = lean_nat_dec_eq(v_searcher_455_, v___x_461_);
lean_dec(v___x_461_);
if (v___x_462_ == 0)
{
uint32_t v___x_463_; uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_463_ = 10;
v___x_464_ = lean_string_utf8_get_fast(v_val_441_, v_searcher_455_);
v___x_465_ = lean_uint32_dec_eq(v___x_464_, v___x_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_string_utf8_next_fast(v_val_441_, v_searcher_455_);
lean_dec(v_searcher_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_466_);
v___x_468_ = v___x_457_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_currPos_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v_a_444_ = v___x_468_;
goto _start;
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_slice_474_; lean_object* v_nextIt_476_; 
v___x_471_ = lean_string_utf8_next_fast(v_val_441_, v_searcher_455_);
v___x_472_ = lean_nat_sub(v___x_471_, v_searcher_455_);
v___x_473_ = lean_nat_add(v_searcher_455_, v___x_472_);
lean_dec(v___x_472_);
v_slice_474_ = l_String_Slice_subslice_x21(v___x_442_, v_currPos_454_, v_searcher_455_);
lean_inc(v___x_473_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_473_);
lean_ctor_set(v___x_457_, 0, v___x_473_);
v_nextIt_476_ = v___x_457_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_473_);
v_nextIt_476_ = v_reuseFailAlloc_479_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v_startInclusive_477_; lean_object* v_endExclusive_478_; 
v_startInclusive_477_ = lean_ctor_get(v_slice_474_, 0);
lean_inc(v_startInclusive_477_);
v_endExclusive_478_ = lean_ctor_get(v_slice_474_, 1);
lean_inc(v_endExclusive_478_);
lean_dec_ref(v_slice_474_);
v_it_447_ = v_nextIt_476_;
v_startInclusive_448_ = v_startInclusive_477_;
v_endExclusive_449_ = v_endExclusive_478_;
goto v___jp_446_;
}
}
}
else
{
lean_object* v___x_480_; 
lean_del_object(v___x_457_);
lean_dec(v_searcher_455_);
v___x_480_ = lean_box(1);
lean_inc(v___x_443_);
v_it_447_ = v___x_480_;
v_startInclusive_448_ = v_currPos_454_;
v_endExclusive_449_ = v___x_443_;
goto v___jp_446_;
}
}
}
else
{
lean_dec(v___x_443_);
lean_dec_ref(v_val_441_);
return v_b_445_;
}
v___jp_446_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc_ref(v_val_441_);
v___x_450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_450_, 0, v_val_441_);
lean_ctor_set(v___x_450_, 1, v_startInclusive_448_);
lean_ctor_set(v___x_450_, 2, v_endExclusive_449_);
v___x_451_ = l_String_Slice_toString(v___x_450_);
lean_dec_ref(v___x_450_);
v___x_452_ = lean_array_push(v_b_445_, v___x_451_);
v_a_444_ = v_it_447_;
v_b_445_ = v___x_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg___boxed(lean_object* v_val_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_482_, v___x_483_, v___x_484_, v_a_485_, v_b_486_);
lean_dec_ref(v___x_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
if (lean_obj_tag(v_a_488_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = l_List_reverse___redArg(v_a_489_);
return v___x_490_;
}
else
{
lean_object* v_head_491_; lean_object* v_tail_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_501_; 
v_head_491_ = lean_ctor_get(v_a_488_, 0);
v_tail_492_ = lean_ctor_get(v_a_488_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_501_ == 0)
{
v___x_494_ = v_a_488_;
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_tail_492_);
lean_inc(v_head_491_);
lean_dec(v_a_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(v_head_491_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v_a_489_);
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_a_489_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
v_a_488_ = v_tail_492_;
v_a_489_ = v___x_498_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(lean_object* v_s_502_, lean_object* v_pos_503_){
_start:
{
lean_object* v_str_504_; lean_object* v_startInclusive_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_str_504_ = lean_ctor_get(v_s_502_, 0);
v_startInclusive_505_ = lean_ctor_get(v_s_502_, 1);
v___x_506_ = lean_nat_add(v_startInclusive_505_, v_pos_503_);
v___x_507_ = lean_nat_sub(v___x_506_, v_startInclusive_505_);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_nat_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___y_518_; lean_object* v___x_519_; uint32_t v___x_520_; uint8_t v___y_522_; uint32_t v___x_527_; uint8_t v___x_528_; 
lean_inc(v_startInclusive_505_);
lean_inc_ref(v_str_504_);
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v_str_504_);
lean_ctor_set(v___x_510_, 1, v_startInclusive_505_);
lean_ctor_set(v___x_510_, 2, v___x_506_);
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_sub(v___x_507_, v___x_511_);
lean_dec(v___x_507_);
v___x_513_ = l_String_Slice_posLE(v___x_510_, v___x_512_);
lean_dec_ref(v___x_510_);
v___x_519_ = lean_nat_add(v_startInclusive_505_, v___x_513_);
v___x_520_ = lean_string_utf8_get_fast(v_str_504_, v___x_519_);
lean_dec(v___x_519_);
v___x_527_ = 32;
v___x_528_ = lean_uint32_dec_eq(v___x_520_, v___x_527_);
if (v___x_528_ == 0)
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 9;
v___x_530_ = lean_uint32_dec_eq(v___x_520_, v___x_529_);
v___y_522_ = v___x_530_;
goto v___jp_521_;
}
else
{
v___y_522_ = v___x_528_;
goto v___jp_521_;
}
v___jp_514_:
{
uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_lt(v___x_513_, v_pos_503_);
if (v___x_515_ == 0)
{
lean_dec(v___x_513_);
return v_pos_503_;
}
else
{
lean_dec(v_pos_503_);
v_pos_503_ = v___x_513_;
goto _start;
}
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_dec(v___x_513_);
return v_pos_503_;
}
else
{
goto v___jp_514_;
}
}
v___jp_521_:
{
if (v___y_522_ == 0)
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 13;
v___x_524_ = lean_uint32_dec_eq(v___x_520_, v___x_523_);
if (v___x_524_ == 0)
{
uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 10;
v___x_526_ = lean_uint32_dec_eq(v___x_520_, v___x_525_);
v___y_518_ = v___x_526_;
goto v___jp_517_;
}
else
{
v___y_518_ = v___x_524_;
goto v___jp_517_;
}
}
else
{
goto v___jp_514_;
}
}
}
else
{
lean_dec(v___x_507_);
lean_dec(v___x_506_);
return v_pos_503_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2___boxed(lean_object* v_s_531_, lean_object* v_pos_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v_s_531_, v_pos_532_);
lean_dec_ref(v_s_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
return v_x_534_;
}
else
{
lean_object* v_head_536_; lean_object* v_tail_537_; lean_object* v___x_538_; 
v_head_536_ = lean_ctor_get(v_x_535_, 0);
v_tail_537_ = lean_ctor_get(v_x_535_, 1);
v___x_538_ = lean_string_append(v_x_534_, v_head_536_);
v_x_534_ = v___x_538_;
v_x_535_ = v_tail_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4___boxed(lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v_x_540_, v_x_541_);
lean_dec(v_x_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(lean_object* v_spelling_553_){
_start:
{
lean_object* v_notation_554_; lean_object* v_recommendedSpelling_555_; lean_object* v_additionalInformation_x3f_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_601_; 
v_notation_554_ = lean_ctor_get(v_spelling_553_, 0);
v_recommendedSpelling_555_ = lean_ctor_get(v_spelling_553_, 1);
v_additionalInformation_x3f_556_ = lean_ctor_get(v_spelling_553_, 2);
v_isSharedCheck_601_ = !lean_is_exclusive(v_spelling_553_);
if (v_isSharedCheck_601_ == 0)
{
v___x_558_ = v_spelling_553_;
v_isShared_559_ = v_isSharedCheck_601_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_additionalInformation_x3f_556_);
lean_inc(v_recommendedSpelling_555_);
lean_inc(v_notation_554_);
lean_dec(v_spelling_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_601_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_firstLine_566_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0));
v___x_561_ = lean_string_append(v___x_560_, v_notation_554_);
lean_dec_ref(v_notation_554_);
v___x_562_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1));
v___x_563_ = lean_string_append(v___x_561_, v___x_562_);
v___x_564_ = lean_string_append(v___x_563_, v_recommendedSpelling_555_);
lean_dec_ref(v_recommendedSpelling_555_);
v___x_565_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2));
v_firstLine_566_ = lean_string_append(v___x_564_, v___x_565_);
if (lean_obj_tag(v_additionalInformation_x3f_556_) == 0)
{
lean_del_object(v___x_558_);
goto v___jp_567_;
}
else
{
lean_object* v_val_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v_val_570_ = lean_ctor_get(v_additionalInformation_x3f_556_, 0);
lean_inc(v_val_570_);
lean_dec_ref(v_additionalInformation_x3f_556_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_string_utf8_byte_size(v_val_570_);
lean_inc(v_val_570_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 2, v___x_572_);
lean_ctor_set(v___x_558_, 1, v___x_571_);
lean_ctor_set(v___x_558_, 0, v_val_570_);
v___x_574_ = v___x_558_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_val_570_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v___x_572_);
v___x_574_ = v_reuseFailAlloc_600_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4));
v___x_577_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_570_, v___x_574_, v___x_572_, v___x_575_, v___x_576_);
lean_dec_ref(v___x_574_);
v___x_578_ = lean_array_to_list(v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
goto v___jp_567_;
}
else
{
lean_object* v_tail_579_; 
v_tail_579_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_tail_579_);
if (lean_obj_tag(v_tail_579_) == 0)
{
lean_object* v_head_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_head_580_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_head_580_);
lean_dec_ref(v___x_578_);
v___x_581_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5));
v___x_582_ = lean_string_utf8_byte_size(v_head_580_);
lean_inc(v_head_580_);
v___x_583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_583_, 0, v_head_580_);
lean_ctor_set(v___x_583_, 1, v___x_571_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
v___x_584_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_583_, v___x_582_);
lean_dec_ref(v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v_head_580_);
lean_ctor_set(v___x_585_, 1, v___x_571_);
lean_ctor_set(v___x_585_, 2, v___x_584_);
v___x_586_ = l_String_Slice_toString(v___x_585_);
lean_dec_ref(v___x_585_);
v___x_587_ = lean_string_append(v___x_581_, v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6));
v___x_589_ = lean_string_append(v___x_587_, v___x_588_);
v___x_590_ = lean_string_append(v_firstLine_566_, v___x_589_);
lean_dec_ref(v___x_589_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_tail_579_);
v___x_591_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3));
v___x_592_ = lean_string_append(v_firstLine_566_, v___x_591_);
v___x_593_ = lean_box(0);
v___x_594_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(v___x_578_, v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
v___x_596_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_595_, v___x_594_);
lean_dec(v___x_594_);
v___x_597_ = lean_string_append(v___x_592_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
return v___x_599_;
}
}
}
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3));
v___x_569_ = lean_string_append(v_firstLine_566_, v___x_568_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(lean_object* v_val_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v_inst_605_, lean_object* v_R_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_602_, v___x_603_, v___x_604_, v_a_607_, v_b_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___boxed(lean_object* v_val_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_inst_613_, lean_object* v_R_614_, lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(v_val_610_, v___x_611_, v___x_612_, v_inst_613_, v_R_614_, v_a_615_, v_b_616_);
lean_dec_ref(v___x_611_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
if (lean_obj_tag(v_a_618_) == 0)
{
lean_object* v___x_620_; 
v___x_620_ = l_List_reverse___redArg(v_a_619_);
return v___x_620_;
}
else
{
lean_object* v_head_621_; lean_object* v_tail_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_631_; 
v_head_621_ = lean_ctor_get(v_a_618_, 0);
v_tail_622_ = lean_ctor_get(v_a_618_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_631_ == 0)
{
v___x_624_ = v_a_618_;
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_tail_622_);
lean_inc(v_head_621_);
lean_dec(v_a_618_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(v_head_621_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_a_619_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_a_619_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_a_618_ = v_tail_622_;
v_a_619_ = v___x_628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object* v_env_633_, lean_object* v_declName_634_){
_start:
{
lean_object* v_spellings_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_spellings_635_ = l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(v_env_633_, v_declName_634_);
v___x_636_ = lean_array_get_size(v_spellings_635_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_nat_dec_eq(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_639_ = ((lean_object*)(l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0));
v___x_640_ = lean_array_to_list(v_spellings_635_);
v___x_641_ = lean_box(0);
v___x_642_ = l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(v___x_640_, v___x_641_);
v___x_643_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
v___x_644_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_643_, v___x_642_);
lean_dec(v___x_642_);
v___x_645_ = lean_string_append(v___x_639_, v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = lean_string_utf8_byte_size(v___x_645_);
lean_inc_ref(v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_637_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
v___x_648_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_647_, v___x_646_);
lean_dec_ref(v___x_647_);
v___x_649_ = lean_string_utf8_extract(v___x_645_, v___x_637_, v___x_648_);
lean_dec(v___x_648_);
lean_dec_ref(v___x_645_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; 
lean_dec_ref(v_spellings_635_);
v___x_650_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
return v___x_650_;
}
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt);
lean_dec_ref(res);
res = l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
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
