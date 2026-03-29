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
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_Term_Doc_initFn___closed__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_Term_Doc_initFn___closed__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_x_95_, lean_object* v_s_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_99_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_98_, v_s_96_);
v___x_105_ = lean_array_get_size(v___x_99_);
v___x_106_ = lean_nat_dec_eq(v___x_105_, v___x_97_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___y_110_; uint8_t v___x_112_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_sub(v___x_105_, v___x_107_);
v___x_112_ = lean_nat_dec_le(v___x_97_, v___x_108_);
if (v___x_112_ == 0)
{
lean_inc(v___x_108_);
v___y_110_ = v___x_108_;
goto v___jp_109_;
}
else
{
v___y_110_ = v___x_97_;
goto v___jp_109_;
}
v___jp_109_:
{
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_le(v___y_110_, v___x_108_);
if (v___x_111_ == 0)
{
lean_dec(v___x_108_);
lean_inc(v___y_110_);
v___y_101_ = v___y_110_;
v___y_102_ = v___y_110_;
goto v___jp_100_;
}
else
{
v___y_101_ = v___y_110_;
v___y_102_ = v___x_108_;
goto v___jp_100_;
}
}
}
else
{
lean_object* v___x_113_; 
lean_inc_ref_n(v___x_99_, 2);
v___x_113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_99_);
lean_ctor_set(v___x_113_, 1, v___x_99_);
lean_ctor_set(v___x_113_, 2, v___x_99_);
return v___x_113_;
}
v___jp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_99_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_inc_ref_n(v___x_103_, 2);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_x_114_, lean_object* v_s_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_114_, v_s_115_);
lean_dec(v_s_115_);
lean_dec_ref(v_x_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_x_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_x_119_);
lean_dec(v_x_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v_es_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_124_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v___x_123_, v_es_121_);
v___x_125_ = lean_array_get_size(v___x_124_);
v___x_126_ = lean_nat_dec_eq(v___x_125_, v___x_122_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___y_130_; uint8_t v___x_134_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_sub(v___x_125_, v___x_127_);
v___x_134_ = lean_nat_dec_le(v___x_122_, v___x_128_);
if (v___x_134_ == 0)
{
lean_inc(v___x_128_);
v___y_130_ = v___x_128_;
goto v___jp_129_;
}
else
{
v___y_130_ = v___x_122_;
goto v___jp_129_;
}
v___jp_129_:
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_le(v___y_130_, v___x_128_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec(v___x_128_);
lean_inc(v___y_130_);
v___x_132_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_124_, v___y_130_, v___y_130_);
lean_dec(v___y_130_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v___x_124_, v___y_130_, v___x_128_);
lean_dec(v___x_128_);
return v___x_133_;
}
}
}
else
{
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_es_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v_es_135_);
lean_dec(v_es_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v___x_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v___x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(lean_object* v___x_143_, lean_object* v_x_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_143_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v___x_148_, lean_object* v_x_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Parser_Term_Doc_initFn___lam__5_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(v___x_148_, v_x_149_, v___y_150_);
lean_dec_ref(v___y_150_);
lean_dec_ref(v_x_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___closed__13_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_));
v___x_186_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2____boxed(lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2_();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(lean_object* v_init_189_, lean_object* v_t_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0_spec__0(v_init_189_, v_t_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_192_, lean_object* v_t_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__0(v_init_192_, v_t_193_);
lean_dec(v_t_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(lean_object* v_n_195_, lean_object* v_as_196_, lean_object* v_lo_197_, lean_object* v_hi_198_, lean_object* v_w_199_, lean_object* v_hlo_200_, lean_object* v_hhi_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg(v_as_196_, v_lo_197_, v_hi_198_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_203_, lean_object* v_as_204_, lean_object* v_lo_205_, lean_object* v_hi_206_, lean_object* v_w_207_, lean_object* v_hlo_208_, lean_object* v_hhi_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1(v_n_203_, v_as_204_, v_lo_205_, v_hi_206_, v_w_207_, v_hlo_208_, v_hhi_209_);
lean_dec(v_hi_206_);
lean_dec(v_n_203_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_211_, lean_object* v_t_212_, lean_object* v_k_213_, lean_object* v_fallback_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___redArg(v_t_212_, v_k_213_, v_fallback_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_216_, lean_object* v_t_217_, lean_object* v_k_218_, lean_object* v_fallback_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__2(v_00_u03b4_216_, v_t_217_, v_k_218_, v_fallback_219_);
lean_dec(v_fallback_219_);
lean_dec(v_k_218_);
lean_dec(v_t_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___y_221_){
_start:
{
lean_inc_ref(v___y_221_);
return v___y_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Parser_Term_Doc_initFn___lam__0_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___y_222_);
lean_dec_ref(v___y_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v_x_224_, lean_object* v_s_225_){
_start:
{
lean_object* v___x_226_; 
lean_inc_ref_n(v_s_225_, 2);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v_s_225_);
lean_ctor_set(v___x_226_, 1, v_s_225_);
lean_ctor_set(v___x_226_, 2, v_s_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_x_227_, lean_object* v_s_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Parser_Term_Doc_initFn___lam__1_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_227_, v_s_228_);
lean_dec_ref(v_x_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Parser_Term_Doc_initFn___lam__2_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v_x_232_);
lean_dec_ref(v_x_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___x_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___x_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Parser_Term_Doc_initFn___lam__3_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(lean_object* v___x_240_, lean_object* v_x_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_240_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v___x_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Parser_Term_Doc_initFn___lam__4_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(v___x_245_, v_x_246_, v___y_247_);
lean_dec_ref(v___y_247_);
lean_dec_ref(v_x_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_Parser_Term_Doc_initFn___closed__10_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_));
v___x_281_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2____boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_205972326____hygCtx___hyg_2_();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_addRecommendedSpelling(lean_object* v_env_284_, lean_object* v_rec_285_, lean_object* v_names_286_){
_start:
{
lean_object* v___x_287_; lean_object* v_toEnvExtension_288_; lean_object* v_asyncMode_289_; lean_object* v___x_290_; lean_object* v_toEnvExtension_291_; lean_object* v_asyncMode_292_; lean_object* v___x_293_; lean_object* v_env_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_287_ = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
v_toEnvExtension_288_ = lean_ctor_get(v___x_287_, 0);
v_asyncMode_289_ = lean_ctor_get(v_toEnvExtension_288_, 2);
v___x_290_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
v_toEnvExtension_291_ = lean_ctor_get(v___x_290_, 0);
v_asyncMode_292_ = lean_ctor_get(v_toEnvExtension_291_, 2);
v___x_293_ = lean_box(0);
lean_inc_ref(v_rec_285_);
v_env_294_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_287_, v_env_284_, v_rec_285_, v_asyncMode_289_, v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_rec_285_);
lean_ctor_set(v___x_295_, 1, v_names_286_);
v___x_296_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_290_, v_env_294_, v___x_295_, v_asyncMode_292_, v___x_293_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(lean_object* v_as_297_, lean_object* v_k_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_m_303_; lean_object* v_a_304_; uint8_t v___x_305_; 
v___x_301_ = lean_nat_add(v_x_299_, v_x_300_);
v___x_302_ = lean_unsigned_to_nat(1u);
v_m_303_ = lean_nat_shiftr(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
v_a_304_ = lean_array_fget_borrowed(v_as_297_, v_m_303_);
v___x_305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_304_, v_k_298_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
lean_dec(v_x_300_);
v___x_306_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_298_, v_a_304_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_dec(v_m_303_);
lean_dec(v_x_299_);
lean_inc(v_a_304_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v_a_304_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_nat_dec_eq(v_m_303_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_nat_sub(v_m_303_, v___x_302_);
lean_dec(v_m_303_);
v___x_311_ = lean_nat_dec_lt(v___x_310_, v_x_299_);
if (v___x_311_ == 0)
{
v_x_300_ = v___x_310_;
goto _start;
}
else
{
lean_object* v___x_313_; 
lean_dec(v___x_310_);
lean_dec(v_x_299_);
v___x_313_ = lean_box(0);
return v___x_313_;
}
}
else
{
lean_object* v___x_314_; 
lean_dec(v_m_303_);
lean_dec(v_x_299_);
v___x_314_ = lean_box(0);
return v___x_314_;
}
}
}
else
{
lean_object* v___x_315_; uint8_t v___x_316_; 
lean_dec(v_x_299_);
v___x_315_ = lean_nat_add(v_m_303_, v___x_302_);
lean_dec(v_m_303_);
v___x_316_ = lean_nat_dec_le(v___x_315_, v_x_300_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v___x_315_);
lean_dec(v_x_300_);
v___x_317_ = lean_box(0);
return v___x_317_;
}
else
{
v_x_299_ = v___x_315_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg___boxed(lean_object* v_as_319_, lean_object* v_k_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_319_, v_k_320_, v_x_321_, v_x_322_);
lean_dec_ref(v_k_320_);
lean_dec_ref(v_as_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(lean_object* v_declName_324_, lean_object* v_as_325_, size_t v_sz_326_, size_t v_i_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_a_330_; uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_334_ == 0)
{
lean_dec(v_declName_324_);
return v_b_328_;
}
else
{
lean_object* v___x_335_; lean_object* v_a_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v_a_336_ = lean_array_uget_borrowed(v_as_325_, v_i_327_);
v___x_337_ = lean_array_get_size(v_a_336_);
v___x_338_ = lean_nat_dec_lt(v___x_335_, v___x_337_);
if (v___x_338_ == 0)
{
v_a_330_ = v_b_328_;
goto v___jp_329_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_sub(v___x_337_, v___x_339_);
v___x_341_ = lean_nat_dec_le(v___x_335_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v___x_340_);
v_a_330_ = v_b_328_;
goto v___jp_329_;
}
else
{
lean_object* v_spellings_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_spellings_342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
lean_inc(v_declName_324_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_declName_324_);
lean_ctor_set(v___x_343_, 1, v_spellings_342_);
v___x_344_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_a_336_, v___x_343_, v___x_335_, v___x_340_);
lean_dec_ref(v___x_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v_snd_346_; lean_object* v___x_347_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___x_344_);
v_snd_346_ = lean_ctor_get(v_val_345_, 1);
lean_inc(v_snd_346_);
lean_dec(v_val_345_);
v___x_347_ = l_Array_append___redArg(v_b_328_, v_snd_346_);
lean_dec(v_snd_346_);
v_a_330_ = v___x_347_;
goto v___jp_329_;
}
else
{
lean_dec(v___x_344_);
v_a_330_ = v_b_328_;
goto v___jp_329_;
}
}
}
}
v___jp_329_:
{
size_t v___x_331_; size_t v___x_332_; 
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_327_, v___x_331_);
v_i_327_ = v___x_332_;
v_b_328_ = v_a_330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1___boxed(lean_object* v_declName_348_, lean_object* v_as_349_, lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_b_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_354_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_348_, v_as_349_, v_sz_boxed_353_, v_i_boxed_354_, v_b_352_);
lean_dec_ref(v_as_349_);
return v_res_355_;
}
}
static lean_object* _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_box(1);
v___x_357_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(lean_object* v_env_358_, lean_object* v_declName_359_){
_start:
{
lean_object* v___x_360_; lean_object* v_toEnvExtension_361_; lean_object* v_asyncMode_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_importedEntries_367_; lean_object* v_spellings_368_; size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_360_ = l_Lean_Parser_Term_Doc_recommendedSpellingByNameExt;
v_toEnvExtension_361_ = lean_ctor_get(v___x_360_, 0);
v_asyncMode_362_ = lean_ctor_get(v_toEnvExtension_361_, 2);
v___x_363_ = lean_box(1);
v___x_364_ = lean_obj_once(&l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0, &l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0_once, _init_l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName___closed__0);
v___x_365_ = lean_box(0);
lean_inc_ref(v_env_358_);
v___x_366_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_364_, v_toEnvExtension_361_, v_env_358_, v_asyncMode_362_, v___x_365_);
v_importedEntries_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_importedEntries_367_);
lean_dec(v___x_366_);
v_spellings_368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Term_Doc_initFn_00___x40_Lean_Parser_Term_Doc_383197578____hygCtx___hyg_2__spec__3___closed__0));
v_sz_369_ = lean_array_size(v_importedEntries_367_);
v___x_370_ = ((size_t)0ULL);
lean_inc(v_declName_359_);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__1(v_declName_359_, v_importedEntries_367_, v_sz_369_, v___x_370_, v_spellings_368_);
lean_dec_ref(v_importedEntries_367_);
v___x_372_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_363_, v___x_360_, v_env_358_, v_asyncMode_362_, v___x_365_);
v___x_373_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_372_, v_declName_359_);
lean_dec(v_declName_359_);
lean_dec(v___x_372_);
if (lean_obj_tag(v___x_373_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_375_; 
v_val_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_374_);
lean_dec_ref(v___x_373_);
v___x_375_ = l_Array_append___redArg(v___x_371_, v_val_374_);
lean_dec(v_val_374_);
return v___x_375_;
}
else
{
lean_dec(v___x_373_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(lean_object* v_as_376_, lean_object* v_k_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___redArg(v_as_376_, v_k_377_, v_x_378_, v_x_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0___boxed(lean_object* v_as_382_, lean_object* v_k_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Array_binSearchAux___at___00Lean_Parser_Term_Doc_getRecommendedSpellingsForName_spec__0(v_as_382_, v_k_383_, v_x_384_, v_x_385_, v_x_386_);
lean_dec_ref(v_k_383_);
lean_dec_ref(v_as_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(lean_object* v_s_388_, lean_object* v_pos_389_){
_start:
{
lean_object* v_str_390_; lean_object* v_startInclusive_391_; lean_object* v_endExclusive_392_; lean_object* v___x_393_; uint8_t v___y_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_str_390_ = lean_ctor_get(v_s_388_, 0);
v_startInclusive_391_ = lean_ctor_get(v_s_388_, 1);
v_endExclusive_392_ = lean_ctor_get(v_s_388_, 2);
v___x_393_ = lean_nat_add(v_startInclusive_391_, v_pos_389_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_nat_sub(v_endExclusive_392_, v___x_393_);
v___x_404_ = lean_nat_dec_eq(v___x_402_, v___x_403_);
lean_dec(v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___y_407_; uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_405_ = lean_string_utf8_get_fast(v_str_390_, v___x_393_);
v___x_412_ = 32;
v___x_413_ = lean_uint32_dec_eq(v___x_405_, v___x_412_);
if (v___x_413_ == 0)
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 9;
v___x_415_ = lean_uint32_dec_eq(v___x_405_, v___x_414_);
v___y_407_ = v___x_415_;
goto v___jp_406_;
}
else
{
v___y_407_ = v___x_413_;
goto v___jp_406_;
}
v___jp_406_:
{
if (v___y_407_ == 0)
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 13;
v___x_409_ = lean_uint32_dec_eq(v___x_405_, v___x_408_);
if (v___x_409_ == 0)
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 10;
v___x_411_ = lean_uint32_dec_eq(v___x_405_, v___x_410_);
v___y_401_ = v___x_411_;
goto v___jp_400_;
}
else
{
v___y_401_ = v___x_409_;
goto v___jp_400_;
}
}
else
{
goto v___jp_394_;
}
}
}
else
{
lean_dec(v___x_393_);
return v_pos_389_;
}
v___jp_394_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_395_ = lean_string_utf8_next_fast(v_str_390_, v___x_393_);
v___x_396_ = lean_nat_sub(v___x_395_, v___x_393_);
lean_dec(v___x_393_);
v___x_397_ = lean_nat_add(v_pos_389_, v___x_396_);
lean_dec(v___x_396_);
v___x_398_ = l_String_instDecidableLtRaw___aux__1(v_pos_389_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec(v___x_397_);
return v_pos_389_;
}
else
{
lean_dec(v_pos_389_);
v_pos_389_ = v___x_397_;
goto _start;
}
}
v___jp_400_:
{
if (v___y_401_ == 0)
{
lean_dec(v___x_393_);
return v_pos_389_;
}
else
{
goto v___jp_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0___boxed(lean_object* v_s_416_, lean_object* v_pos_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v_s_416_, v_pos_417_);
lean_dec_ref(v_s_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(lean_object* v_str_421_){
_start:
{
lean_object* v___y_423_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_string_utf8_byte_size(v_str_421_);
lean_inc_ref(v_str_421_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v_str_421_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
v___x_429_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine_spec__0(v___x_428_, v___x_426_);
lean_dec_ref(v___x_428_);
v___x_430_ = lean_nat_sub(v___x_427_, v___x_429_);
lean_dec(v___x_429_);
v___x_431_ = lean_nat_dec_eq(v___x_430_, v___x_426_);
lean_dec(v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__1));
v___x_433_ = lean_string_append(v___x_432_, v_str_421_);
lean_dec_ref(v_str_421_);
v___y_423_ = v___x_433_;
goto v___jp_422_;
}
else
{
v___y_423_ = v_str_421_;
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine___closed__0));
v___x_425_ = lean_string_append(v___y_423_, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(lean_object* v_s_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___closed__0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0___boxed(lean_object* v_s_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v_s_438_);
lean_dec_ref(v_s_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(lean_object* v_val_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v_it_446_; lean_object* v_startInclusive_447_; lean_object* v_endExclusive_448_; 
if (lean_obj_tag(v_a_443_) == 0)
{
lean_object* v_currPos_453_; lean_object* v_searcher_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_480_; 
v_currPos_453_ = lean_ctor_get(v_a_443_, 0);
v_searcher_454_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_480_ == 0)
{
v___x_456_ = v_a_443_;
v_isShared_457_ = v_isSharedCheck_480_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_searcher_454_);
lean_inc(v_currPos_453_);
lean_dec(v_a_443_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_480_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_startInclusive_458_; lean_object* v_endExclusive_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_startInclusive_458_ = lean_ctor_get(v___x_441_, 1);
v_endExclusive_459_ = lean_ctor_get(v___x_441_, 2);
v___x_460_ = lean_nat_sub(v_endExclusive_459_, v_startInclusive_458_);
v___x_461_ = lean_nat_dec_eq(v_searcher_454_, v___x_460_);
lean_dec(v___x_460_);
if (v___x_461_ == 0)
{
uint32_t v___x_462_; uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = 10;
v___x_463_ = lean_string_utf8_get_fast(v_val_440_, v_searcher_454_);
v___x_464_ = lean_uint32_dec_eq(v___x_463_, v___x_462_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_string_utf8_next_fast(v_val_440_, v_searcher_454_);
lean_dec(v_searcher_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_465_);
v___x_467_ = v___x_456_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_currPos_453_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_469_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v_a_443_ = v___x_467_;
goto _start;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_slice_473_; lean_object* v_nextIt_475_; 
v___x_470_ = lean_string_utf8_next_fast(v_val_440_, v_searcher_454_);
v___x_471_ = lean_nat_sub(v___x_470_, v_searcher_454_);
v___x_472_ = lean_nat_add(v_searcher_454_, v___x_471_);
lean_dec(v___x_471_);
v_slice_473_ = l_String_Slice_subslice_x21(v___x_441_, v_currPos_453_, v_searcher_454_);
lean_inc(v___x_472_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_472_);
lean_ctor_set(v___x_456_, 0, v___x_472_);
v_nextIt_475_ = v___x_456_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_472_);
v_nextIt_475_ = v_reuseFailAlloc_478_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v_startInclusive_476_; lean_object* v_endExclusive_477_; 
v_startInclusive_476_ = lean_ctor_get(v_slice_473_, 0);
lean_inc(v_startInclusive_476_);
v_endExclusive_477_ = lean_ctor_get(v_slice_473_, 1);
lean_inc(v_endExclusive_477_);
lean_dec_ref(v_slice_473_);
v_it_446_ = v_nextIt_475_;
v_startInclusive_447_ = v_startInclusive_476_;
v_endExclusive_448_ = v_endExclusive_477_;
goto v___jp_445_;
}
}
}
else
{
lean_object* v___x_479_; 
lean_del_object(v___x_456_);
lean_dec(v_searcher_454_);
v___x_479_ = lean_box(1);
lean_inc(v___x_442_);
v_it_446_ = v___x_479_;
v_startInclusive_447_ = v_currPos_453_;
v_endExclusive_448_ = v___x_442_;
goto v___jp_445_;
}
}
}
else
{
lean_dec(v___x_442_);
lean_dec_ref(v_val_440_);
return v_b_444_;
}
v___jp_445_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc_ref(v_val_440_);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v_val_440_);
lean_ctor_set(v___x_449_, 1, v_startInclusive_447_);
lean_ctor_set(v___x_449_, 2, v_endExclusive_448_);
v___x_450_ = l_String_Slice_toString(v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_array_push(v_b_444_, v___x_450_);
v_a_443_ = v_it_446_;
v_b_444_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg___boxed(lean_object* v_val_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_481_, v___x_482_, v___x_483_, v_a_484_, v_b_485_);
lean_dec_ref(v___x_482_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
if (lean_obj_tag(v_a_487_) == 0)
{
lean_object* v___x_489_; 
v___x_489_ = l_List_reverse___redArg(v_a_488_);
return v___x_489_;
}
else
{
lean_object* v_head_490_; lean_object* v_tail_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
v_head_490_ = lean_ctor_get(v_a_487_, 0);
v_tail_491_ = lean_ctor_get(v_a_487_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_487_);
if (v_isSharedCheck_500_ == 0)
{
v___x_493_ = v_a_487_;
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_tail_491_);
lean_inc(v_head_490_);
lean_dec(v_a_487_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_indentLine(v_head_490_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v_a_488_);
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_488_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
v_a_487_ = v_tail_491_;
v_a_488_ = v___x_497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(lean_object* v_s_501_, lean_object* v_pos_502_){
_start:
{
lean_object* v_str_503_; lean_object* v_startInclusive_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_str_503_ = lean_ctor_get(v_s_501_, 0);
v_startInclusive_504_ = lean_ctor_get(v_s_501_, 1);
v___x_505_ = lean_nat_add(v_startInclusive_504_, v_pos_502_);
v___x_506_ = lean_nat_sub(v___x_505_, v_startInclusive_504_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_nat_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___y_517_; lean_object* v___x_518_; uint32_t v___x_519_; uint8_t v___y_521_; uint32_t v___x_526_; uint8_t v___x_527_; 
lean_inc(v_startInclusive_504_);
lean_inc_ref(v_str_503_);
v___x_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_509_, 0, v_str_503_);
lean_ctor_set(v___x_509_, 1, v_startInclusive_504_);
lean_ctor_set(v___x_509_, 2, v___x_505_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_sub(v___x_506_, v___x_510_);
lean_dec(v___x_506_);
v___x_512_ = l_String_Slice_posLE(v___x_509_, v___x_511_);
lean_dec_ref(v___x_509_);
v___x_518_ = lean_nat_add(v_startInclusive_504_, v___x_512_);
v___x_519_ = lean_string_utf8_get_fast(v_str_503_, v___x_518_);
lean_dec(v___x_518_);
v___x_526_ = 32;
v___x_527_ = lean_uint32_dec_eq(v___x_519_, v___x_526_);
if (v___x_527_ == 0)
{
uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 9;
v___x_529_ = lean_uint32_dec_eq(v___x_519_, v___x_528_);
v___y_521_ = v___x_529_;
goto v___jp_520_;
}
else
{
v___y_521_ = v___x_527_;
goto v___jp_520_;
}
v___jp_513_:
{
uint8_t v___x_514_; 
v___x_514_ = l_String_instDecidableLtRaw___aux__1(v___x_512_, v_pos_502_);
if (v___x_514_ == 0)
{
lean_dec(v___x_512_);
return v_pos_502_;
}
else
{
lean_dec(v_pos_502_);
v_pos_502_ = v___x_512_;
goto _start;
}
}
v___jp_516_:
{
if (v___y_517_ == 0)
{
lean_dec(v___x_512_);
return v_pos_502_;
}
else
{
goto v___jp_513_;
}
}
v___jp_520_:
{
if (v___y_521_ == 0)
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 13;
v___x_523_ = lean_uint32_dec_eq(v___x_519_, v___x_522_);
if (v___x_523_ == 0)
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 10;
v___x_525_ = lean_uint32_dec_eq(v___x_519_, v___x_524_);
v___y_517_ = v___x_525_;
goto v___jp_516_;
}
else
{
v___y_517_ = v___x_523_;
goto v___jp_516_;
}
}
else
{
goto v___jp_513_;
}
}
}
else
{
lean_dec(v___x_506_);
lean_dec(v___x_505_);
return v_pos_502_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2___boxed(lean_object* v_s_530_, lean_object* v_pos_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v_s_530_, v_pos_531_);
lean_dec_ref(v_s_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
return v_x_533_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; lean_object* v___x_537_; 
v_head_535_ = lean_ctor_get(v_x_534_, 0);
v_tail_536_ = lean_ctor_get(v_x_534_, 1);
v___x_537_ = lean_string_append(v_x_533_, v_head_535_);
v_x_533_ = v___x_537_;
v_x_534_ = v_tail_536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4___boxed(lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v_x_539_, v_x_540_);
lean_dec(v_x_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(lean_object* v_spelling_552_){
_start:
{
lean_object* v_notation_553_; lean_object* v_recommendedSpelling_554_; lean_object* v_additionalInformation_x3f_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_600_; 
v_notation_553_ = lean_ctor_get(v_spelling_552_, 0);
v_recommendedSpelling_554_ = lean_ctor_get(v_spelling_552_, 1);
v_additionalInformation_x3f_555_ = lean_ctor_get(v_spelling_552_, 2);
v_isSharedCheck_600_ = !lean_is_exclusive(v_spelling_552_);
if (v_isSharedCheck_600_ == 0)
{
v___x_557_ = v_spelling_552_;
v_isShared_558_ = v_isSharedCheck_600_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_additionalInformation_x3f_555_);
lean_inc(v_recommendedSpelling_554_);
lean_inc(v_notation_553_);
lean_dec(v_spelling_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_600_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_firstLine_565_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__0));
v___x_560_ = lean_string_append(v___x_559_, v_notation_553_);
lean_dec_ref(v_notation_553_);
v___x_561_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__1));
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
v___x_563_ = lean_string_append(v___x_562_, v_recommendedSpelling_554_);
lean_dec_ref(v_recommendedSpelling_554_);
v___x_564_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__2));
v_firstLine_565_ = lean_string_append(v___x_563_, v___x_564_);
if (lean_obj_tag(v_additionalInformation_x3f_555_) == 0)
{
lean_del_object(v___x_557_);
goto v___jp_566_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v_val_569_ = lean_ctor_get(v_additionalInformation_x3f_555_, 0);
lean_inc_n(v_val_569_, 2);
lean_dec_ref(v_additionalInformation_x3f_555_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_string_utf8_byte_size(v_val_569_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 2, v___x_571_);
lean_ctor_set(v___x_557_, 1, v___x_570_);
lean_ctor_set(v___x_557_, 0, v_val_569_);
v___x_573_ = v___x_557_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_val_569_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v___x_571_);
v___x_573_ = v_reuseFailAlloc_599_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(v___x_573_);
v___x_575_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__4));
v___x_576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_569_, v___x_573_, v___x_571_, v___x_574_, v___x_575_);
lean_dec_ref(v___x_573_);
v___x_577_ = lean_array_to_list(v___x_576_);
if (lean_obj_tag(v___x_577_) == 0)
{
goto v___jp_566_;
}
else
{
lean_object* v_tail_578_; 
v_tail_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_tail_578_);
if (lean_obj_tag(v_tail_578_) == 0)
{
lean_object* v_head_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_head_579_ = lean_ctor_get(v___x_577_, 0);
lean_inc_n(v_head_579_, 2);
lean_dec_ref(v___x_577_);
v___x_580_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__5));
v___x_581_ = lean_string_utf8_byte_size(v_head_579_);
v___x_582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_582_, 0, v_head_579_);
lean_ctor_set(v___x_582_, 1, v___x_570_);
lean_ctor_set(v___x_582_, 2, v___x_581_);
v___x_583_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_582_, v___x_581_);
lean_dec_ref(v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v_head_579_);
lean_ctor_set(v___x_584_, 1, v___x_570_);
lean_ctor_set(v___x_584_, 2, v___x_583_);
v___x_585_ = l_String_Slice_toString(v___x_584_);
lean_dec_ref(v___x_584_);
v___x_586_ = lean_string_append(v___x_580_, v___x_585_);
lean_dec_ref(v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__6));
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
v___x_589_ = lean_string_append(v_firstLine_565_, v___x_588_);
lean_dec_ref(v___x_588_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_tail_578_);
v___x_590_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3));
v___x_591_ = lean_string_append(v_firstLine_565_, v___x_590_);
v___x_592_ = lean_box(0);
v___x_593_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__3(v___x_577_, v___x_592_);
v___x_594_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
v___x_595_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_594_, v___x_593_);
lean_dec(v___x_593_);
v___x_596_ = lean_string_append(v___x_591_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__8));
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
return v___x_598_;
}
}
}
}
v___jp_566_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__3));
v___x_568_ = lean_string_append(v_firstLine_565_, v___x_567_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(lean_object* v_val_601_, lean_object* v___x_602_, lean_object* v___x_603_, lean_object* v_inst_604_, lean_object* v_R_605_, lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___redArg(v_val_601_, v___x_602_, v___x_603_, v_a_606_, v_b_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1___boxed(lean_object* v_val_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_inst_612_, lean_object* v_R_613_, lean_object* v_a_614_, lean_object* v_b_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__1(v_val_609_, v___x_610_, v___x_611_, v_inst_612_, v_R_613_, v_a_614_, v_b_615_);
lean_dec_ref(v___x_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
if (lean_obj_tag(v_a_617_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = l_List_reverse___redArg(v_a_618_);
return v___x_619_;
}
else
{
lean_object* v_head_620_; lean_object* v_tail_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_630_; 
v_head_620_ = lean_ctor_get(v_a_617_, 0);
v_tail_621_ = lean_ctor_get(v_a_617_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_630_ == 0)
{
v___x_623_ = v_a_617_;
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tail_621_);
lean_inc(v_head_620_);
lean_dec(v_a_617_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet(v_head_620_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_a_618_);
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_618_);
v___x_627_ = v_reuseFailAlloc_629_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_a_617_ = v_tail_621_;
v_a_618_ = v___x_627_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object* v_env_632_, lean_object* v_declName_633_){
_start:
{
lean_object* v_spellings_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_spellings_634_ = l_Lean_Parser_Term_Doc_getRecommendedSpellingsForName(v_env_632_, v_declName_633_);
v___x_635_ = lean_array_get_size(v_spellings_634_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_638_ = ((lean_object*)(l_Lean_Parser_Term_Doc_getRecommendedSpellingString___closed__0));
v___x_639_ = lean_array_to_list(v_spellings_634_);
v___x_640_ = lean_box(0);
v___x_641_ = l_List_mapTR_loop___at___00Lean_Parser_Term_Doc_getRecommendedSpellingString_spec__0(v___x_639_, v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
v___x_643_ = l_List_foldl___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__4(v___x_642_, v___x_641_);
lean_dec(v___x_641_);
v___x_644_ = lean_string_append(v___x_638_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = lean_string_utf8_byte_size(v___x_644_);
lean_inc_ref(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_636_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
v___x_647_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__2(v___x_646_, v___x_645_);
lean_dec_ref(v___x_646_);
v___x_648_ = lean_string_utf8_extract(v___x_644_, v___x_636_, v___x_647_);
lean_dec(v___x_647_);
lean_dec_ref(v___x_644_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
lean_dec_ref(v_spellings_634_);
v___x_649_ = ((lean_object*)(l___private_Lean_Parser_Term_Doc_0__Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet___closed__7));
return v___x_649_;
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
