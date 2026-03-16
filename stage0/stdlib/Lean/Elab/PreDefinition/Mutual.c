// Lean compiler output
// Module: Lean.Elab.PreDefinition.Mutual
// Imports: public import Lean.Elab.PreDefinition.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_filterAttrs(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_allowUnsafeReducibility;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1;
static lean_once_cell_t l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2;
static lean_once_cell_t l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instance_reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 180, 213, 185, 56, 77, 23, 14)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implicit_reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 100, 121, 167, 26, 160, 176, 156)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object* v_opts_15_, lean_object* v_opt_16_){
_start:
{
lean_object* v_name_17_; lean_object* v_defValue_18_; lean_object* v_map_19_; lean_object* v___x_20_; 
v_name_17_ = lean_ctor_get(v_opt_16_, 0);
v_defValue_18_ = lean_ctor_get(v_opt_16_, 1);
v_map_19_ = lean_ctor_get(v_opts_15_, 0);
v___x_20_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_19_, v_name_17_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
else
{
lean_object* v_val_21_; 
v_val_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref(v___x_20_);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref(v_val_21_);
return v_v_22_;
}
else
{
lean_dec(v_val_21_);
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object* v_opts_23_, lean_object* v_opt_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_opts_23_, v_opt_24_);
lean_dec_ref(v_opt_24_);
lean_dec_ref(v_opts_23_);
return v_res_25_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(lean_object* v_attr_29_){
_start:
{
lean_object* v_name_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_name_30_ = lean_ctor_get(v_attr_29_, 0);
v___x_31_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1));
v___x_32_ = lean_name_eq(v_name_30_, v___x_31_);
if (v___x_32_ == 0)
{
uint8_t v___x_33_; 
v___x_33_ = 1;
return v___x_33_;
}
else
{
uint8_t v___x_34_; 
v___x_34_ = 0;
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(lean_object* v_attr_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(v_attr_35_);
lean_dec_ref(v_attr_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(uint8_t v_flag_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v_infoState_42_; lean_object* v_env_43_; lean_object* v_nextMacroScope_44_; lean_object* v_ngen_45_; lean_object* v_auxDeclNGen_46_; lean_object* v_traceState_47_; lean_object* v_cache_48_; lean_object* v_messages_49_; lean_object* v_snapshotTasks_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_70_; 
v___x_41_ = lean_st_ref_take(v___y_39_);
v_infoState_42_ = lean_ctor_get(v___x_41_, 7);
v_env_43_ = lean_ctor_get(v___x_41_, 0);
v_nextMacroScope_44_ = lean_ctor_get(v___x_41_, 1);
v_ngen_45_ = lean_ctor_get(v___x_41_, 2);
v_auxDeclNGen_46_ = lean_ctor_get(v___x_41_, 3);
v_traceState_47_ = lean_ctor_get(v___x_41_, 4);
v_cache_48_ = lean_ctor_get(v___x_41_, 5);
v_messages_49_ = lean_ctor_get(v___x_41_, 6);
v_snapshotTasks_50_ = lean_ctor_get(v___x_41_, 8);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_70_ == 0)
{
v___x_52_ = v___x_41_;
v_isShared_53_ = v_isSharedCheck_70_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_snapshotTasks_50_);
lean_inc(v_infoState_42_);
lean_inc(v_messages_49_);
lean_inc(v_cache_48_);
lean_inc(v_traceState_47_);
lean_inc(v_auxDeclNGen_46_);
lean_inc(v_ngen_45_);
lean_inc(v_nextMacroScope_44_);
lean_inc(v_env_43_);
lean_dec(v___x_41_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_70_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_assignment_54_; lean_object* v_lazyAssignment_55_; lean_object* v_trees_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_69_; 
v_assignment_54_ = lean_ctor_get(v_infoState_42_, 0);
v_lazyAssignment_55_ = lean_ctor_get(v_infoState_42_, 1);
v_trees_56_ = lean_ctor_get(v_infoState_42_, 2);
v_isSharedCheck_69_ = !lean_is_exclusive(v_infoState_42_);
if (v_isSharedCheck_69_ == 0)
{
v___x_58_ = v_infoState_42_;
v_isShared_59_ = v_isSharedCheck_69_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_trees_56_);
lean_inc(v_lazyAssignment_55_);
lean_inc(v_assignment_54_);
lean_dec(v_infoState_42_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_69_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_assignment_54_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_lazyAssignment_55_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v_trees_56_);
v___x_61_ = v_reuseFailAlloc_68_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_63_; 
lean_ctor_set_uint8(v___x_61_, sizeof(void*)*3, v_flag_38_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 7, v___x_61_);
v___x_63_ = v___x_52_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_env_43_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_nextMacroScope_44_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v_ngen_45_);
lean_ctor_set(v_reuseFailAlloc_67_, 3, v_auxDeclNGen_46_);
lean_ctor_set(v_reuseFailAlloc_67_, 4, v_traceState_47_);
lean_ctor_set(v_reuseFailAlloc_67_, 5, v_cache_48_);
lean_ctor_set(v_reuseFailAlloc_67_, 6, v_messages_49_);
lean_ctor_set(v_reuseFailAlloc_67_, 7, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_67_, 8, v_snapshotTasks_50_);
v___x_63_ = v_reuseFailAlloc_67_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_st_ref_set(v___y_39_, v___x_63_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg___boxed(lean_object* v_flag_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v_flag_boxed_74_; lean_object* v_res_75_; 
v_flag_boxed_74_ = lean_unbox(v_flag_71_);
v_res_75_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_boxed_74_, v___y_72_);
lean_dec(v___y_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(uint8_t v_flag_76_, lean_object* v_x_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v_infoState_86_; uint8_t v_enabled_87_; lean_object* v_a_89_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_85_ = lean_st_ref_get(v___y_83_);
v_infoState_86_ = lean_ctor_get(v___x_85_, 7);
lean_inc_ref(v_infoState_86_);
lean_dec(v___x_85_);
v_enabled_87_ = lean_ctor_get_uint8(v_infoState_86_, sizeof(void*)*3);
lean_dec_ref(v_infoState_86_);
v___x_99_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_76_, v___y_83_);
lean_dec_ref(v___x_99_);
lean_inc(v___y_83_);
v___x_100_ = lean_apply_7(v_x_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref(v___x_100_);
v___x_102_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_87_, v___y_83_);
lean_dec(v___y_83_);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v___x_102_, 0);
lean_dec(v_unused_110_);
v___x_104_ = v___x_102_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_dec(v___x_102_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_a_101_);
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_101_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_object* v_a_111_; 
v_a_111_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_111_);
lean_dec_ref(v___x_100_);
v_a_89_ = v_a_111_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v___x_90_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_87_, v___y_83_);
lean_dec(v___y_83_);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v___x_90_, 0);
lean_dec(v_unused_98_);
v___x_92_ = v___x_90_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_dec(v___x_90_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set_tag(v___x_92_, 1);
lean_ctor_set(v___x_92_, 0, v_a_89_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_89_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg___boxed(lean_object* v_flag_112_, lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v_flag_boxed_121_; lean_object* v_res_122_; 
v_flag_boxed_121_ = lean_unbox(v_flag_112_);
v_res_122_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_boxed_121_, v_x_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
if (lean_obj_tag(v_a_123_) == 0)
{
lean_object* v___x_125_; 
v___x_125_ = l_List_reverse___redArg(v_a_124_);
return v___x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_136_; 
v_head_126_ = lean_ctor_get(v_a_123_, 0);
v_tail_127_ = lean_ctor_get(v_a_123_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_123_);
if (v_isSharedCheck_136_ == 0)
{
v___x_129_ = v_a_123_;
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_head_126_);
lean_dec(v_a_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_declName_131_; lean_object* v___x_133_; 
v_declName_131_ = lean_ctor_get(v_head_126_, 3);
lean_inc(v_declName_131_);
lean_dec(v_head_126_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v_a_124_);
lean_ctor_set(v___x_129_, 0, v_declName_131_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_declName_131_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_a_124_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v_a_123_ = v_tail_127_;
v_a_124_ = v___x_133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(lean_object* v_o_140_, lean_object* v_k_141_, uint8_t v_v_142_){
_start:
{
lean_object* v_map_143_; uint8_t v_hasTrace_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_158_; 
v_map_143_ = lean_ctor_get(v_o_140_, 0);
v_hasTrace_144_ = lean_ctor_get_uint8(v_o_140_, sizeof(void*)*1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_o_140_);
if (v_isSharedCheck_158_ == 0)
{
v___x_146_ = v_o_140_;
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_map_143_);
lean_dec(v_o_140_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_148_, 0, v_v_142_);
lean_inc(v_k_141_);
v___x_149_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_141_, v___x_148_, v_map_143_);
if (v_hasTrace_144_ == 0)
{
lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_153_; 
v___x_150_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1));
v___x_151_ = l_Lean_Name_isPrefixOf(v___x_150_, v_k_141_);
lean_dec(v_k_141_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_153_ = v___x_146_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_149_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_151_);
return v___x_153_;
}
}
else
{
lean_object* v___x_156_; 
lean_dec(v_k_141_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_156_ = v___x_146_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, sizeof(void*)*1, v_hasTrace_144_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___boxed(lean_object* v_o_159_, lean_object* v_k_160_, lean_object* v_v_161_){
_start:
{
uint8_t v_v_boxed_162_; lean_object* v_res_163_; 
v_v_boxed_162_ = lean_unbox(v_v_161_);
v_res_163_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_o_159_, v_k_160_, v_v_boxed_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object* v_opts_164_, lean_object* v_opt_165_, uint8_t v_val_166_){
_start:
{
lean_object* v_name_167_; lean_object* v___x_168_; 
v_name_167_ = lean_ctor_get(v_opt_165_, 0);
lean_inc(v_name_167_);
lean_dec_ref(v_opt_165_);
v___x_168_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_opts_164_, v_name_167_, v_val_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object* v_opts_169_, lean_object* v_opt_170_, lean_object* v_val_171_){
_start:
{
uint8_t v_val_boxed_172_; lean_object* v_res_173_; 
v_val_boxed_172_ = lean_unbox(v_val_171_);
v_res_173_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_opts_169_, v_opt_170_, v_val_boxed_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(lean_object* v_docCtx_174_, lean_object* v_declNames_175_, uint8_t v_cacheProofs_176_, lean_object* v_as_177_, size_t v_i_178_, size_t v_stop_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_eq(v_i_178_, v_stop_179_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = 1;
v___x_190_ = lean_array_uget_borrowed(v_as_177_, v_i_178_);
lean_inc(v___y_186_);
lean_inc_ref(v___y_185_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v_declNames_175_);
lean_inc(v___x_190_);
lean_inc_ref(v_docCtx_174_);
v___x_191_ = l_Lean_Elab_addNonRec(v_docCtx_174_, v___x_190_, v___x_188_, v_declNames_175_, v_cacheProofs_176_, v___x_188_, v___x_189_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; size_t v___x_193_; size_t v___x_194_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref(v___x_191_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_178_, v___x_193_);
v_i_178_ = v___x_194_;
v_b_180_ = v_a_192_;
goto _start;
}
else
{
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v_declNames_175_);
lean_dec_ref(v_docCtx_174_);
return v___x_191_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v_declNames_175_);
lean_dec_ref(v_docCtx_174_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_b_180_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5___boxed(lean_object* v_docCtx_197_, lean_object* v_declNames_198_, lean_object* v_cacheProofs_199_, lean_object* v_as_200_, lean_object* v_i_201_, lean_object* v_stop_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
uint8_t v_cacheProofs_boxed_211_; size_t v_i_boxed_212_; size_t v_stop_boxed_213_; lean_object* v_res_214_; 
v_cacheProofs_boxed_211_ = lean_unbox(v_cacheProofs_199_);
v_i_boxed_212_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_stop_boxed_213_ = lean_unbox_usize(v_stop_202_);
lean_dec(v_stop_202_);
v_res_214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_197_, v_declNames_198_, v_cacheProofs_boxed_211_, v_as_200_, v_i_boxed_212_, v_stop_boxed_213_, v_b_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec_ref(v_as_200_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object* v_docCtx_221_, lean_object* v_preDefs_222_, lean_object* v_preDefsNonrec_223_, lean_object* v_unaryPreDefNonRec_224_, uint8_t v_cacheProofs_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_declName_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_declName_237_; lean_object* v___x_238_; lean_object* v_fileName_239_; lean_object* v_fileMap_240_; lean_object* v_options_241_; lean_object* v_currRecDepth_242_; lean_object* v_ref_243_; lean_object* v_currNamespace_244_; lean_object* v_openDecls_245_; lean_object* v_initHeartbeats_246_; lean_object* v_maxHeartbeats_247_; lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_cancelTk_x3f_250_; uint8_t v_suppressElabErrors_251_; lean_object* v_inheritedTraceOptions_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_344_; 
v_declName_233_ = lean_ctor_get(v_unaryPreDefNonRec_224_, 3);
v___x_234_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_array_get_borrowed(v___x_234_, v_preDefs_222_, v___x_235_);
v_declName_237_ = lean_ctor_get(v___x_236_, 3);
v___x_238_ = lean_st_ref_get(v_a_231_);
v_fileName_239_ = lean_ctor_get(v_a_230_, 0);
v_fileMap_240_ = lean_ctor_get(v_a_230_, 1);
v_options_241_ = lean_ctor_get(v_a_230_, 2);
v_currRecDepth_242_ = lean_ctor_get(v_a_230_, 3);
v_ref_243_ = lean_ctor_get(v_a_230_, 5);
v_currNamespace_244_ = lean_ctor_get(v_a_230_, 6);
v_openDecls_245_ = lean_ctor_get(v_a_230_, 7);
v_initHeartbeats_246_ = lean_ctor_get(v_a_230_, 8);
v_maxHeartbeats_247_ = lean_ctor_get(v_a_230_, 9);
v_quotContext_248_ = lean_ctor_get(v_a_230_, 10);
v_currMacroScope_249_ = lean_ctor_get(v_a_230_, 11);
v_cancelTk_x3f_250_ = lean_ctor_get(v_a_230_, 12);
v_suppressElabErrors_251_ = lean_ctor_get_uint8(v_a_230_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_252_ = lean_ctor_get(v_a_230_, 13);
v_isSharedCheck_344_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v_a_230_, 4);
lean_dec(v_unused_345_);
v___x_254_ = v_a_230_;
v_isShared_255_ = v_isSharedCheck_344_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_inheritedTraceOptions_252_);
lean_inc(v_cancelTk_x3f_250_);
lean_inc(v_currMacroScope_249_);
lean_inc(v_quotContext_248_);
lean_inc(v_maxHeartbeats_247_);
lean_inc(v_initHeartbeats_246_);
lean_inc(v_openDecls_245_);
lean_inc(v_currNamespace_244_);
lean_inc(v_ref_243_);
lean_inc(v_currRecDepth_242_);
lean_inc(v_options_241_);
lean_inc(v_fileMap_240_);
lean_inc(v_fileName_239_);
lean_dec(v_a_230_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_344_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_env_256_; lean_object* v___f_257_; uint8_t v___x_258_; lean_object* v_preDefNonRec_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_declNames_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v_fileName_269_; lean_object* v_fileMap_270_; lean_object* v_currRecDepth_271_; lean_object* v_ref_272_; lean_object* v_currNamespace_273_; lean_object* v_openDecls_274_; lean_object* v_initHeartbeats_275_; lean_object* v_maxHeartbeats_276_; lean_object* v_quotContext_277_; lean_object* v_currMacroScope_278_; lean_object* v_cancelTk_x3f_279_; uint8_t v_suppressElabErrors_280_; lean_object* v_inheritedTraceOptions_281_; lean_object* v___y_282_; uint8_t v___y_322_; uint8_t v___x_343_; 
v_env_256_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_238_);
v___f_257_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v___x_258_ = lean_name_eq(v_declName_233_, v_declName_237_);
v_preDefNonRec_259_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_224_, v___f_257_);
v___x_260_ = lean_array_to_list(v_preDefs_222_);
v___x_261_ = lean_box(0);
v_declNames_262_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_260_, v___x_261_);
v___x_263_ = l_Lean_allowUnsafeReducibility;
v___x_264_ = 1;
v___x_265_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_options_241_, v___x_263_, v___x_264_);
v___x_266_ = l_Lean_diagnostics;
v___x_267_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v___x_265_, v___x_266_);
v___x_343_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_256_);
lean_dec_ref(v_env_256_);
if (v___x_343_ == 0)
{
if (v___x_267_ == 0)
{
v_fileName_269_ = v_fileName_239_;
v_fileMap_270_ = v_fileMap_240_;
v_currRecDepth_271_ = v_currRecDepth_242_;
v_ref_272_ = v_ref_243_;
v_currNamespace_273_ = v_currNamespace_244_;
v_openDecls_274_ = v_openDecls_245_;
v_initHeartbeats_275_ = v_initHeartbeats_246_;
v_maxHeartbeats_276_ = v_maxHeartbeats_247_;
v_quotContext_277_ = v_quotContext_248_;
v_currMacroScope_278_ = v_currMacroScope_249_;
v_cancelTk_x3f_279_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_280_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_281_ = v_inheritedTraceOptions_252_;
v___y_282_ = v_a_231_;
goto v___jp_268_;
}
else
{
v___y_322_ = v___x_343_;
goto v___jp_321_;
}
}
else
{
v___y_322_ = v___x_267_;
goto v___jp_321_;
}
v___jp_268_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = l_Lean_maxRecDepth;
v___x_284_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v___x_265_, v___x_283_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 13, v_inheritedTraceOptions_281_);
lean_ctor_set(v___x_254_, 12, v_cancelTk_x3f_279_);
lean_ctor_set(v___x_254_, 11, v_currMacroScope_278_);
lean_ctor_set(v___x_254_, 10, v_quotContext_277_);
lean_ctor_set(v___x_254_, 9, v_maxHeartbeats_276_);
lean_ctor_set(v___x_254_, 8, v_initHeartbeats_275_);
lean_ctor_set(v___x_254_, 7, v_openDecls_274_);
lean_ctor_set(v___x_254_, 6, v_currNamespace_273_);
lean_ctor_set(v___x_254_, 5, v_ref_272_);
lean_ctor_set(v___x_254_, 4, v___x_284_);
lean_ctor_set(v___x_254_, 3, v_currRecDepth_271_);
lean_ctor_set(v___x_254_, 2, v___x_265_);
lean_ctor_set(v___x_254_, 1, v_fileMap_270_);
lean_ctor_set(v___x_254_, 0, v_fileName_269_);
v___x_286_ = v___x_254_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_fileName_269_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_fileMap_270_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_currRecDepth_271_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_320_, 5, v_ref_272_);
lean_ctor_set(v_reuseFailAlloc_320_, 6, v_currNamespace_273_);
lean_ctor_set(v_reuseFailAlloc_320_, 7, v_openDecls_274_);
lean_ctor_set(v_reuseFailAlloc_320_, 8, v_initHeartbeats_275_);
lean_ctor_set(v_reuseFailAlloc_320_, 9, v_maxHeartbeats_276_);
lean_ctor_set(v_reuseFailAlloc_320_, 10, v_quotContext_277_);
lean_ctor_set(v_reuseFailAlloc_320_, 11, v_currMacroScope_278_);
lean_ctor_set(v_reuseFailAlloc_320_, 12, v_cancelTk_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_320_, 13, v_inheritedTraceOptions_281_);
v___x_286_ = v_reuseFailAlloc_320_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*14, v___x_267_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*14 + 1, v_suppressElabErrors_280_);
if (v___x_258_ == 0)
{
lean_object* v_declName_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_declName_287_ = lean_ctor_get(v_preDefNonRec_259_, 3);
lean_inc(v_declName_287_);
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v_declName_287_);
lean_ctor_set(v___x_288_, 1, v___x_261_);
v___x_289_ = lean_box(v___x_258_);
v___x_290_ = lean_box(v_cacheProofs_225_);
v___x_291_ = lean_box(v___x_258_);
v___x_292_ = lean_box(v___x_264_);
lean_inc_ref(v_docCtx_221_);
v___x_293_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 14, 7);
lean_closure_set(v___x_293_, 0, v_docCtx_221_);
lean_closure_set(v___x_293_, 1, v_preDefNonRec_259_);
lean_closure_set(v___x_293_, 2, v___x_289_);
lean_closure_set(v___x_293_, 3, v___x_288_);
lean_closure_set(v___x_293_, 4, v___x_290_);
lean_closure_set(v___x_293_, 5, v___x_291_);
lean_closure_set(v___x_293_, 6, v___x_292_);
lean_inc(v___y_282_);
lean_inc_ref(v___x_286_);
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
lean_inc(v_a_227_);
lean_inc_ref(v_a_226_);
v___x_294_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v___x_258_, v___x_293_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_286_, v___y_282_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_314_; 
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v___x_294_, 0);
lean_dec(v_unused_315_);
v___x_296_ = v___x_294_;
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
else
{
lean_dec(v___x_294_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = lean_array_get_size(v_preDefsNonrec_223_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_nat_dec_lt(v___x_235_, v___x_298_);
if (v___x_300_ == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_286_);
lean_dec(v___y_282_);
lean_dec(v_declNames_262_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_docCtx_221_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_299_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_299_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
else
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_le(v___x_298_, v___x_298_);
if (v___x_304_ == 0)
{
if (v___x_300_ == 0)
{
lean_object* v___x_306_; 
lean_dec_ref(v___x_286_);
lean_dec(v___y_282_);
lean_dec(v_declNames_262_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_docCtx_221_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_299_);
v___x_306_ = v___x_296_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_299_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
size_t v___x_308_; size_t v___x_309_; lean_object* v___x_310_; 
lean_del_object(v___x_296_);
v___x_308_ = ((size_t)0ULL);
v___x_309_ = lean_usize_of_nat(v___x_298_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_221_, v_declNames_262_, v_cacheProofs_225_, v_preDefsNonrec_223_, v___x_308_, v___x_309_, v___x_299_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_286_, v___y_282_);
return v___x_310_;
}
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
lean_del_object(v___x_296_);
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_298_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_221_, v_declNames_262_, v_cacheProofs_225_, v_preDefsNonrec_223_, v___x_311_, v___x_312_, v___x_299_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_286_, v___y_282_);
return v___x_313_;
}
}
}
}
else
{
lean_dec_ref(v___x_286_);
lean_dec(v___y_282_);
lean_dec(v_declNames_262_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_docCtx_221_);
return v___x_294_;
}
}
else
{
lean_object* v_declName_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_declNames_262_);
v_declName_316_ = lean_ctor_get(v_preDefNonRec_259_, 3);
lean_inc(v_declName_316_);
v___x_317_ = 0;
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v_declName_316_);
lean_ctor_set(v___x_318_, 1, v___x_261_);
v___x_319_ = l_Lean_Elab_addNonRec(v_docCtx_221_, v_preDefNonRec_259_, v___x_317_, v___x_318_, v_cacheProofs_225_, v___x_317_, v___x_264_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_286_, v___y_282_);
return v___x_319_;
}
}
}
v___jp_321_:
{
if (v___y_322_ == 0)
{
lean_object* v___x_323_; lean_object* v_env_324_; lean_object* v_nextMacroScope_325_; lean_object* v_ngen_326_; lean_object* v_auxDeclNGen_327_; lean_object* v_traceState_328_; lean_object* v_messages_329_; lean_object* v_infoState_330_; lean_object* v_snapshotTasks_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_341_; 
v___x_323_ = lean_st_ref_take(v_a_231_);
v_env_324_ = lean_ctor_get(v___x_323_, 0);
v_nextMacroScope_325_ = lean_ctor_get(v___x_323_, 1);
v_ngen_326_ = lean_ctor_get(v___x_323_, 2);
v_auxDeclNGen_327_ = lean_ctor_get(v___x_323_, 3);
v_traceState_328_ = lean_ctor_get(v___x_323_, 4);
v_messages_329_ = lean_ctor_get(v___x_323_, 6);
v_infoState_330_ = lean_ctor_get(v___x_323_, 7);
v_snapshotTasks_331_ = lean_ctor_get(v___x_323_, 8);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v___x_323_, 5);
lean_dec(v_unused_342_);
v___x_333_ = v___x_323_;
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snapshotTasks_331_);
lean_inc(v_infoState_330_);
lean_inc(v_messages_329_);
lean_inc(v_traceState_328_);
lean_inc(v_auxDeclNGen_327_);
lean_inc(v_ngen_326_);
lean_inc(v_nextMacroScope_325_);
lean_inc(v_env_324_);
lean_dec(v___x_323_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = l_Lean_Kernel_enableDiag(v_env_324_, v___x_267_);
v___x_336_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 5, v___x_336_);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_nextMacroScope_325_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_ngen_326_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_auxDeclNGen_327_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_traceState_328_);
lean_ctor_set(v_reuseFailAlloc_340_, 5, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 6, v_messages_329_);
lean_ctor_set(v_reuseFailAlloc_340_, 7, v_infoState_330_);
lean_ctor_set(v_reuseFailAlloc_340_, 8, v_snapshotTasks_331_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; 
v___x_339_ = lean_st_ref_set(v_a_231_, v___x_338_);
v_fileName_269_ = v_fileName_239_;
v_fileMap_270_ = v_fileMap_240_;
v_currRecDepth_271_ = v_currRecDepth_242_;
v_ref_272_ = v_ref_243_;
v_currNamespace_273_ = v_currNamespace_244_;
v_openDecls_274_ = v_openDecls_245_;
v_initHeartbeats_275_ = v_initHeartbeats_246_;
v_maxHeartbeats_276_ = v_maxHeartbeats_247_;
v_quotContext_277_ = v_quotContext_248_;
v_currMacroScope_278_ = v_currMacroScope_249_;
v_cancelTk_x3f_279_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_280_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_281_ = v_inheritedTraceOptions_252_;
v___y_282_ = v_a_231_;
goto v___jp_268_;
}
}
}
else
{
v_fileName_269_ = v_fileName_239_;
v_fileMap_270_ = v_fileMap_240_;
v_currRecDepth_271_ = v_currRecDepth_242_;
v_ref_272_ = v_ref_243_;
v_currNamespace_273_ = v_currNamespace_244_;
v_openDecls_274_ = v_openDecls_245_;
v_initHeartbeats_275_ = v_initHeartbeats_246_;
v_maxHeartbeats_276_ = v_maxHeartbeats_247_;
v_quotContext_277_ = v_quotContext_248_;
v_currMacroScope_278_ = v_currMacroScope_249_;
v_cancelTk_x3f_279_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_280_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_281_ = v_inheritedTraceOptions_252_;
v___y_282_ = v_a_231_;
goto v___jp_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_346_, lean_object* v_preDefs_347_, lean_object* v_preDefsNonrec_348_, lean_object* v_unaryPreDefNonRec_349_, lean_object* v_cacheProofs_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
uint8_t v_cacheProofs_boxed_358_; lean_object* v_res_359_; 
v_cacheProofs_boxed_358_ = lean_unbox(v_cacheProofs_350_);
v_res_359_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_346_, v_preDefs_347_, v_preDefsNonrec_348_, v_unaryPreDefNonRec_349_, v_cacheProofs_boxed_358_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec_ref(v_preDefsNonrec_348_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(uint8_t v_flag_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_360_, v___y_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_flag_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
uint8_t v_flag_boxed_377_; lean_object* v_res_378_; 
v_flag_boxed_377_ = lean_unbox(v_flag_369_);
v_res_378_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_flag_boxed_377_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_00_u03b1_379_, uint8_t v_flag_380_, lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_380_, v_x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_00_u03b1_390_, lean_object* v_flag_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v_flag_boxed_400_; lean_object* v_res_401_; 
v_flag_boxed_400_ = lean_unbox(v_flag_391_);
v_res_401_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_00_u03b1_390_, v_flag_boxed_400_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_402_, uint8_t v_cacheProofs_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; 
lean_inc(v_a_407_);
lean_inc_ref(v_a_406_);
v___x_409_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_402_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v___x_409_);
v___x_411_ = l_Lean_Elab_abstractNestedProofs(v_a_410_, v_cacheProofs_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_411_;
}
else
{
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_412_, lean_object* v_cacheProofs_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
uint8_t v_cacheProofs_boxed_419_; lean_object* v_res_420_; 
v_cacheProofs_boxed_419_ = lean_unbox(v_cacheProofs_413_);
v_res_420_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_412_, v_cacheProofs_boxed_419_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_421_, size_t v_sz_422_, size_t v_i_423_, lean_object* v_b_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_usize_dec_lt(v_i_423_, v_sz_422_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec_ref(v___y_425_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_b_424_);
return v___x_429_;
}
else
{
lean_object* v_a_430_; lean_object* v_declName_431_; lean_object* v___x_432_; 
v_a_430_ = lean_array_uget_borrowed(v_as_421_, v_i_423_);
v_declName_431_ = lean_ctor_get(v_a_430_, 3);
lean_inc_ref(v___y_425_);
lean_inc(v_declName_431_);
v___x_432_ = l_Lean_enableRealizationsForConst(v_declName_431_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; size_t v___x_434_; size_t v___x_435_; 
lean_dec_ref(v___x_432_);
v___x_433_ = lean_box(0);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_423_, v___x_434_);
v_i_423_ = v___x_435_;
v_b_424_ = v___x_433_;
goto _start;
}
else
{
lean_dec_ref(v___y_425_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_437_, lean_object* v_sz_438_, lean_object* v_i_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
size_t v_sz_boxed_444_; size_t v_i_boxed_445_; lean_object* v_res_446_; 
v_sz_boxed_444_ = lean_unbox_usize(v_sz_438_);
lean_dec(v_sz_438_);
v_i_boxed_445_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_437_, v_sz_boxed_444_, v_i_boxed_445_, v_b_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v_as_437_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_447_, size_t v_sz_448_, size_t v_i_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_449_, v_sz_448_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_b_450_);
return v___x_459_;
}
else
{
lean_object* v_a_460_; lean_object* v_declName_461_; lean_object* v___x_462_; 
v_a_460_ = lean_array_uget_borrowed(v_as_447_, v_i_449_);
v_declName_461_ = lean_ctor_get(v_a_460_, 3);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
lean_inc(v_declName_461_);
v___x_462_ = l_Lean_Meta_generateEagerEqns(v_declName_461_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v___x_462_);
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_mk_empty_array_with_capacity(v___x_463_);
lean_inc(v_a_460_);
v___x_465_ = lean_array_push(v___x_464_, v_a_460_);
v___x_466_ = 1;
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
v___x_467_ = l_Lean_Elab_applyAttributesOf(v___x_465_, v___x_466_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec_ref(v___x_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; size_t v___x_469_; size_t v___x_470_; 
lean_dec_ref(v___x_467_);
v___x_468_ = lean_box(0);
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_add(v_i_449_, v___x_469_);
v_i_449_ = v___x_470_;
v_b_450_ = v___x_468_;
goto _start;
}
else
{
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v___x_467_;
}
}
else
{
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_472_, lean_object* v_sz_473_, lean_object* v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
size_t v_sz_boxed_483_; size_t v_i_boxed_484_; lean_object* v_res_485_; 
v_sz_boxed_483_ = lean_unbox_usize(v_sz_473_);
lean_dec(v_sz_473_);
v_i_boxed_484_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_472_, v_sz_boxed_483_, v_i_boxed_484_, v_b_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec_ref(v_as_472_);
return v_res_485_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_487_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
lean_ctor_set(v___x_487_, 3, v___x_486_);
lean_ctor_set(v___x_487_, 4, v___x_486_);
lean_ctor_set(v___x_487_, 5, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_488_, uint8_t v_s_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; lean_object* v_env_494_; lean_object* v_nextMacroScope_495_; lean_object* v_ngen_496_; lean_object* v_auxDeclNGen_497_; lean_object* v_traceState_498_; lean_object* v_messages_499_; lean_object* v_infoState_500_; lean_object* v_snapshotTasks_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_530_; 
v___x_493_ = lean_st_ref_take(v___y_491_);
v_env_494_ = lean_ctor_get(v___x_493_, 0);
v_nextMacroScope_495_ = lean_ctor_get(v___x_493_, 1);
v_ngen_496_ = lean_ctor_get(v___x_493_, 2);
v_auxDeclNGen_497_ = lean_ctor_get(v___x_493_, 3);
v_traceState_498_ = lean_ctor_get(v___x_493_, 4);
v_messages_499_ = lean_ctor_get(v___x_493_, 6);
v_infoState_500_ = lean_ctor_get(v___x_493_, 7);
v_snapshotTasks_501_ = lean_ctor_get(v___x_493_, 8);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v___x_493_, 5);
lean_dec(v_unused_531_);
v___x_503_ = v___x_493_;
v_isShared_504_ = v_isSharedCheck_530_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snapshotTasks_501_);
lean_inc(v_infoState_500_);
lean_inc(v_messages_499_);
lean_inc(v_traceState_498_);
lean_inc(v_auxDeclNGen_497_);
lean_inc(v_ngen_496_);
lean_inc(v_nextMacroScope_495_);
lean_inc(v_env_494_);
lean_dec(v___x_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_530_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_505_ = 0;
v___x_506_ = lean_box(0);
v___x_507_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_494_, v_declName_488_, v_s_489_, v___x_505_, v___x_506_);
v___x_508_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 5, v___x_508_);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_nextMacroScope_495_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_ngen_496_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_auxDeclNGen_497_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_traceState_498_);
lean_ctor_set(v_reuseFailAlloc_529_, 5, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_529_, 6, v_messages_499_);
lean_ctor_set(v_reuseFailAlloc_529_, 7, v_infoState_500_);
lean_ctor_set(v_reuseFailAlloc_529_, 8, v_snapshotTasks_501_);
v___x_510_ = v_reuseFailAlloc_529_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_mctx_513_; lean_object* v_zetaDeltaFVarIds_514_; lean_object* v_postponed_515_; lean_object* v_diag_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_527_; 
v___x_511_ = lean_st_ref_set(v___y_491_, v___x_510_);
v___x_512_ = lean_st_ref_take(v___y_490_);
v_mctx_513_ = lean_ctor_get(v___x_512_, 0);
v_zetaDeltaFVarIds_514_ = lean_ctor_get(v___x_512_, 2);
v_postponed_515_ = lean_ctor_get(v___x_512_, 3);
v_diag_516_ = lean_ctor_get(v___x_512_, 4);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_512_, 1);
lean_dec(v_unused_528_);
v___x_518_ = v___x_512_;
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_diag_516_);
lean_inc(v_postponed_515_);
lean_inc(v_zetaDeltaFVarIds_514_);
lean_inc(v_mctx_513_);
lean_dec(v___x_512_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_mctx_513_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_zetaDeltaFVarIds_514_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_postponed_515_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v_diag_516_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_st_ref_set(v___y_490_, v___x_522_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_532_, lean_object* v_s_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v_s_boxed_537_; lean_object* v_res_538_; 
v_s_boxed_537_ = lean_unbox(v_s_533_);
v_res_538_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_532_, v_s_boxed_537_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec(v___y_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v___x_547_; lean_object* v___x_548_; 
v___x_547_ = 2;
v___x_548_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_539_, v___x_547_, v___y_543_, v___y_545_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_557_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v_as_570_, size_t v_i_571_, size_t v_stop_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_571_, v_stop_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v_name_575_; uint8_t v___x_576_; uint8_t v___y_578_; uint8_t v___y_583_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_574_ = lean_array_uget_borrowed(v_as_570_, v_i_571_);
v_name_575_ = lean_ctor_get(v___x_574_, 0);
v___x_576_ = 1;
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_590_ = lean_name_eq(v_name_575_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_592_ = lean_name_eq(v_name_575_, v___x_591_);
v___y_583_ = v___x_592_;
goto v___jp_582_;
}
else
{
v___y_583_ = v___x_590_;
goto v___jp_582_;
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
size_t v___x_579_; size_t v___x_580_; 
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_571_, v___x_579_);
v_i_571_ = v___x_580_;
goto _start;
}
else
{
return v___x_576_;
}
}
v___jp_582_:
{
if (v___y_583_ == 0)
{
lean_object* v_name_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_name_584_ = lean_ctor_get(v___x_574_, 0);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_586_ = lean_name_eq(v_name_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_588_ = lean_name_eq(v_name_584_, v___x_587_);
v___y_578_ = v___x_588_;
goto v___jp_577_;
}
else
{
v___y_578_ = v___x_586_;
goto v___jp_577_;
}
}
else
{
return v___x_576_;
}
}
}
else
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_stop_596_){
_start:
{
size_t v_i_boxed_597_; size_t v_stop_boxed_598_; uint8_t v_res_599_; lean_object* v_r_600_; 
v_i_boxed_597_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_stop_boxed_598_ = lean_unbox_usize(v_stop_596_);
lean_dec(v_stop_596_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_as_594_, v_i_boxed_597_, v_stop_boxed_598_);
lean_dec_ref(v_as_594_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_601_, size_t v_sz_602_, size_t v_i_603_, lean_object* v_b_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_a_613_; uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_603_, v_sz_602_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_604_);
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v_modifiers_620_; lean_object* v_attrs_621_; lean_object* v___x_622_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_a_619_ = lean_array_uget_borrowed(v_as_601_, v_i_603_);
v_modifiers_620_ = lean_ctor_get(v_a_619_, 2);
v_attrs_621_ = lean_ctor_get(v_modifiers_620_, 2);
v___x_622_ = lean_box(0);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_array_get_size(v_attrs_621_);
v___x_628_ = lean_nat_dec_lt(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
goto v___jp_623_;
}
else
{
if (v___x_628_ == 0)
{
goto v___jp_623_;
}
else
{
size_t v___x_629_; size_t v___x_630_; uint8_t v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_627_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_attrs_621_, v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
goto v___jp_623_;
}
else
{
v_a_613_ = v___x_622_;
goto v___jp_612_;
}
}
}
v___jp_623_:
{
lean_object* v_declName_624_; lean_object* v___x_625_; 
v_declName_624_ = lean_ctor_get(v_a_619_, 3);
lean_inc(v_declName_624_);
v___x_625_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_624_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec_ref(v___x_625_);
v_a_613_ = v___x_622_;
goto v___jp_612_;
}
else
{
return v___x_625_;
}
}
}
v___jp_612_:
{
size_t v___x_614_; size_t v___x_615_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_603_, v___x_614_);
v_i_603_ = v___x_615_;
v_b_604_ = v_a_613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_632_, lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_b_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
size_t v_sz_boxed_643_; size_t v_i_boxed_644_; lean_object* v_res_645_; 
v_sz_boxed_643_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_644_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_632_, v_sz_boxed_643_, v_i_boxed_644_, v_b_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v_as_632_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_654_; size_t v_sz_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_box(0);
v_sz_655_ = lean_array_size(v_preDefs_646_);
v___x_656_ = ((size_t)0ULL);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_646_, v_sz_655_, v___x_656_, v___x_654_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; size_t v_sz_659_; lean_object* v___x_660_; 
lean_dec_ref(v___x_657_);
lean_inc_ref(v_preDefs_646_);
v___x_658_ = l_Array_reverse___redArg(v_preDefs_646_);
v_sz_659_ = lean_array_size(v___x_658_);
lean_inc_ref(v_a_651_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v___x_658_, v_sz_659_, v___x_656_, v___x_654_, v_a_651_, v_a_652_);
lean_dec_ref(v___x_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v___x_660_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_preDefs_646_, v_sz_655_, v___x_656_, v___x_654_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec_ref(v_preDefs_646_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_661_, 0);
lean_dec(v_unused_669_);
v___x_663_ = v___x_661_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_dec(v___x_661_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_654_);
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_654_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
return v___x_661_;
}
}
else
{
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_preDefs_646_);
return v___x_660_;
}
}
else
{
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_preDefs_646_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_679_, uint8_t v_s_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_679_, v_s_680_, v___y_684_, v___y_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_689_, lean_object* v_s_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v_s_boxed_698_; lean_object* v_res_699_; 
v_s_boxed_698_ = lean_unbox(v_s_690_);
v_res_699_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_689_, v_s_boxed_698_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_700_, size_t v_sz_701_, size_t v_i_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_700_, v_sz_701_, v_i_702_, v_b_703_, v___y_708_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_712_, lean_object* v_sz_713_, lean_object* v_i_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_713_);
lean_dec(v_sz_713_);
v_i_boxed_724_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_712_, v_sz_boxed_723_, v_i_boxed_724_, v_b_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_as_712_);
return v_res_725_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Mutual(builtin);
}
#ifdef __cplusplus
}
#endif
