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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instance_reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 180, 213, 185, 56, 77, 23, 14)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implicit_reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(138, 100, 121, 167, 26, 160, 176, 156)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
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
lean_dec_ref_known(v___x_20_, 1);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref_known(v_val_21_, 1);
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
v___x_64_ = lean_st_ref_put(v___y_39_, v___x_63_);
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
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
v___x_100_ = lean_apply_7(v_x_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_100_, 1);
v___x_102_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_87_, v___y_83_);
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
lean_dec_ref_known(v___x_100_, 1);
v_a_89_ = v_a_111_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v___x_90_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_87_, v___y_83_);
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
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(lean_object* v_docCtx_174_, uint8_t v___x_175_, lean_object* v_declNames_176_, uint8_t v_cacheProofs_177_, lean_object* v_as_178_, size_t v_i_179_, size_t v_stop_180_, lean_object* v_b_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = lean_usize_dec_eq(v_i_179_, v_stop_180_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = 1;
v___x_191_ = lean_array_uget_borrowed(v_as_178_, v_i_179_);
lean_inc(v_declNames_176_);
lean_inc(v___x_191_);
lean_inc_ref(v_docCtx_174_);
v___x_192_ = l_Lean_Elab_addNonRec(v_docCtx_174_, v___x_191_, v___x_175_, v_declNames_176_, v_cacheProofs_177_, v___x_175_, v___x_190_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; size_t v___x_194_; size_t v___x_195_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_179_, v___x_194_);
v_i_179_ = v___x_195_;
v_b_181_ = v_a_193_;
goto _start;
}
else
{
lean_dec(v_declNames_176_);
lean_dec_ref(v_docCtx_174_);
return v___x_192_;
}
}
else
{
lean_object* v___x_197_; 
lean_dec(v_declNames_176_);
lean_dec_ref(v_docCtx_174_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_b_181_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5___boxed(lean_object* v_docCtx_198_, lean_object* v___x_199_, lean_object* v_declNames_200_, lean_object* v_cacheProofs_201_, lean_object* v_as_202_, lean_object* v_i_203_, lean_object* v_stop_204_, lean_object* v_b_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
uint8_t v___x_4374__boxed_213_; uint8_t v_cacheProofs_boxed_214_; size_t v_i_boxed_215_; size_t v_stop_boxed_216_; lean_object* v_res_217_; 
v___x_4374__boxed_213_ = lean_unbox(v___x_199_);
v_cacheProofs_boxed_214_ = lean_unbox(v_cacheProofs_201_);
v_i_boxed_215_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_stop_boxed_216_ = lean_unbox_usize(v_stop_204_);
lean_dec(v_stop_204_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_198_, v___x_4374__boxed_213_, v_declNames_200_, v_cacheProofs_boxed_214_, v_as_202_, v_i_boxed_215_, v_stop_boxed_216_, v_b_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec_ref(v_as_202_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object* v_docCtx_224_, lean_object* v_preDefs_225_, lean_object* v_preDefsNonrec_226_, lean_object* v_unaryPreDefNonRec_227_, uint8_t v_cacheProofs_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; lean_object* v_declName_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_declName_241_; lean_object* v_fileName_242_; lean_object* v_fileMap_243_; lean_object* v_options_244_; lean_object* v_currRecDepth_245_; lean_object* v_ref_246_; lean_object* v_currNamespace_247_; lean_object* v_openDecls_248_; lean_object* v_initHeartbeats_249_; lean_object* v_maxHeartbeats_250_; lean_object* v_quotContext_251_; lean_object* v_currMacroScope_252_; lean_object* v_cancelTk_x3f_253_; uint8_t v_suppressElabErrors_254_; lean_object* v_inheritedTraceOptions_255_; lean_object* v_env_256_; lean_object* v___f_257_; lean_object* v_preDefNonRec_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_declNames_261_; uint8_t v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v_fileName_269_; lean_object* v_fileMap_270_; lean_object* v_currRecDepth_271_; lean_object* v_ref_272_; lean_object* v_currNamespace_273_; lean_object* v_openDecls_274_; lean_object* v_initHeartbeats_275_; lean_object* v_maxHeartbeats_276_; lean_object* v_quotContext_277_; lean_object* v_currMacroScope_278_; lean_object* v_cancelTk_x3f_279_; uint8_t v_suppressElabErrors_280_; lean_object* v_inheritedTraceOptions_281_; lean_object* v___y_282_; uint8_t v___y_320_; uint8_t v___x_341_; 
v___x_236_ = lean_st_ref_get(v_a_234_);
v_declName_237_ = lean_ctor_get(v_unaryPreDefNonRec_227_, 3);
lean_inc(v_declName_237_);
v___x_238_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_array_get_borrowed(v___x_238_, v_preDefs_225_, v___x_239_);
v_declName_241_ = lean_ctor_get(v___x_240_, 3);
lean_inc(v_declName_241_);
v_fileName_242_ = lean_ctor_get(v_a_233_, 0);
v_fileMap_243_ = lean_ctor_get(v_a_233_, 1);
v_options_244_ = lean_ctor_get(v_a_233_, 2);
v_currRecDepth_245_ = lean_ctor_get(v_a_233_, 3);
v_ref_246_ = lean_ctor_get(v_a_233_, 5);
v_currNamespace_247_ = lean_ctor_get(v_a_233_, 6);
v_openDecls_248_ = lean_ctor_get(v_a_233_, 7);
v_initHeartbeats_249_ = lean_ctor_get(v_a_233_, 8);
v_maxHeartbeats_250_ = lean_ctor_get(v_a_233_, 9);
v_quotContext_251_ = lean_ctor_get(v_a_233_, 10);
v_currMacroScope_252_ = lean_ctor_get(v_a_233_, 11);
v_cancelTk_x3f_253_ = lean_ctor_get(v_a_233_, 12);
v_suppressElabErrors_254_ = lean_ctor_get_uint8(v_a_233_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_255_ = lean_ctor_get(v_a_233_, 13);
v_env_256_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_236_);
v___f_257_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v_preDefNonRec_258_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_227_, v___f_257_);
v___x_259_ = lean_array_to_list(v_preDefs_225_);
v___x_260_ = lean_box(0);
v_declNames_261_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_259_, v___x_260_);
v___x_262_ = lean_name_eq(v_declName_237_, v_declName_241_);
lean_dec(v_declName_241_);
lean_dec(v_declName_237_);
v___x_263_ = l_Lean_allowUnsafeReducibility;
v___x_264_ = 1;
lean_inc_ref(v_options_244_);
v___x_265_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_options_244_, v___x_263_, v___x_264_);
v___x_266_ = l_Lean_diagnostics;
v___x_267_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v___x_265_, v___x_266_);
v___x_341_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_256_);
lean_dec_ref(v_env_256_);
if (v___x_267_ == 0)
{
if (v___x_341_ == 0)
{
v_fileName_269_ = v_fileName_242_;
v_fileMap_270_ = v_fileMap_243_;
v_currRecDepth_271_ = v_currRecDepth_245_;
v_ref_272_ = v_ref_246_;
v_currNamespace_273_ = v_currNamespace_247_;
v_openDecls_274_ = v_openDecls_248_;
v_initHeartbeats_275_ = v_initHeartbeats_249_;
v_maxHeartbeats_276_ = v_maxHeartbeats_250_;
v_quotContext_277_ = v_quotContext_251_;
v_currMacroScope_278_ = v_currMacroScope_252_;
v_cancelTk_x3f_279_ = v_cancelTk_x3f_253_;
v_suppressElabErrors_280_ = v_suppressElabErrors_254_;
v_inheritedTraceOptions_281_ = v_inheritedTraceOptions_255_;
v___y_282_ = v_a_234_;
goto v___jp_268_;
}
else
{
v___y_320_ = v___x_267_;
goto v___jp_319_;
}
}
else
{
v___y_320_ = v___x_341_;
goto v___jp_319_;
}
v___jp_268_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = l_Lean_maxRecDepth;
v___x_284_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v___x_265_, v___x_283_);
lean_inc_ref(v_inheritedTraceOptions_281_);
lean_inc(v_cancelTk_x3f_279_);
lean_inc(v_currMacroScope_278_);
lean_inc(v_quotContext_277_);
lean_inc(v_maxHeartbeats_276_);
lean_inc(v_initHeartbeats_275_);
lean_inc(v_openDecls_274_);
lean_inc(v_currNamespace_273_);
lean_inc(v_ref_272_);
lean_inc(v_currRecDepth_271_);
lean_inc_ref(v_fileMap_270_);
lean_inc_ref(v_fileName_269_);
v___x_285_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_285_, 0, v_fileName_269_);
lean_ctor_set(v___x_285_, 1, v_fileMap_270_);
lean_ctor_set(v___x_285_, 2, v___x_265_);
lean_ctor_set(v___x_285_, 3, v_currRecDepth_271_);
lean_ctor_set(v___x_285_, 4, v___x_284_);
lean_ctor_set(v___x_285_, 5, v_ref_272_);
lean_ctor_set(v___x_285_, 6, v_currNamespace_273_);
lean_ctor_set(v___x_285_, 7, v_openDecls_274_);
lean_ctor_set(v___x_285_, 8, v_initHeartbeats_275_);
lean_ctor_set(v___x_285_, 9, v_maxHeartbeats_276_);
lean_ctor_set(v___x_285_, 10, v_quotContext_277_);
lean_ctor_set(v___x_285_, 11, v_currMacroScope_278_);
lean_ctor_set(v___x_285_, 12, v_cancelTk_x3f_279_);
lean_ctor_set(v___x_285_, 13, v_inheritedTraceOptions_281_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*14, v___x_267_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*14 + 1, v_suppressElabErrors_280_);
if (v___x_262_ == 0)
{
lean_object* v_declName_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_declName_286_ = lean_ctor_get(v_preDefNonRec_258_, 3);
lean_inc(v_declName_286_);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v_declName_286_);
lean_ctor_set(v___x_287_, 1, v___x_260_);
v___x_288_ = lean_box(v___x_262_);
v___x_289_ = lean_box(v_cacheProofs_228_);
v___x_290_ = lean_box(v___x_262_);
v___x_291_ = lean_box(v___x_264_);
lean_inc_ref(v_docCtx_224_);
v___x_292_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 14, 7);
lean_closure_set(v___x_292_, 0, v_docCtx_224_);
lean_closure_set(v___x_292_, 1, v_preDefNonRec_258_);
lean_closure_set(v___x_292_, 2, v___x_288_);
lean_closure_set(v___x_292_, 3, v___x_287_);
lean_closure_set(v___x_292_, 4, v___x_289_);
lean_closure_set(v___x_292_, 5, v___x_290_);
lean_closure_set(v___x_292_, 6, v___x_291_);
v___x_293_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v___x_262_, v___x_292_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_285_, v___y_282_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_313_; 
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_293_, 0);
lean_dec(v_unused_314_);
v___x_295_ = v___x_293_;
v_isShared_296_ = v_isSharedCheck_313_;
goto v_resetjp_294_;
}
else
{
lean_dec(v___x_293_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_313_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = lean_array_get_size(v_preDefsNonrec_226_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_nat_dec_lt(v___x_239_, v___x_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_301_; 
lean_dec_ref_known(v___x_285_, 14);
lean_dec(v_declNames_261_);
lean_dec_ref(v_docCtx_224_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_298_);
v___x_301_ = v___x_295_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_le(v___x_297_, v___x_297_);
if (v___x_303_ == 0)
{
if (v___x_299_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref_known(v___x_285_, 14);
lean_dec(v_declNames_261_);
lean_dec_ref(v_docCtx_224_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_298_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_298_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
lean_del_object(v___x_295_);
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_297_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_224_, v___x_262_, v_declNames_261_, v_cacheProofs_228_, v_preDefsNonrec_226_, v___x_307_, v___x_308_, v___x_298_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_285_, v___y_282_);
lean_dec_ref_known(v___x_285_, 14);
return v___x_309_;
}
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
lean_del_object(v___x_295_);
v___x_310_ = ((size_t)0ULL);
v___x_311_ = lean_usize_of_nat(v___x_297_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_224_, v___x_262_, v_declNames_261_, v_cacheProofs_228_, v_preDefsNonrec_226_, v___x_310_, v___x_311_, v___x_298_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_285_, v___y_282_);
lean_dec_ref_known(v___x_285_, 14);
return v___x_312_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_285_, 14);
lean_dec(v_declNames_261_);
lean_dec_ref(v_docCtx_224_);
return v___x_293_;
}
}
else
{
lean_object* v_declName_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_declNames_261_);
v_declName_315_ = lean_ctor_get(v_preDefNonRec_258_, 3);
lean_inc(v_declName_315_);
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v_declName_315_);
lean_ctor_set(v___x_317_, 1, v___x_260_);
v___x_318_ = l_Lean_Elab_addNonRec(v_docCtx_224_, v_preDefNonRec_258_, v___x_316_, v___x_317_, v_cacheProofs_228_, v___x_316_, v___x_262_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_285_, v___y_282_);
lean_dec_ref_known(v___x_285_, 14);
return v___x_318_;
}
}
v___jp_319_:
{
if (v___y_320_ == 0)
{
lean_object* v___x_321_; lean_object* v_env_322_; lean_object* v_nextMacroScope_323_; lean_object* v_ngen_324_; lean_object* v_auxDeclNGen_325_; lean_object* v_traceState_326_; lean_object* v_messages_327_; lean_object* v_infoState_328_; lean_object* v_snapshotTasks_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_339_; 
v___x_321_ = lean_st_ref_take(v_a_234_);
v_env_322_ = lean_ctor_get(v___x_321_, 0);
v_nextMacroScope_323_ = lean_ctor_get(v___x_321_, 1);
v_ngen_324_ = lean_ctor_get(v___x_321_, 2);
v_auxDeclNGen_325_ = lean_ctor_get(v___x_321_, 3);
v_traceState_326_ = lean_ctor_get(v___x_321_, 4);
v_messages_327_ = lean_ctor_get(v___x_321_, 6);
v_infoState_328_ = lean_ctor_get(v___x_321_, 7);
v_snapshotTasks_329_ = lean_ctor_get(v___x_321_, 8);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v___x_321_, 5);
lean_dec(v_unused_340_);
v___x_331_ = v___x_321_;
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snapshotTasks_329_);
lean_inc(v_infoState_328_);
lean_inc(v_messages_327_);
lean_inc(v_traceState_326_);
lean_inc(v_auxDeclNGen_325_);
lean_inc(v_ngen_324_);
lean_inc(v_nextMacroScope_323_);
lean_inc(v_env_322_);
lean_dec(v___x_321_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_333_ = l_Lean_Kernel_enableDiag(v_env_322_, v___x_267_);
v___x_334_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 5, v___x_334_);
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_336_ = v___x_331_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_nextMacroScope_323_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_ngen_324_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_auxDeclNGen_325_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_traceState_326_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_338_, 6, v_messages_327_);
lean_ctor_set(v_reuseFailAlloc_338_, 7, v_infoState_328_);
lean_ctor_set(v_reuseFailAlloc_338_, 8, v_snapshotTasks_329_);
v___x_336_ = v_reuseFailAlloc_338_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_st_ref_put(v_a_234_, v___x_336_);
v_fileName_269_ = v_fileName_242_;
v_fileMap_270_ = v_fileMap_243_;
v_currRecDepth_271_ = v_currRecDepth_245_;
v_ref_272_ = v_ref_246_;
v_currNamespace_273_ = v_currNamespace_247_;
v_openDecls_274_ = v_openDecls_248_;
v_initHeartbeats_275_ = v_initHeartbeats_249_;
v_maxHeartbeats_276_ = v_maxHeartbeats_250_;
v_quotContext_277_ = v_quotContext_251_;
v_currMacroScope_278_ = v_currMacroScope_252_;
v_cancelTk_x3f_279_ = v_cancelTk_x3f_253_;
v_suppressElabErrors_280_ = v_suppressElabErrors_254_;
v_inheritedTraceOptions_281_ = v_inheritedTraceOptions_255_;
v___y_282_ = v_a_234_;
goto v___jp_268_;
}
}
}
else
{
v_fileName_269_ = v_fileName_242_;
v_fileMap_270_ = v_fileMap_243_;
v_currRecDepth_271_ = v_currRecDepth_245_;
v_ref_272_ = v_ref_246_;
v_currNamespace_273_ = v_currNamespace_247_;
v_openDecls_274_ = v_openDecls_248_;
v_initHeartbeats_275_ = v_initHeartbeats_249_;
v_maxHeartbeats_276_ = v_maxHeartbeats_250_;
v_quotContext_277_ = v_quotContext_251_;
v_currMacroScope_278_ = v_currMacroScope_252_;
v_cancelTk_x3f_279_ = v_cancelTk_x3f_253_;
v_suppressElabErrors_280_ = v_suppressElabErrors_254_;
v_inheritedTraceOptions_281_ = v_inheritedTraceOptions_255_;
v___y_282_ = v_a_234_;
goto v___jp_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_342_, lean_object* v_preDefs_343_, lean_object* v_preDefsNonrec_344_, lean_object* v_unaryPreDefNonRec_345_, lean_object* v_cacheProofs_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
uint8_t v_cacheProofs_boxed_354_; lean_object* v_res_355_; 
v_cacheProofs_boxed_354_ = lean_unbox(v_cacheProofs_346_);
v_res_355_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_342_, v_preDefs_343_, v_preDefsNonrec_344_, v_unaryPreDefNonRec_345_, v_cacheProofs_boxed_354_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_preDefsNonrec_344_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(uint8_t v_flag_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_356_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_flag_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v_flag_boxed_373_; lean_object* v_res_374_; 
v_flag_boxed_373_ = lean_unbox(v_flag_365_);
v_res_374_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_flag_boxed_373_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_00_u03b1_375_, uint8_t v_flag_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_376_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_00_u03b1_386_, lean_object* v_flag_387_, lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
uint8_t v_flag_boxed_396_; lean_object* v_res_397_; 
v_flag_boxed_396_ = lean_unbox(v_flag_387_);
v_res_397_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_00_u03b1_386_, v_flag_boxed_396_, v_x_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_398_, uint8_t v_cacheProofs_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_398_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_Lean_Elab_abstractNestedProofs(v_a_406_, v_cacheProofs_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_407_;
}
else
{
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_408_, lean_object* v_cacheProofs_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
uint8_t v_cacheProofs_boxed_415_; lean_object* v_res_416_; 
v_cacheProofs_boxed_415_ = lean_unbox(v_cacheProofs_409_);
v_res_416_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_408_, v_cacheProofs_boxed_415_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_417_, size_t v_sz_418_, size_t v_i_419_, lean_object* v_b_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_lt(v_i_419_, v_sz_418_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_b_420_);
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v_declName_427_; lean_object* v___x_428_; 
v_a_426_ = lean_array_uget_borrowed(v_as_417_, v_i_419_);
v_declName_427_ = lean_ctor_get(v_a_426_, 3);
lean_inc(v_declName_427_);
v___x_428_ = l_Lean_enableRealizationsForConst(v_declName_427_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; size_t v___x_430_; size_t v___x_431_; 
lean_dec_ref_known(v___x_428_, 1);
v___x_429_ = lean_box(0);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_419_, v___x_430_);
v_i_419_ = v___x_431_;
v_b_420_ = v___x_429_;
goto _start;
}
else
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_433_, lean_object* v_sz_434_, lean_object* v_i_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
size_t v_sz_boxed_440_; size_t v_i_boxed_441_; lean_object* v_res_442_; 
v_sz_boxed_440_ = lean_unbox_usize(v_sz_434_);
lean_dec(v_sz_434_);
v_i_boxed_441_ = lean_unbox_usize(v_i_435_);
lean_dec(v_i_435_);
v_res_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_433_, v_sz_boxed_440_, v_i_boxed_441_, v_b_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v_as_433_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_443_, size_t v_sz_444_, size_t v_i_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_lt(v_i_445_, v_sz_444_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v_b_446_);
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v_declName_455_; lean_object* v___x_456_; 
v_a_454_ = lean_array_uget_borrowed(v_as_443_, v_i_445_);
v_declName_455_ = lean_ctor_get(v_a_454_, 3);
lean_inc(v_declName_455_);
v___x_456_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_455_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_457_; size_t v___x_458_; size_t v___x_459_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_457_ = lean_box(0);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_445_, v___x_458_);
v_i_445_ = v___x_459_;
v_b_446_ = v___x_457_;
goto _start;
}
else
{
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_461_, lean_object* v_sz_462_, lean_object* v_i_463_, lean_object* v_b_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
size_t v_sz_boxed_470_; size_t v_i_boxed_471_; lean_object* v_res_472_; 
v_sz_boxed_470_ = lean_unbox_usize(v_sz_462_);
lean_dec(v_sz_462_);
v_i_boxed_471_ = lean_unbox_usize(v_i_463_);
lean_dec(v_i_463_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_461_, v_sz_boxed_470_, v_i_boxed_471_, v_b_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec_ref(v_as_461_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_473_, size_t v_sz_474_, size_t v_i_475_, lean_object* v_b_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_lt(v_i_475_, v_sz_474_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_b_476_);
return v___x_485_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; 
v_a_486_ = lean_array_uget_borrowed(v_as_473_, v_i_475_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
lean_inc(v_a_486_);
v___x_489_ = lean_array_push(v___x_488_, v_a_486_);
v___x_490_ = 1;
v___x_491_ = l_Lean_Elab_applyAttributesOf(v___x_489_, v___x_490_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec_ref(v___x_489_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; 
lean_dec_ref_known(v___x_491_, 1);
v___x_492_ = lean_box(0);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_475_, v___x_493_);
v_i_475_ = v___x_494_;
v_b_476_ = v___x_492_;
goto _start;
}
else
{
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
size_t v_sz_boxed_507_; size_t v_i_boxed_508_; lean_object* v_res_509_; 
v_sz_boxed_507_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_508_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_496_, v_sz_boxed_507_, v_i_boxed_508_, v_b_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_as_496_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_511_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
lean_ctor_set(v___x_511_, 2, v___x_510_);
lean_ctor_set(v___x_511_, 3, v___x_510_);
lean_ctor_set(v___x_511_, 4, v___x_510_);
lean_ctor_set(v___x_511_, 5, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_512_, uint8_t v_s_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_env_518_; lean_object* v_nextMacroScope_519_; lean_object* v_ngen_520_; lean_object* v_auxDeclNGen_521_; lean_object* v_traceState_522_; lean_object* v_messages_523_; lean_object* v_infoState_524_; lean_object* v_snapshotTasks_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_554_; 
v___x_517_ = lean_st_ref_take(v___y_515_);
v_env_518_ = lean_ctor_get(v___x_517_, 0);
v_nextMacroScope_519_ = lean_ctor_get(v___x_517_, 1);
v_ngen_520_ = lean_ctor_get(v___x_517_, 2);
v_auxDeclNGen_521_ = lean_ctor_get(v___x_517_, 3);
v_traceState_522_ = lean_ctor_get(v___x_517_, 4);
v_messages_523_ = lean_ctor_get(v___x_517_, 6);
v_infoState_524_ = lean_ctor_get(v___x_517_, 7);
v_snapshotTasks_525_ = lean_ctor_get(v___x_517_, 8);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_517_, 5);
lean_dec(v_unused_555_);
v___x_527_ = v___x_517_;
v_isShared_528_ = v_isSharedCheck_554_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snapshotTasks_525_);
lean_inc(v_infoState_524_);
lean_inc(v_messages_523_);
lean_inc(v_traceState_522_);
lean_inc(v_auxDeclNGen_521_);
lean_inc(v_ngen_520_);
lean_inc(v_nextMacroScope_519_);
lean_inc(v_env_518_);
lean_dec(v___x_517_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_554_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_529_ = 0;
v___x_530_ = lean_box(0);
v___x_531_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_518_, v_declName_512_, v_s_513_, v___x_529_, v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 5, v___x_532_);
lean_ctor_set(v___x_527_, 0, v___x_531_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_ngen_520_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_auxDeclNGen_521_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_traceState_522_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_messages_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_infoState_524_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_snapshotTasks_525_);
v___x_534_ = v_reuseFailAlloc_553_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_mctx_537_; lean_object* v_zetaDeltaFVarIds_538_; lean_object* v_postponed_539_; lean_object* v_diag_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v___x_535_ = lean_st_ref_put(v___y_515_, v___x_534_);
v___x_536_ = lean_st_ref_take(v___y_514_);
v_mctx_537_ = lean_ctor_get(v___x_536_, 0);
v_zetaDeltaFVarIds_538_ = lean_ctor_get(v___x_536_, 2);
v_postponed_539_ = lean_ctor_get(v___x_536_, 3);
v_diag_540_ = lean_ctor_get(v___x_536_, 4);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_536_, 1);
lean_dec(v_unused_552_);
v___x_542_ = v___x_536_;
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_diag_540_);
lean_inc(v_postponed_539_);
lean_inc(v_zetaDeltaFVarIds_538_);
lean_inc(v_mctx_537_);
lean_dec(v___x_536_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_mctx_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_zetaDeltaFVarIds_538_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_postponed_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_diag_540_);
v___x_546_ = v_reuseFailAlloc_550_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_st_ref_put(v___y_514_, v___x_546_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_556_, lean_object* v_s_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_s_boxed_561_; lean_object* v_res_562_; 
v_s_boxed_561_ = lean_unbox(v_s_557_);
v_res_562_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_556_, v_s_boxed_561_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec(v___y_558_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_571_; lean_object* v___x_572_; 
v___x_571_ = 2;
v___x_572_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_563_, v___x_571_, v___y_567_, v___y_569_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_581_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_594_, lean_object* v_as_595_, size_t v_i_596_, size_t v_stop_597_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_eq(v_i_596_, v_stop_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v_name_600_; lean_object* v___x_601_; uint8_t v___x_602_; uint8_t v___x_603_; uint8_t v___y_605_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_599_ = lean_array_uget_borrowed(v_as_595_, v_i_596_);
v_name_600_ = lean_ctor_get(v___x_599_, 0);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_nat_dec_lt(v___x_601_, v___x_594_);
v___x_603_ = 1;
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_610_ = lean_name_eq(v_name_600_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_612_ = lean_name_eq(v_name_600_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_614_ = lean_name_eq(v_name_600_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_616_ = lean_name_eq(v_name_600_, v___x_615_);
v___y_605_ = v___x_616_;
goto v___jp_604_;
}
else
{
v___y_605_ = v___x_602_;
goto v___jp_604_;
}
}
else
{
v___y_605_ = v___x_602_;
goto v___jp_604_;
}
}
else
{
v___y_605_ = v___x_602_;
goto v___jp_604_;
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
size_t v___x_606_; size_t v___x_607_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_596_, v___x_606_);
v_i_596_ = v___x_607_;
goto _start;
}
else
{
return v___x_603_;
}
}
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_618_, lean_object* v_as_619_, lean_object* v_i_620_, lean_object* v_stop_621_){
_start:
{
size_t v_i_boxed_622_; size_t v_stop_boxed_623_; uint8_t v_res_624_; lean_object* v_r_625_; 
v_i_boxed_622_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_stop_boxed_623_ = lean_unbox_usize(v_stop_621_);
lean_dec(v_stop_621_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_618_, v_as_619_, v_i_boxed_622_, v_stop_boxed_623_);
lean_dec_ref(v_as_619_);
lean_dec(v___x_618_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_626_, size_t v_sz_627_, size_t v_i_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_a_638_; uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_lt(v_i_628_, v_sz_627_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_b_629_);
return v___x_643_;
}
else
{
lean_object* v_a_644_; uint8_t v_kind_645_; lean_object* v_modifiers_646_; lean_object* v___x_647_; uint8_t v___x_651_; 
v_a_644_ = lean_array_uget_borrowed(v_as_626_, v_i_628_);
v_kind_645_ = lean_ctor_get_uint8(v_a_644_, sizeof(void*)*9);
v_modifiers_646_ = lean_ctor_get(v_a_644_, 2);
v___x_647_ = lean_box(0);
v___x_651_ = l_Lean_Elab_DefKind_isTheorem(v_kind_645_);
if (v___x_651_ == 0)
{
lean_object* v_attrs_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_attrs_652_ = lean_ctor_get(v_modifiers_646_, 2);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_array_get_size(v_attrs_652_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
goto v___jp_648_;
}
else
{
if (v___x_655_ == 0)
{
goto v___jp_648_;
}
else
{
size_t v___x_656_; size_t v___x_657_; uint8_t v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_654_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_654_, v_attrs_652_, v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
goto v___jp_648_;
}
else
{
v_a_638_ = v___x_647_;
goto v___jp_637_;
}
}
}
}
else
{
v_a_638_ = v___x_647_;
goto v___jp_637_;
}
v___jp_648_:
{
lean_object* v_declName_649_; lean_object* v___x_650_; 
v_declName_649_ = lean_ctor_get(v_a_644_, 3);
lean_inc(v_declName_649_);
v___x_650_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_649_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_dec_ref_known(v___x_650_, 1);
v_a_638_ = v___x_647_;
goto v___jp_637_;
}
else
{
return v___x_650_;
}
}
}
v___jp_637_:
{
size_t v___x_639_; size_t v___x_640_; 
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_add(v_i_628_, v___x_639_);
v_i_628_ = v___x_640_;
v_b_629_ = v_a_638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_659_, lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
size_t v_sz_boxed_670_; size_t v_i_boxed_671_; lean_object* v_res_672_; 
v_sz_boxed_670_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_671_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_659_, v_sz_boxed_670_, v_i_boxed_671_, v_b_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v_as_659_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; size_t v_sz_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_681_ = lean_box(0);
v_sz_682_ = lean_array_size(v_preDefs_673_);
v___x_683_ = ((size_t)0ULL);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_673_, v_sz_682_, v___x_683_, v___x_681_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v___x_685_; 
lean_dec_ref_known(v___x_684_, 1);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_673_, v_sz_682_, v___x_683_, v___x_681_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v___x_686_; size_t v_sz_687_; lean_object* v___x_688_; 
lean_dec_ref_known(v___x_685_, 1);
lean_inc_ref(v_preDefs_673_);
v___x_686_ = l_Array_reverse___redArg(v_preDefs_673_);
v_sz_687_ = lean_array_size(v___x_686_);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_686_, v_sz_687_, v___x_683_, v___x_681_, v_a_678_, v_a_679_);
lean_dec_ref(v___x_686_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; 
lean_dec_ref_known(v___x_688_, 1);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_673_, v_sz_682_, v___x_683_, v___x_681_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec_ref(v_preDefs_673_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v___x_689_, 0);
lean_dec(v_unused_697_);
v___x_691_ = v___x_689_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_dec(v___x_689_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_681_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_681_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
return v___x_689_;
}
}
else
{
lean_dec_ref(v_preDefs_673_);
return v___x_688_;
}
}
else
{
lean_dec_ref(v_preDefs_673_);
return v___x_685_;
}
}
else
{
lean_dec_ref(v_preDefs_673_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_707_, uint8_t v_s_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_707_, v_s_708_, v___y_712_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_717_, lean_object* v_s_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v_s_boxed_726_; lean_object* v_res_727_; 
v_s_boxed_726_ = lean_unbox(v_s_718_);
v_res_727_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_717_, v_s_boxed_726_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_728_, size_t v_sz_729_, size_t v_i_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_728_, v_sz_729_, v_i_730_, v_b_731_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_740_, lean_object* v_sz_741_, lean_object* v_i_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
size_t v_sz_boxed_751_; size_t v_i_boxed_752_; lean_object* v_res_753_; 
v_sz_boxed_751_ = lean_unbox_usize(v_sz_741_);
lean_dec(v_sz_741_);
v_i_boxed_752_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_740_, v_sz_boxed_751_, v_i_boxed_752_, v_b_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v_as_740_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_754_, v_sz_755_, v_i_756_, v_b_757_, v___y_762_, v___y_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
size_t v_sz_boxed_777_; size_t v_i_boxed_778_; lean_object* v_res_779_; 
v_sz_boxed_777_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_778_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_766_, v_sz_boxed_777_, v_i_boxed_778_, v_b_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec_ref(v_as_766_);
return v_res_779_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
