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
uint8_t v___x_4302__boxed_213_; uint8_t v_cacheProofs_boxed_214_; size_t v_i_boxed_215_; size_t v_stop_boxed_216_; lean_object* v_res_217_; 
v___x_4302__boxed_213_ = lean_unbox(v___x_199_);
v_cacheProofs_boxed_214_ = lean_unbox(v_cacheProofs_201_);
v_i_boxed_215_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_stop_boxed_216_ = lean_unbox_usize(v_stop_204_);
lean_dec(v_stop_204_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_198_, v___x_4302__boxed_213_, v_declNames_200_, v_cacheProofs_boxed_214_, v_as_202_, v_i_boxed_215_, v_stop_boxed_216_, v_b_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
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
lean_object* v___x_236_; lean_object* v_declName_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_declName_241_; lean_object* v_toCold_242_; lean_object* v_options_243_; lean_object* v_currRecDepth_244_; lean_object* v_ref_245_; lean_object* v_currNamespace_246_; lean_object* v_openDecls_247_; lean_object* v_initHeartbeats_248_; lean_object* v_maxHeartbeats_249_; lean_object* v_currMacroScope_250_; uint8_t v_suppressElabErrors_251_; lean_object* v_env_252_; lean_object* v___f_253_; lean_object* v_preDefNonRec_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_declNames_257_; uint8_t v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v_toCold_265_; lean_object* v_currRecDepth_266_; lean_object* v_ref_267_; lean_object* v_currNamespace_268_; lean_object* v_openDecls_269_; lean_object* v_initHeartbeats_270_; lean_object* v_maxHeartbeats_271_; lean_object* v_currMacroScope_272_; uint8_t v_suppressElabErrors_273_; lean_object* v___y_274_; uint8_t v___y_312_; uint8_t v___x_333_; 
v___x_236_ = lean_st_ref_get(v_a_234_);
v_declName_237_ = lean_ctor_get(v_unaryPreDefNonRec_227_, 3);
lean_inc(v_declName_237_);
v___x_238_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_array_get_borrowed(v___x_238_, v_preDefs_225_, v___x_239_);
v_declName_241_ = lean_ctor_get(v___x_240_, 3);
lean_inc(v_declName_241_);
v_toCold_242_ = lean_ctor_get(v_a_233_, 0);
v_options_243_ = lean_ctor_get(v_a_233_, 1);
v_currRecDepth_244_ = lean_ctor_get(v_a_233_, 2);
v_ref_245_ = lean_ctor_get(v_a_233_, 4);
v_currNamespace_246_ = lean_ctor_get(v_a_233_, 5);
v_openDecls_247_ = lean_ctor_get(v_a_233_, 6);
v_initHeartbeats_248_ = lean_ctor_get(v_a_233_, 7);
v_maxHeartbeats_249_ = lean_ctor_get(v_a_233_, 8);
v_currMacroScope_250_ = lean_ctor_get(v_a_233_, 9);
v_suppressElabErrors_251_ = lean_ctor_get_uint8(v_a_233_, sizeof(void*)*10 + 1);
v_env_252_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_env_252_);
lean_dec(v___x_236_);
v___f_253_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v_preDefNonRec_254_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_227_, v___f_253_);
v___x_255_ = lean_array_to_list(v_preDefs_225_);
v___x_256_ = lean_box(0);
v_declNames_257_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_255_, v___x_256_);
v___x_258_ = lean_name_eq(v_declName_237_, v_declName_241_);
lean_dec(v_declName_241_);
lean_dec(v_declName_237_);
v___x_259_ = l_Lean_allowUnsafeReducibility;
v___x_260_ = 1;
lean_inc_ref(v_options_243_);
v___x_261_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_options_243_, v___x_259_, v___x_260_);
v___x_262_ = l_Lean_diagnostics;
v___x_263_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v___x_261_, v___x_262_);
v___x_333_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_252_);
lean_dec_ref(v_env_252_);
if (v___x_263_ == 0)
{
if (v___x_333_ == 0)
{
v_toCold_265_ = v_toCold_242_;
v_currRecDepth_266_ = v_currRecDepth_244_;
v_ref_267_ = v_ref_245_;
v_currNamespace_268_ = v_currNamespace_246_;
v_openDecls_269_ = v_openDecls_247_;
v_initHeartbeats_270_ = v_initHeartbeats_248_;
v_maxHeartbeats_271_ = v_maxHeartbeats_249_;
v_currMacroScope_272_ = v_currMacroScope_250_;
v_suppressElabErrors_273_ = v_suppressElabErrors_251_;
v___y_274_ = v_a_234_;
goto v___jp_264_;
}
else
{
v___y_312_ = v___x_263_;
goto v___jp_311_;
}
}
else
{
v___y_312_ = v___x_333_;
goto v___jp_311_;
}
v___jp_264_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_maxRecDepth;
v___x_276_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v___x_261_, v___x_275_);
lean_inc(v_currMacroScope_272_);
lean_inc(v_maxHeartbeats_271_);
lean_inc(v_initHeartbeats_270_);
lean_inc(v_openDecls_269_);
lean_inc(v_currNamespace_268_);
lean_inc(v_ref_267_);
lean_inc(v_currRecDepth_266_);
lean_inc_ref(v_toCold_265_);
v___x_277_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_277_, 0, v_toCold_265_);
lean_ctor_set(v___x_277_, 1, v___x_261_);
lean_ctor_set(v___x_277_, 2, v_currRecDepth_266_);
lean_ctor_set(v___x_277_, 3, v___x_276_);
lean_ctor_set(v___x_277_, 4, v_ref_267_);
lean_ctor_set(v___x_277_, 5, v_currNamespace_268_);
lean_ctor_set(v___x_277_, 6, v_openDecls_269_);
lean_ctor_set(v___x_277_, 7, v_initHeartbeats_270_);
lean_ctor_set(v___x_277_, 8, v_maxHeartbeats_271_);
lean_ctor_set(v___x_277_, 9, v_currMacroScope_272_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*10, v___x_263_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*10 + 1, v_suppressElabErrors_273_);
if (v___x_258_ == 0)
{
lean_object* v_declName_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_declName_278_ = lean_ctor_get(v_preDefNonRec_254_, 3);
lean_inc(v_declName_278_);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v_declName_278_);
lean_ctor_set(v___x_279_, 1, v___x_256_);
v___x_280_ = lean_box(v___x_258_);
v___x_281_ = lean_box(v_cacheProofs_228_);
v___x_282_ = lean_box(v___x_258_);
v___x_283_ = lean_box(v___x_260_);
lean_inc_ref(v_docCtx_224_);
v___x_284_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 14, 7);
lean_closure_set(v___x_284_, 0, v_docCtx_224_);
lean_closure_set(v___x_284_, 1, v_preDefNonRec_254_);
lean_closure_set(v___x_284_, 2, v___x_280_);
lean_closure_set(v___x_284_, 3, v___x_279_);
lean_closure_set(v___x_284_, 4, v___x_281_);
lean_closure_set(v___x_284_, 5, v___x_282_);
lean_closure_set(v___x_284_, 6, v___x_283_);
v___x_285_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v___x_258_, v___x_284_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_277_, v___y_274_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_305_; 
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_285_, 0);
lean_dec(v_unused_306_);
v___x_287_ = v___x_285_;
v_isShared_288_ = v_isSharedCheck_305_;
goto v_resetjp_286_;
}
else
{
lean_dec(v___x_285_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_305_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_array_get_size(v_preDefsNonrec_226_);
v___x_290_ = lean_box(0);
v___x_291_ = lean_nat_dec_lt(v___x_239_, v___x_289_);
if (v___x_291_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref_known(v___x_277_, 10);
lean_dec(v_declNames_257_);
lean_dec_ref(v_docCtx_224_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_290_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_290_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_le(v___x_289_, v___x_289_);
if (v___x_295_ == 0)
{
if (v___x_291_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref_known(v___x_277_, 10);
lean_dec(v_declNames_257_);
lean_dec_ref(v_docCtx_224_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_290_);
v___x_297_ = v___x_287_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_290_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
lean_del_object(v___x_287_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_289_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_224_, v___x_258_, v_declNames_257_, v_cacheProofs_228_, v_preDefsNonrec_226_, v___x_299_, v___x_300_, v___x_290_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_277_, v___y_274_);
lean_dec_ref_known(v___x_277_, 10);
return v___x_301_;
}
}
else
{
size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; 
lean_del_object(v___x_287_);
v___x_302_ = ((size_t)0ULL);
v___x_303_ = lean_usize_of_nat(v___x_289_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_224_, v___x_258_, v_declNames_257_, v_cacheProofs_228_, v_preDefsNonrec_226_, v___x_302_, v___x_303_, v___x_290_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_277_, v___y_274_);
lean_dec_ref_known(v___x_277_, 10);
return v___x_304_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_277_, 10);
lean_dec(v_declNames_257_);
lean_dec_ref(v_docCtx_224_);
return v___x_285_;
}
}
else
{
lean_object* v_declName_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_declNames_257_);
v_declName_307_ = lean_ctor_get(v_preDefNonRec_254_, 3);
lean_inc(v_declName_307_);
v___x_308_ = 0;
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v_declName_307_);
lean_ctor_set(v___x_309_, 1, v___x_256_);
v___x_310_ = l_Lean_Elab_addNonRec(v_docCtx_224_, v_preDefNonRec_254_, v___x_308_, v___x_309_, v_cacheProofs_228_, v___x_308_, v___x_258_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v___x_277_, v___y_274_);
lean_dec_ref_known(v___x_277_, 10);
return v___x_310_;
}
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v___x_313_; lean_object* v_env_314_; lean_object* v_nextMacroScope_315_; lean_object* v_ngen_316_; lean_object* v_auxDeclNGen_317_; lean_object* v_traceState_318_; lean_object* v_messages_319_; lean_object* v_infoState_320_; lean_object* v_snapshotTasks_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v___x_313_ = lean_st_ref_take(v_a_234_);
v_env_314_ = lean_ctor_get(v___x_313_, 0);
v_nextMacroScope_315_ = lean_ctor_get(v___x_313_, 1);
v_ngen_316_ = lean_ctor_get(v___x_313_, 2);
v_auxDeclNGen_317_ = lean_ctor_get(v___x_313_, 3);
v_traceState_318_ = lean_ctor_get(v___x_313_, 4);
v_messages_319_ = lean_ctor_get(v___x_313_, 6);
v_infoState_320_ = lean_ctor_get(v___x_313_, 7);
v_snapshotTasks_321_ = lean_ctor_get(v___x_313_, 8);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_313_, 5);
lean_dec(v_unused_332_);
v___x_323_ = v___x_313_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_snapshotTasks_321_);
lean_inc(v_infoState_320_);
lean_inc(v_messages_319_);
lean_inc(v_traceState_318_);
lean_inc(v_auxDeclNGen_317_);
lean_inc(v_ngen_316_);
lean_inc(v_nextMacroScope_315_);
lean_inc(v_env_314_);
lean_dec(v___x_313_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = l_Lean_Kernel_enableDiag(v_env_314_, v___x_263_);
v___x_326_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 5, v___x_326_);
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_nextMacroScope_315_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_ngen_316_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_auxDeclNGen_317_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_traceState_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_messages_319_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_infoState_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_snapshotTasks_321_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = lean_st_ref_put(v_a_234_, v___x_328_);
v_toCold_265_ = v_toCold_242_;
v_currRecDepth_266_ = v_currRecDepth_244_;
v_ref_267_ = v_ref_245_;
v_currNamespace_268_ = v_currNamespace_246_;
v_openDecls_269_ = v_openDecls_247_;
v_initHeartbeats_270_ = v_initHeartbeats_248_;
v_maxHeartbeats_271_ = v_maxHeartbeats_249_;
v_currMacroScope_272_ = v_currMacroScope_250_;
v_suppressElabErrors_273_ = v_suppressElabErrors_251_;
v___y_274_ = v_a_234_;
goto v___jp_264_;
}
}
}
else
{
v_toCold_265_ = v_toCold_242_;
v_currRecDepth_266_ = v_currRecDepth_244_;
v_ref_267_ = v_ref_245_;
v_currNamespace_268_ = v_currNamespace_246_;
v_openDecls_269_ = v_openDecls_247_;
v_initHeartbeats_270_ = v_initHeartbeats_248_;
v_maxHeartbeats_271_ = v_maxHeartbeats_249_;
v_currMacroScope_272_ = v_currMacroScope_250_;
v_suppressElabErrors_273_ = v_suppressElabErrors_251_;
v___y_274_ = v_a_234_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_334_, lean_object* v_preDefs_335_, lean_object* v_preDefsNonrec_336_, lean_object* v_unaryPreDefNonRec_337_, lean_object* v_cacheProofs_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
uint8_t v_cacheProofs_boxed_346_; lean_object* v_res_347_; 
v_cacheProofs_boxed_346_ = lean_unbox(v_cacheProofs_338_);
v_res_347_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_334_, v_preDefs_335_, v_preDefsNonrec_336_, v_unaryPreDefNonRec_337_, v_cacheProofs_boxed_346_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec_ref(v_preDefsNonrec_336_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(uint8_t v_flag_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_348_, v___y_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_flag_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v_flag_boxed_365_; lean_object* v_res_366_; 
v_flag_boxed_365_ = lean_unbox(v_flag_357_);
v_res_366_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_flag_boxed_365_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_00_u03b1_367_, uint8_t v_flag_368_, lean_object* v_x_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_368_, v_x_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_00_u03b1_378_, lean_object* v_flag_379_, lean_object* v_x_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v_flag_boxed_388_; lean_object* v_res_389_; 
v_flag_boxed_388_ = lean_unbox(v_flag_379_);
v_res_389_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_00_u03b1_378_, v_flag_boxed_388_, v_x_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_390_, uint8_t v_cacheProofs_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_390_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = l_Lean_Elab_abstractNestedProofs(v_a_398_, v_cacheProofs_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_399_;
}
else
{
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_400_, lean_object* v_cacheProofs_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
uint8_t v_cacheProofs_boxed_407_; lean_object* v_res_408_; 
v_cacheProofs_boxed_407_ = lean_unbox(v_cacheProofs_401_);
v_res_408_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_400_, v_cacheProofs_boxed_407_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_409_, size_t v_sz_410_, size_t v_i_411_, lean_object* v_b_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_lt(v_i_411_, v_sz_410_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_b_412_);
return v___x_417_;
}
else
{
lean_object* v_a_418_; lean_object* v_declName_419_; lean_object* v___x_420_; 
v_a_418_ = lean_array_uget_borrowed(v_as_409_, v_i_411_);
v_declName_419_ = lean_ctor_get(v_a_418_, 3);
lean_inc(v_declName_419_);
v___x_420_ = l_Lean_enableRealizationsForConst(v_declName_419_, v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; size_t v___x_422_; size_t v___x_423_; 
lean_dec_ref_known(v___x_420_, 1);
v___x_421_ = lean_box(0);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_add(v_i_411_, v___x_422_);
v_i_411_ = v___x_423_;
v_b_412_ = v___x_421_;
goto _start;
}
else
{
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_425_, lean_object* v_sz_426_, lean_object* v_i_427_, lean_object* v_b_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
size_t v_sz_boxed_432_; size_t v_i_boxed_433_; lean_object* v_res_434_; 
v_sz_boxed_432_ = lean_unbox_usize(v_sz_426_);
lean_dec(v_sz_426_);
v_i_boxed_433_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_425_, v_sz_boxed_432_, v_i_boxed_433_, v_b_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v_as_425_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_435_, size_t v_sz_436_, size_t v_i_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_437_, v_sz_436_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_b_438_);
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v_declName_447_; lean_object* v___x_448_; 
v_a_446_ = lean_array_uget_borrowed(v_as_435_, v_i_437_);
v_declName_447_ = lean_ctor_get(v_a_446_, 3);
lean_inc(v_declName_447_);
v___x_448_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_447_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; size_t v___x_450_; size_t v___x_451_; 
lean_dec_ref_known(v___x_448_, 1);
v___x_449_ = lean_box(0);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_437_, v___x_450_);
v_i_437_ = v___x_451_;
v_b_438_ = v___x_449_;
goto _start;
}
else
{
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_453_, lean_object* v_sz_454_, lean_object* v_i_455_, lean_object* v_b_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
size_t v_sz_boxed_462_; size_t v_i_boxed_463_; lean_object* v_res_464_; 
v_sz_boxed_462_ = lean_unbox_usize(v_sz_454_);
lean_dec(v_sz_454_);
v_i_boxed_463_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_res_464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_453_, v_sz_boxed_462_, v_i_boxed_463_, v_b_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec_ref(v_as_453_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_465_, size_t v_sz_466_, size_t v_i_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_lt(v_i_467_, v_sz_466_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_b_468_);
return v___x_477_;
}
else
{
lean_object* v_a_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; 
v_a_478_ = lean_array_uget_borrowed(v_as_465_, v_i_467_);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_mk_empty_array_with_capacity(v___x_479_);
lean_inc(v_a_478_);
v___x_481_ = lean_array_push(v___x_480_, v_a_478_);
v___x_482_ = 1;
v___x_483_ = l_Lean_Elab_applyAttributesOf(v___x_481_, v___x_482_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec_ref(v___x_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; size_t v___x_485_; size_t v___x_486_; 
lean_dec_ref_known(v___x_483_, 1);
v___x_484_ = lean_box(0);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_467_, v___x_485_);
v_i_467_ = v___x_486_;
v_b_468_ = v___x_484_;
goto _start;
}
else
{
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_488_, lean_object* v_sz_489_, lean_object* v_i_490_, lean_object* v_b_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_489_);
lean_dec(v_sz_489_);
v_i_boxed_500_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_488_, v_sz_boxed_499_, v_i_boxed_500_, v_b_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v_as_488_);
return v_res_501_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_503_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
lean_ctor_set(v___x_503_, 3, v___x_502_);
lean_ctor_set(v___x_503_, 4, v___x_502_);
lean_ctor_set(v___x_503_, 5, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_504_, uint8_t v_s_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; lean_object* v_env_510_; lean_object* v_nextMacroScope_511_; lean_object* v_ngen_512_; lean_object* v_auxDeclNGen_513_; lean_object* v_traceState_514_; lean_object* v_messages_515_; lean_object* v_infoState_516_; lean_object* v_snapshotTasks_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_546_; 
v___x_509_ = lean_st_ref_take(v___y_507_);
v_env_510_ = lean_ctor_get(v___x_509_, 0);
v_nextMacroScope_511_ = lean_ctor_get(v___x_509_, 1);
v_ngen_512_ = lean_ctor_get(v___x_509_, 2);
v_auxDeclNGen_513_ = lean_ctor_get(v___x_509_, 3);
v_traceState_514_ = lean_ctor_get(v___x_509_, 4);
v_messages_515_ = lean_ctor_get(v___x_509_, 6);
v_infoState_516_ = lean_ctor_get(v___x_509_, 7);
v_snapshotTasks_517_ = lean_ctor_get(v___x_509_, 8);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v___x_509_, 5);
lean_dec(v_unused_547_);
v___x_519_ = v___x_509_;
v_isShared_520_ = v_isSharedCheck_546_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snapshotTasks_517_);
lean_inc(v_infoState_516_);
lean_inc(v_messages_515_);
lean_inc(v_traceState_514_);
lean_inc(v_auxDeclNGen_513_);
lean_inc(v_ngen_512_);
lean_inc(v_nextMacroScope_511_);
lean_inc(v_env_510_);
lean_dec(v___x_509_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_546_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_521_ = 0;
v___x_522_ = lean_box(0);
v___x_523_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_510_, v_declName_504_, v_s_505_, v___x_521_, v___x_522_);
v___x_524_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 5, v___x_524_);
lean_ctor_set(v___x_519_, 0, v___x_523_);
v___x_526_ = v___x_519_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextMacroScope_511_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_ngen_512_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_auxDeclNGen_513_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_traceState_514_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_messages_515_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_infoState_516_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_snapshotTasks_517_);
v___x_526_ = v_reuseFailAlloc_545_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_mctx_529_; lean_object* v_zetaDeltaFVarIds_530_; lean_object* v_postponed_531_; lean_object* v_diag_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_543_; 
v___x_527_ = lean_st_ref_put(v___y_507_, v___x_526_);
v___x_528_ = lean_st_ref_take(v___y_506_);
v_mctx_529_ = lean_ctor_get(v___x_528_, 0);
v_zetaDeltaFVarIds_530_ = lean_ctor_get(v___x_528_, 2);
v_postponed_531_ = lean_ctor_get(v___x_528_, 3);
v_diag_532_ = lean_ctor_get(v___x_528_, 4);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_528_, 1);
lean_dec(v_unused_544_);
v___x_534_ = v___x_528_;
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_diag_532_);
lean_inc(v_postponed_531_);
lean_inc(v_zetaDeltaFVarIds_530_);
lean_inc(v_mctx_529_);
lean_dec(v___x_528_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_mctx_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_zetaDeltaFVarIds_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_postponed_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_diag_532_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_st_ref_put(v___y_506_, v___x_538_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_548_, lean_object* v_s_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
uint8_t v_s_boxed_553_; lean_object* v_res_554_; 
v_s_boxed_553_ = lean_unbox(v_s_549_);
v_res_554_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_548_, v_s_boxed_553_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v___y_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_563_; lean_object* v___x_564_; 
v___x_563_ = 2;
v___x_564_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_555_, v___x_563_, v___y_559_, v___y_561_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_573_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_586_, lean_object* v_as_587_, size_t v_i_588_, size_t v_stop_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_eq(v_i_588_, v_stop_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v_name_592_; lean_object* v___x_593_; uint8_t v___x_594_; uint8_t v___x_595_; uint8_t v___y_597_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_591_ = lean_array_uget_borrowed(v_as_587_, v_i_588_);
v_name_592_ = lean_ctor_get(v___x_591_, 0);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_nat_dec_lt(v___x_593_, v___x_586_);
v___x_595_ = 1;
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_602_ = lean_name_eq(v_name_592_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_604_ = lean_name_eq(v_name_592_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_606_ = lean_name_eq(v_name_592_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_608_ = lean_name_eq(v_name_592_, v___x_607_);
v___y_597_ = v___x_608_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_594_;
goto v___jp_596_;
}
}
else
{
v___y_597_ = v___x_594_;
goto v___jp_596_;
}
}
else
{
v___y_597_ = v___x_594_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
size_t v___x_598_; size_t v___x_599_; 
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_add(v_i_588_, v___x_598_);
v_i_588_ = v___x_599_;
goto _start;
}
else
{
return v___x_595_;
}
}
}
else
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_610_, lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_stop_613_){
_start:
{
size_t v_i_boxed_614_; size_t v_stop_boxed_615_; uint8_t v_res_616_; lean_object* v_r_617_; 
v_i_boxed_614_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_stop_boxed_615_ = lean_unbox_usize(v_stop_613_);
lean_dec(v_stop_613_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_610_, v_as_611_, v_i_boxed_614_, v_stop_boxed_615_);
lean_dec_ref(v_as_611_);
lean_dec(v___x_610_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_a_630_; uint8_t v___x_634_; 
v___x_634_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_b_621_);
return v___x_635_;
}
else
{
lean_object* v_a_636_; uint8_t v_kind_637_; lean_object* v_modifiers_638_; lean_object* v___x_639_; uint8_t v___x_643_; 
v_a_636_ = lean_array_uget_borrowed(v_as_618_, v_i_620_);
v_kind_637_ = lean_ctor_get_uint8(v_a_636_, sizeof(void*)*9);
v_modifiers_638_ = lean_ctor_get(v_a_636_, 2);
v___x_639_ = lean_box(0);
v___x_643_ = l_Lean_Elab_DefKind_isTheorem(v_kind_637_);
if (v___x_643_ == 0)
{
lean_object* v_attrs_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_attrs_644_ = lean_ctor_get(v_modifiers_638_, 2);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_array_get_size(v_attrs_644_);
v___x_647_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
goto v___jp_640_;
}
else
{
if (v___x_647_ == 0)
{
goto v___jp_640_;
}
else
{
size_t v___x_648_; size_t v___x_649_; uint8_t v___x_650_; 
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_646_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_646_, v_attrs_644_, v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
goto v___jp_640_;
}
else
{
v_a_630_ = v___x_639_;
goto v___jp_629_;
}
}
}
}
else
{
v_a_630_ = v___x_639_;
goto v___jp_629_;
}
v___jp_640_:
{
lean_object* v_declName_641_; lean_object* v___x_642_; 
v_declName_641_ = lean_ctor_get(v_a_636_, 3);
lean_inc(v_declName_641_);
v___x_642_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_641_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_dec_ref_known(v___x_642_, 1);
v_a_630_ = v___x_639_;
goto v___jp_629_;
}
else
{
return v___x_642_;
}
}
}
v___jp_629_:
{
size_t v___x_631_; size_t v___x_632_; 
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_620_, v___x_631_);
v_i_620_ = v___x_632_;
v_b_621_ = v_a_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_651_, lean_object* v_sz_652_, lean_object* v_i_653_, lean_object* v_b_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_652_);
lean_dec(v_sz_652_);
v_i_boxed_663_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_651_, v_sz_boxed_662_, v_i_boxed_663_, v_b_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec_ref(v_as_651_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_box(0);
v_sz_674_ = lean_array_size(v_preDefs_665_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_665_, v_sz_674_, v___x_675_, v___x_673_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_677_; 
lean_dec_ref_known(v___x_676_, 1);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_665_, v_sz_674_, v___x_675_, v___x_673_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; size_t v_sz_679_; lean_object* v___x_680_; 
lean_dec_ref_known(v___x_677_, 1);
lean_inc_ref(v_preDefs_665_);
v___x_678_ = l_Array_reverse___redArg(v_preDefs_665_);
v_sz_679_ = lean_array_size(v___x_678_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_678_, v_sz_679_, v___x_675_, v___x_673_, v_a_670_, v_a_671_);
lean_dec_ref(v___x_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; 
lean_dec_ref_known(v___x_680_, 1);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_665_, v_sz_674_, v___x_675_, v___x_673_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_preDefs_665_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_689_);
v___x_683_ = v___x_681_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_dec(v___x_681_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_673_);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_673_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
return v___x_681_;
}
}
else
{
lean_dec_ref(v_preDefs_665_);
return v___x_680_;
}
}
else
{
lean_dec_ref(v_preDefs_665_);
return v___x_677_;
}
}
else
{
lean_dec_ref(v_preDefs_665_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_699_, uint8_t v_s_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_699_, v_s_700_, v___y_704_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_709_, lean_object* v_s_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v_s_boxed_718_; lean_object* v_res_719_; 
v_s_boxed_718_ = lean_unbox(v_s_710_);
v_res_719_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_709_, v_s_boxed_718_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_720_, v_sz_721_, v_i_722_, v_b_723_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
size_t v_sz_boxed_743_; size_t v_i_boxed_744_; lean_object* v_res_745_; 
v_sz_boxed_743_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_744_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_732_, v_sz_boxed_743_, v_i_boxed_744_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_as_732_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_746_, size_t v_sz_747_, size_t v_i_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_746_, v_sz_747_, v_i_748_, v_b_749_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v_sz_boxed_769_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_770_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_758_, v_sz_boxed_769_, v_i_boxed_770_, v_b_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_as_758_);
return v_res_771_;
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
