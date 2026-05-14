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
lean_object* v___x_41_; lean_object* v_infoState_42_; lean_object* v_env_43_; lean_object* v_nextMacroScope_44_; lean_object* v_ngen_45_; lean_object* v_auxDeclNGen_46_; lean_object* v_traceState_47_; lean_object* v_cache_48_; lean_object* v_messages_49_; lean_object* v_snapshotTasks_50_; lean_object* v_newDecls_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_71_; 
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
v_newDecls_51_ = lean_ctor_get(v___x_41_, 9);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_71_ == 0)
{
v___x_53_ = v___x_41_;
v_isShared_54_ = v_isSharedCheck_71_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_newDecls_51_);
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
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_71_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_assignment_55_; lean_object* v_lazyAssignment_56_; lean_object* v_trees_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_70_; 
v_assignment_55_ = lean_ctor_get(v_infoState_42_, 0);
v_lazyAssignment_56_ = lean_ctor_get(v_infoState_42_, 1);
v_trees_57_ = lean_ctor_get(v_infoState_42_, 2);
v_isSharedCheck_70_ = !lean_is_exclusive(v_infoState_42_);
if (v_isSharedCheck_70_ == 0)
{
v___x_59_ = v_infoState_42_;
v_isShared_60_ = v_isSharedCheck_70_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_trees_57_);
lean_inc(v_lazyAssignment_56_);
lean_inc(v_assignment_55_);
lean_dec(v_infoState_42_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_70_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_assignment_55_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_lazyAssignment_56_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_trees_57_);
v___x_62_ = v_reuseFailAlloc_69_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_64_; 
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*3, v_flag_38_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 7, v___x_62_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_env_43_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_nextMacroScope_44_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v_ngen_45_);
lean_ctor_set(v_reuseFailAlloc_68_, 3, v_auxDeclNGen_46_);
lean_ctor_set(v_reuseFailAlloc_68_, 4, v_traceState_47_);
lean_ctor_set(v_reuseFailAlloc_68_, 5, v_cache_48_);
lean_ctor_set(v_reuseFailAlloc_68_, 6, v_messages_49_);
lean_ctor_set(v_reuseFailAlloc_68_, 7, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_68_, 8, v_snapshotTasks_50_);
lean_ctor_set(v_reuseFailAlloc_68_, 9, v_newDecls_51_);
v___x_64_ = v_reuseFailAlloc_68_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_st_ref_set(v___y_39_, v___x_64_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg___boxed(lean_object* v_flag_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
uint8_t v_flag_boxed_75_; lean_object* v_res_76_; 
v_flag_boxed_75_ = lean_unbox(v_flag_72_);
v_res_76_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_boxed_75_, v___y_73_);
lean_dec(v___y_73_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(uint8_t v_flag_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; lean_object* v_infoState_87_; uint8_t v_enabled_88_; lean_object* v_a_90_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_86_ = lean_st_ref_get(v___y_84_);
v_infoState_87_ = lean_ctor_get(v___x_86_, 7);
lean_inc_ref(v_infoState_87_);
lean_dec(v___x_86_);
v_enabled_88_ = lean_ctor_get_uint8(v_infoState_87_, sizeof(void*)*3);
lean_dec_ref(v_infoState_87_);
v___x_100_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_77_, v___y_84_);
lean_dec_ref(v___x_100_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
v___x_101_ = lean_apply_7(v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, lean_box(0));
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_88_, v___y_84_);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v___x_103_, 0);
lean_dec(v_unused_111_);
v___x_105_ = v___x_103_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_dec(v___x_103_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v_a_102_);
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_102_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
else
{
lean_object* v_a_112_; 
v_a_112_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v___x_101_);
v_a_90_ = v_a_112_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v___x_91_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_enabled_88_, v___y_84_);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v___x_91_, 0);
lean_dec(v_unused_99_);
v___x_93_ = v___x_91_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_dec(v___x_91_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
lean_ctor_set(v___x_93_, 0, v_a_90_);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_90_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg___boxed(lean_object* v_flag_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v_flag_boxed_122_; lean_object* v_res_123_; 
v_flag_boxed_122_ = lean_unbox(v_flag_113_);
v_res_123_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_boxed_122_, v_x_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
if (lean_obj_tag(v_a_124_) == 0)
{
lean_object* v___x_126_; 
v___x_126_ = l_List_reverse___redArg(v_a_125_);
return v___x_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_137_; 
v_head_127_ = lean_ctor_get(v_a_124_, 0);
v_tail_128_ = lean_ctor_get(v_a_124_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_a_124_);
if (v_isSharedCheck_137_ == 0)
{
v___x_130_ = v_a_124_;
v_isShared_131_ = v_isSharedCheck_137_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_tail_128_);
lean_inc(v_head_127_);
lean_dec(v_a_124_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_137_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_declName_132_; lean_object* v___x_134_; 
v_declName_132_ = lean_ctor_get(v_head_127_, 3);
lean_inc(v_declName_132_);
lean_dec(v_head_127_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_a_125_);
lean_ctor_set(v___x_130_, 0, v_declName_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_declName_132_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_a_125_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v_a_124_ = v_tail_128_;
v_a_125_ = v___x_134_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(lean_object* v_o_141_, lean_object* v_k_142_, uint8_t v_v_143_){
_start:
{
lean_object* v_map_144_; uint8_t v_hasTrace_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_159_; 
v_map_144_ = lean_ctor_get(v_o_141_, 0);
v_hasTrace_145_ = lean_ctor_get_uint8(v_o_141_, sizeof(void*)*1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_o_141_);
if (v_isSharedCheck_159_ == 0)
{
v___x_147_ = v_o_141_;
v_isShared_148_ = v_isSharedCheck_159_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_map_144_);
lean_dec(v_o_141_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_159_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_149_, 0, v_v_143_);
lean_inc(v_k_142_);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_142_, v___x_149_, v_map_144_);
if (v_hasTrace_145_ == 0)
{
lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_154_; 
v___x_151_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1));
v___x_152_ = l_Lean_Name_isPrefixOf(v___x_151_, v_k_142_);
lean_dec(v_k_142_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_154_ = v___x_147_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_150_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_152_);
return v___x_154_;
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v_k_142_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_157_ = v___x_147_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*1, v_hasTrace_145_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___boxed(lean_object* v_o_160_, lean_object* v_k_161_, lean_object* v_v_162_){
_start:
{
uint8_t v_v_boxed_163_; lean_object* v_res_164_; 
v_v_boxed_163_ = lean_unbox(v_v_162_);
v_res_164_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_o_160_, v_k_161_, v_v_boxed_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object* v_opts_165_, lean_object* v_opt_166_, uint8_t v_val_167_){
_start:
{
lean_object* v_name_168_; lean_object* v___x_169_; 
v_name_168_ = lean_ctor_get(v_opt_166_, 0);
lean_inc(v_name_168_);
lean_dec_ref(v_opt_166_);
v___x_169_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_opts_165_, v_name_168_, v_val_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object* v_opts_170_, lean_object* v_opt_171_, lean_object* v_val_172_){
_start:
{
uint8_t v_val_boxed_173_; lean_object* v_res_174_; 
v_val_boxed_173_ = lean_unbox(v_val_172_);
v_res_174_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_opts_170_, v_opt_171_, v_val_boxed_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(lean_object* v_docCtx_175_, lean_object* v_declNames_176_, uint8_t v_cacheProofs_177_, lean_object* v_as_178_, size_t v_i_179_, size_t v_stop_180_, lean_object* v_b_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
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
lean_inc_ref(v_docCtx_175_);
v___x_192_ = l_Lean_Elab_addNonRec(v_docCtx_175_, v___x_191_, v___x_189_, v_declNames_176_, v_cacheProofs_177_, v___x_189_, v___x_190_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; size_t v___x_194_; size_t v___x_195_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref(v___x_192_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_179_, v___x_194_);
v_i_179_ = v___x_195_;
v_b_181_ = v_a_193_;
goto _start;
}
else
{
lean_dec(v_declNames_176_);
lean_dec_ref(v_docCtx_175_);
return v___x_192_;
}
}
else
{
lean_object* v___x_197_; 
lean_dec(v_declNames_176_);
lean_dec_ref(v_docCtx_175_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_b_181_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5___boxed(lean_object* v_docCtx_198_, lean_object* v_declNames_199_, lean_object* v_cacheProofs_200_, lean_object* v_as_201_, lean_object* v_i_202_, lean_object* v_stop_203_, lean_object* v_b_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v_cacheProofs_boxed_212_; size_t v_i_boxed_213_; size_t v_stop_boxed_214_; lean_object* v_res_215_; 
v_cacheProofs_boxed_212_ = lean_unbox(v_cacheProofs_200_);
v_i_boxed_213_ = lean_unbox_usize(v_i_202_);
lean_dec(v_i_202_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_203_);
lean_dec(v_stop_203_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_198_, v_declNames_199_, v_cacheProofs_boxed_212_, v_as_201_, v_i_boxed_213_, v_stop_boxed_214_, v_b_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec_ref(v_as_201_);
return v_res_215_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object* v_docCtx_222_, lean_object* v_preDefs_223_, lean_object* v_preDefsNonrec_224_, lean_object* v_unaryPreDefNonRec_225_, uint8_t v_cacheProofs_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_declName_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_declName_238_; lean_object* v___x_239_; lean_object* v_fileName_240_; lean_object* v_fileMap_241_; lean_object* v_options_242_; lean_object* v_currRecDepth_243_; lean_object* v_ref_244_; lean_object* v_currNamespace_245_; lean_object* v_openDecls_246_; lean_object* v_initHeartbeats_247_; lean_object* v_maxHeartbeats_248_; lean_object* v_quotContext_249_; lean_object* v_currMacroScope_250_; lean_object* v_cancelTk_x3f_251_; uint8_t v_suppressElabErrors_252_; lean_object* v_inheritedTraceOptions_253_; lean_object* v_env_254_; lean_object* v___f_255_; uint8_t v___x_256_; lean_object* v_preDefNonRec_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_declNames_260_; lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v_fileName_267_; lean_object* v_fileMap_268_; lean_object* v_currRecDepth_269_; lean_object* v_ref_270_; lean_object* v_currNamespace_271_; lean_object* v_openDecls_272_; lean_object* v_initHeartbeats_273_; lean_object* v_maxHeartbeats_274_; lean_object* v_quotContext_275_; lean_object* v_currMacroScope_276_; lean_object* v_cancelTk_x3f_277_; uint8_t v_suppressElabErrors_278_; lean_object* v_inheritedTraceOptions_279_; lean_object* v___y_280_; uint8_t v___y_318_; uint8_t v___x_340_; 
v_declName_234_ = lean_ctor_get(v_unaryPreDefNonRec_225_, 3);
v___x_235_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_array_get_borrowed(v___x_235_, v_preDefs_223_, v___x_236_);
v_declName_238_ = lean_ctor_get(v___x_237_, 3);
v___x_239_ = lean_st_ref_get(v_a_232_);
v_fileName_240_ = lean_ctor_get(v_a_231_, 0);
v_fileMap_241_ = lean_ctor_get(v_a_231_, 1);
v_options_242_ = lean_ctor_get(v_a_231_, 2);
v_currRecDepth_243_ = lean_ctor_get(v_a_231_, 3);
v_ref_244_ = lean_ctor_get(v_a_231_, 5);
v_currNamespace_245_ = lean_ctor_get(v_a_231_, 6);
v_openDecls_246_ = lean_ctor_get(v_a_231_, 7);
v_initHeartbeats_247_ = lean_ctor_get(v_a_231_, 8);
v_maxHeartbeats_248_ = lean_ctor_get(v_a_231_, 9);
v_quotContext_249_ = lean_ctor_get(v_a_231_, 10);
v_currMacroScope_250_ = lean_ctor_get(v_a_231_, 11);
v_cancelTk_x3f_251_ = lean_ctor_get(v_a_231_, 12);
v_suppressElabErrors_252_ = lean_ctor_get_uint8(v_a_231_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_253_ = lean_ctor_get(v_a_231_, 13);
v_env_254_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_env_254_);
lean_dec(v___x_239_);
v___f_255_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v___x_256_ = lean_name_eq(v_declName_234_, v_declName_238_);
v_preDefNonRec_257_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_225_, v___f_255_);
v___x_258_ = lean_array_to_list(v_preDefs_223_);
v___x_259_ = lean_box(0);
v_declNames_260_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_258_, v___x_259_);
v___x_261_ = l_Lean_allowUnsafeReducibility;
v___x_262_ = 1;
lean_inc_ref(v_options_242_);
v___x_263_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_options_242_, v___x_261_, v___x_262_);
v___x_264_ = l_Lean_diagnostics;
v___x_265_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v___x_263_, v___x_264_);
v___x_340_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_254_);
lean_dec_ref(v_env_254_);
if (v___x_340_ == 0)
{
if (v___x_265_ == 0)
{
v_fileName_267_ = v_fileName_240_;
v_fileMap_268_ = v_fileMap_241_;
v_currRecDepth_269_ = v_currRecDepth_243_;
v_ref_270_ = v_ref_244_;
v_currNamespace_271_ = v_currNamespace_245_;
v_openDecls_272_ = v_openDecls_246_;
v_initHeartbeats_273_ = v_initHeartbeats_247_;
v_maxHeartbeats_274_ = v_maxHeartbeats_248_;
v_quotContext_275_ = v_quotContext_249_;
v_currMacroScope_276_ = v_currMacroScope_250_;
v_cancelTk_x3f_277_ = v_cancelTk_x3f_251_;
v_suppressElabErrors_278_ = v_suppressElabErrors_252_;
v_inheritedTraceOptions_279_ = v_inheritedTraceOptions_253_;
v___y_280_ = v_a_232_;
goto v___jp_266_;
}
else
{
v___y_318_ = v___x_340_;
goto v___jp_317_;
}
}
else
{
v___y_318_ = v___x_265_;
goto v___jp_317_;
}
v___jp_266_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = l_Lean_maxRecDepth;
v___x_282_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v___x_263_, v___x_281_);
lean_inc_ref(v_inheritedTraceOptions_279_);
lean_inc(v_cancelTk_x3f_277_);
lean_inc(v_currMacroScope_276_);
lean_inc(v_quotContext_275_);
lean_inc(v_maxHeartbeats_274_);
lean_inc(v_initHeartbeats_273_);
lean_inc(v_openDecls_272_);
lean_inc(v_currNamespace_271_);
lean_inc(v_ref_270_);
lean_inc(v_currRecDepth_269_);
lean_inc_ref(v_fileMap_268_);
lean_inc_ref(v_fileName_267_);
v___x_283_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_283_, 0, v_fileName_267_);
lean_ctor_set(v___x_283_, 1, v_fileMap_268_);
lean_ctor_set(v___x_283_, 2, v___x_263_);
lean_ctor_set(v___x_283_, 3, v_currRecDepth_269_);
lean_ctor_set(v___x_283_, 4, v___x_282_);
lean_ctor_set(v___x_283_, 5, v_ref_270_);
lean_ctor_set(v___x_283_, 6, v_currNamespace_271_);
lean_ctor_set(v___x_283_, 7, v_openDecls_272_);
lean_ctor_set(v___x_283_, 8, v_initHeartbeats_273_);
lean_ctor_set(v___x_283_, 9, v_maxHeartbeats_274_);
lean_ctor_set(v___x_283_, 10, v_quotContext_275_);
lean_ctor_set(v___x_283_, 11, v_currMacroScope_276_);
lean_ctor_set(v___x_283_, 12, v_cancelTk_x3f_277_);
lean_ctor_set(v___x_283_, 13, v_inheritedTraceOptions_279_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*14, v___x_265_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*14 + 1, v_suppressElabErrors_278_);
if (v___x_256_ == 0)
{
lean_object* v_declName_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_declName_284_ = lean_ctor_get(v_preDefNonRec_257_, 3);
lean_inc(v_declName_284_);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v_declName_284_);
lean_ctor_set(v___x_285_, 1, v___x_259_);
v___x_286_ = lean_box(v___x_256_);
v___x_287_ = lean_box(v_cacheProofs_226_);
v___x_288_ = lean_box(v___x_256_);
v___x_289_ = lean_box(v___x_262_);
lean_inc_ref(v_docCtx_222_);
v___x_290_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 14, 7);
lean_closure_set(v___x_290_, 0, v_docCtx_222_);
lean_closure_set(v___x_290_, 1, v_preDefNonRec_257_);
lean_closure_set(v___x_290_, 2, v___x_286_);
lean_closure_set(v___x_290_, 3, v___x_285_);
lean_closure_set(v___x_290_, 4, v___x_287_);
lean_closure_set(v___x_290_, 5, v___x_288_);
lean_closure_set(v___x_290_, 6, v___x_289_);
v___x_291_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v___x_256_, v___x_290_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v___x_283_, v___y_280_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v___x_291_, 0);
lean_dec(v_unused_312_);
v___x_293_ = v___x_291_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_dec(v___x_291_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_array_get_size(v_preDefsNonrec_224_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_nat_dec_lt(v___x_236_, v___x_295_);
if (v___x_297_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v___x_283_);
lean_dec(v_declNames_260_);
lean_dec_ref(v_docCtx_222_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_299_ = v___x_293_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_296_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
uint8_t v___x_301_; 
v___x_301_ = lean_nat_dec_le(v___x_295_, v___x_295_);
if (v___x_301_ == 0)
{
if (v___x_297_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_283_);
lean_dec(v_declNames_260_);
lean_dec_ref(v_docCtx_222_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_303_ = v___x_293_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_296_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
lean_del_object(v___x_293_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_295_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_222_, v_declNames_260_, v_cacheProofs_226_, v_preDefsNonrec_224_, v___x_305_, v___x_306_, v___x_296_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v___x_283_, v___y_280_);
lean_dec_ref(v___x_283_);
return v___x_307_;
}
}
else
{
size_t v___x_308_; size_t v___x_309_; lean_object* v___x_310_; 
lean_del_object(v___x_293_);
v___x_308_ = ((size_t)0ULL);
v___x_309_ = lean_usize_of_nat(v___x_295_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_222_, v_declNames_260_, v_cacheProofs_226_, v_preDefsNonrec_224_, v___x_308_, v___x_309_, v___x_296_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v___x_283_, v___y_280_);
lean_dec_ref(v___x_283_);
return v___x_310_;
}
}
}
}
else
{
lean_dec_ref(v___x_283_);
lean_dec(v_declNames_260_);
lean_dec_ref(v_docCtx_222_);
return v___x_291_;
}
}
else
{
lean_object* v_declName_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_declNames_260_);
v_declName_313_ = lean_ctor_get(v_preDefNonRec_257_, 3);
lean_inc(v_declName_313_);
v___x_314_ = 0;
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_declName_313_);
lean_ctor_set(v___x_315_, 1, v___x_259_);
v___x_316_ = l_Lean_Elab_addNonRec(v_docCtx_222_, v_preDefNonRec_257_, v___x_314_, v___x_315_, v_cacheProofs_226_, v___x_314_, v___x_262_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v___x_283_, v___y_280_);
lean_dec_ref(v___x_283_);
return v___x_316_;
}
}
v___jp_317_:
{
if (v___y_318_ == 0)
{
lean_object* v___x_319_; lean_object* v_env_320_; lean_object* v_nextMacroScope_321_; lean_object* v_ngen_322_; lean_object* v_auxDeclNGen_323_; lean_object* v_traceState_324_; lean_object* v_messages_325_; lean_object* v_infoState_326_; lean_object* v_snapshotTasks_327_; lean_object* v_newDecls_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_338_; 
v___x_319_ = lean_st_ref_take(v_a_232_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
v_nextMacroScope_321_ = lean_ctor_get(v___x_319_, 1);
v_ngen_322_ = lean_ctor_get(v___x_319_, 2);
v_auxDeclNGen_323_ = lean_ctor_get(v___x_319_, 3);
v_traceState_324_ = lean_ctor_get(v___x_319_, 4);
v_messages_325_ = lean_ctor_get(v___x_319_, 6);
v_infoState_326_ = lean_ctor_get(v___x_319_, 7);
v_snapshotTasks_327_ = lean_ctor_get(v___x_319_, 8);
v_newDecls_328_ = lean_ctor_get(v___x_319_, 9);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v___x_319_, 5);
lean_dec(v_unused_339_);
v___x_330_ = v___x_319_;
v_isShared_331_ = v_isSharedCheck_338_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_newDecls_328_);
lean_inc(v_snapshotTasks_327_);
lean_inc(v_infoState_326_);
lean_inc(v_messages_325_);
lean_inc(v_traceState_324_);
lean_inc(v_auxDeclNGen_323_);
lean_inc(v_ngen_322_);
lean_inc(v_nextMacroScope_321_);
lean_inc(v_env_320_);
lean_dec(v___x_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_338_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = l_Lean_Kernel_enableDiag(v_env_320_, v___x_265_);
v___x_333_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 5, v___x_333_);
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_nextMacroScope_321_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_ngen_322_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_auxDeclNGen_323_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_traceState_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_messages_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v_infoState_326_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v_snapshotTasks_327_);
lean_ctor_set(v_reuseFailAlloc_337_, 9, v_newDecls_328_);
v___x_335_ = v_reuseFailAlloc_337_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; 
v___x_336_ = lean_st_ref_set(v_a_232_, v___x_335_);
v_fileName_267_ = v_fileName_240_;
v_fileMap_268_ = v_fileMap_241_;
v_currRecDepth_269_ = v_currRecDepth_243_;
v_ref_270_ = v_ref_244_;
v_currNamespace_271_ = v_currNamespace_245_;
v_openDecls_272_ = v_openDecls_246_;
v_initHeartbeats_273_ = v_initHeartbeats_247_;
v_maxHeartbeats_274_ = v_maxHeartbeats_248_;
v_quotContext_275_ = v_quotContext_249_;
v_currMacroScope_276_ = v_currMacroScope_250_;
v_cancelTk_x3f_277_ = v_cancelTk_x3f_251_;
v_suppressElabErrors_278_ = v_suppressElabErrors_252_;
v_inheritedTraceOptions_279_ = v_inheritedTraceOptions_253_;
v___y_280_ = v_a_232_;
goto v___jp_266_;
}
}
}
else
{
v_fileName_267_ = v_fileName_240_;
v_fileMap_268_ = v_fileMap_241_;
v_currRecDepth_269_ = v_currRecDepth_243_;
v_ref_270_ = v_ref_244_;
v_currNamespace_271_ = v_currNamespace_245_;
v_openDecls_272_ = v_openDecls_246_;
v_initHeartbeats_273_ = v_initHeartbeats_247_;
v_maxHeartbeats_274_ = v_maxHeartbeats_248_;
v_quotContext_275_ = v_quotContext_249_;
v_currMacroScope_276_ = v_currMacroScope_250_;
v_cancelTk_x3f_277_ = v_cancelTk_x3f_251_;
v_suppressElabErrors_278_ = v_suppressElabErrors_252_;
v_inheritedTraceOptions_279_ = v_inheritedTraceOptions_253_;
v___y_280_ = v_a_232_;
goto v___jp_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_341_, lean_object* v_preDefs_342_, lean_object* v_preDefsNonrec_343_, lean_object* v_unaryPreDefNonRec_344_, lean_object* v_cacheProofs_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
uint8_t v_cacheProofs_boxed_353_; lean_object* v_res_354_; 
v_cacheProofs_boxed_353_ = lean_unbox(v_cacheProofs_345_);
v_res_354_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_341_, v_preDefs_342_, v_preDefsNonrec_343_, v_unaryPreDefNonRec_344_, v_cacheProofs_boxed_353_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_preDefsNonrec_343_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(uint8_t v_flag_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_355_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_flag_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v_flag_boxed_372_; lean_object* v_res_373_; 
v_flag_boxed_372_ = lean_unbox(v_flag_364_);
v_res_373_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_flag_boxed_372_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_00_u03b1_374_, uint8_t v_flag_375_, lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_375_, v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_00_u03b1_385_, lean_object* v_flag_386_, lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_flag_boxed_395_; lean_object* v_res_396_; 
v_flag_boxed_395_ = lean_unbox(v_flag_386_);
v_res_396_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_00_u03b1_385_, v_flag_boxed_395_, v_x_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_397_, uint8_t v_cacheProofs_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_397_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref(v___x_404_);
v___x_406_ = l_Lean_Elab_abstractNestedProofs(v_a_405_, v_cacheProofs_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v___x_406_;
}
else
{
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_407_, lean_object* v_cacheProofs_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_cacheProofs_boxed_414_; lean_object* v_res_415_; 
v_cacheProofs_boxed_414_ = lean_unbox(v_cacheProofs_408_);
v_res_415_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_407_, v_cacheProofs_boxed_414_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_416_, size_t v_sz_417_, size_t v_i_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_lt(v_i_418_, v_sz_417_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v_b_419_);
return v___x_424_;
}
else
{
lean_object* v_a_425_; lean_object* v_declName_426_; lean_object* v___x_427_; 
v_a_425_ = lean_array_uget_borrowed(v_as_416_, v_i_418_);
v_declName_426_ = lean_ctor_get(v_a_425_, 3);
lean_inc(v_declName_426_);
v___x_427_ = l_Lean_enableRealizationsForConst(v_declName_426_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; size_t v___x_429_; size_t v___x_430_; 
lean_dec_ref(v___x_427_);
v___x_428_ = lean_box(0);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_add(v_i_418_, v___x_429_);
v_i_418_ = v___x_430_;
v_b_419_ = v___x_428_;
goto _start;
}
else
{
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_432_, lean_object* v_sz_433_, lean_object* v_i_434_, lean_object* v_b_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
size_t v_sz_boxed_439_; size_t v_i_boxed_440_; lean_object* v_res_441_; 
v_sz_boxed_439_ = lean_unbox_usize(v_sz_433_);
lean_dec(v_sz_433_);
v_i_boxed_440_ = lean_unbox_usize(v_i_434_);
lean_dec(v_i_434_);
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_432_, v_sz_boxed_439_, v_i_boxed_440_, v_b_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v_as_432_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_442_, size_t v_sz_443_, size_t v_i_444_, lean_object* v_b_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_lt(v_i_444_, v_sz_443_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_b_445_);
return v___x_452_;
}
else
{
lean_object* v_a_453_; lean_object* v_declName_454_; lean_object* v___x_455_; 
v_a_453_ = lean_array_uget_borrowed(v_as_442_, v_i_444_);
v_declName_454_ = lean_ctor_get(v_a_453_, 3);
lean_inc(v_declName_454_);
v___x_455_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_454_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; size_t v___x_457_; size_t v___x_458_; 
lean_dec_ref(v___x_455_);
v___x_456_ = lean_box(0);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_444_, v___x_457_);
v_i_444_ = v___x_458_;
v_b_445_ = v___x_456_;
goto _start;
}
else
{
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_460_, lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
size_t v_sz_boxed_469_; size_t v_i_boxed_470_; lean_object* v_res_471_; 
v_sz_boxed_469_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_470_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_460_, v_sz_boxed_469_, v_i_boxed_470_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec_ref(v_as_460_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_472_, size_t v_sz_473_, size_t v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_b_475_);
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v_a_485_ = lean_array_uget_borrowed(v_as_472_, v_i_474_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_mk_empty_array_with_capacity(v___x_486_);
lean_inc(v_a_485_);
v___x_488_ = lean_array_push(v___x_487_, v_a_485_);
v___x_489_ = 1;
v___x_490_ = l_Lean_Elab_applyAttributesOf(v___x_488_, v___x_489_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec_ref(v___x_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; 
lean_dec_ref(v___x_490_);
v___x_491_ = lean_box(0);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_474_, v___x_492_);
v_i_474_ = v___x_493_;
v_b_475_ = v___x_491_;
goto _start;
}
else
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_495_, lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_507_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_495_, v_sz_boxed_506_, v_i_boxed_507_, v_b_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_as_495_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_510_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_ctor_set(v___x_510_, 2, v___x_509_);
lean_ctor_set(v___x_510_, 3, v___x_509_);
lean_ctor_set(v___x_510_, 4, v___x_509_);
lean_ctor_set(v___x_510_, 5, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_511_, uint8_t v_s_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; lean_object* v_env_517_; lean_object* v_nextMacroScope_518_; lean_object* v_ngen_519_; lean_object* v_auxDeclNGen_520_; lean_object* v_traceState_521_; lean_object* v_messages_522_; lean_object* v_infoState_523_; lean_object* v_snapshotTasks_524_; lean_object* v_newDecls_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_554_; 
v___x_516_ = lean_st_ref_take(v___y_514_);
v_env_517_ = lean_ctor_get(v___x_516_, 0);
v_nextMacroScope_518_ = lean_ctor_get(v___x_516_, 1);
v_ngen_519_ = lean_ctor_get(v___x_516_, 2);
v_auxDeclNGen_520_ = lean_ctor_get(v___x_516_, 3);
v_traceState_521_ = lean_ctor_get(v___x_516_, 4);
v_messages_522_ = lean_ctor_get(v___x_516_, 6);
v_infoState_523_ = lean_ctor_get(v___x_516_, 7);
v_snapshotTasks_524_ = lean_ctor_get(v___x_516_, 8);
v_newDecls_525_ = lean_ctor_get(v___x_516_, 9);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_516_, 5);
lean_dec(v_unused_555_);
v___x_527_ = v___x_516_;
v_isShared_528_ = v_isSharedCheck_554_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_newDecls_525_);
lean_inc(v_snapshotTasks_524_);
lean_inc(v_infoState_523_);
lean_inc(v_messages_522_);
lean_inc(v_traceState_521_);
lean_inc(v_auxDeclNGen_520_);
lean_inc(v_ngen_519_);
lean_inc(v_nextMacroScope_518_);
lean_inc(v_env_517_);
lean_dec(v___x_516_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_554_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_529_ = 0;
v___x_530_ = lean_box(0);
v___x_531_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_517_, v_declName_511_, v_s_512_, v___x_529_, v___x_530_);
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
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_nextMacroScope_518_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_ngen_519_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_auxDeclNGen_520_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_traceState_521_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_messages_522_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_infoState_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_snapshotTasks_524_);
lean_ctor_set(v_reuseFailAlloc_553_, 9, v_newDecls_525_);
v___x_534_ = v_reuseFailAlloc_553_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_mctx_537_; lean_object* v_zetaDeltaFVarIds_538_; lean_object* v_postponed_539_; lean_object* v_diag_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v___x_535_ = lean_st_ref_set(v___y_514_, v___x_534_);
v___x_536_ = lean_st_ref_take(v___y_513_);
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
v___x_547_ = lean_st_ref_set(v___y_513_, v___x_546_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v_as_594_, size_t v_i_595_, size_t v_stop_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_eq(v_i_595_, v_stop_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v_name_599_; uint8_t v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_598_ = lean_array_uget_borrowed(v_as_594_, v_i_595_);
v_name_599_ = lean_ctor_get(v___x_598_, 0);
v___x_600_ = 1;
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_602_ = lean_name_eq(v_name_599_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_604_ = lean_name_eq(v_name_599_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_606_ = lean_name_eq(v_name_599_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_608_ = lean_name_eq(v_name_599_, v___x_607_);
if (v___x_608_ == 0)
{
size_t v___x_609_; size_t v___x_610_; 
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_595_, v___x_609_);
v_i_595_ = v___x_610_;
goto _start;
}
else
{
return v___x_600_;
}
}
else
{
return v___x_600_;
}
}
else
{
return v___x_600_;
}
}
else
{
return v___x_600_;
}
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v_as_613_, lean_object* v_i_614_, lean_object* v_stop_615_){
_start:
{
size_t v_i_boxed_616_; size_t v_stop_boxed_617_; uint8_t v_res_618_; lean_object* v_r_619_; 
v_i_boxed_616_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_stop_boxed_617_ = lean_unbox_usize(v_stop_615_);
lean_dec(v_stop_615_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_as_613_, v_i_boxed_616_, v_stop_boxed_617_);
lean_dec_ref(v_as_613_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_620_, size_t v_sz_621_, size_t v_i_622_, lean_object* v_b_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_a_632_; uint8_t v___x_636_; 
v___x_636_ = lean_usize_dec_lt(v_i_622_, v_sz_621_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_b_623_);
return v___x_637_;
}
else
{
lean_object* v_a_638_; uint8_t v_kind_639_; lean_object* v_modifiers_640_; lean_object* v___x_641_; uint8_t v___y_643_; uint8_t v___x_646_; 
v_a_638_ = lean_array_uget_borrowed(v_as_620_, v_i_622_);
v_kind_639_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*9);
v_modifiers_640_ = lean_ctor_get(v_a_638_, 2);
v___x_641_ = lean_box(0);
v___x_646_ = l_Lean_Elab_DefKind_isTheorem(v_kind_639_);
if (v___x_646_ == 0)
{
lean_object* v_attrs_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_attrs_647_ = lean_ctor_get(v_modifiers_640_, 2);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_array_get_size(v_attrs_647_);
v___x_650_ = lean_nat_dec_lt(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
v___y_643_ = v___x_646_;
goto v___jp_642_;
}
else
{
if (v___x_650_ == 0)
{
v___y_643_ = v___x_646_;
goto v___jp_642_;
}
else
{
size_t v___x_651_; size_t v___x_652_; uint8_t v___x_653_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_649_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_attrs_647_, v___x_651_, v___x_652_);
v___y_643_ = v___x_653_;
goto v___jp_642_;
}
}
}
else
{
v_a_632_ = v___x_641_;
goto v___jp_631_;
}
v___jp_642_:
{
if (v___y_643_ == 0)
{
lean_object* v_declName_644_; lean_object* v___x_645_; 
v_declName_644_ = lean_ctor_get(v_a_638_, 3);
lean_inc(v_declName_644_);
v___x_645_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_644_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref(v___x_645_);
v_a_632_ = v___x_641_;
goto v___jp_631_;
}
else
{
return v___x_645_;
}
}
else
{
v_a_632_ = v___x_641_;
goto v___jp_631_;
}
}
}
v___jp_631_:
{
size_t v___x_633_; size_t v___x_634_; 
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_i_622_, v___x_633_);
v_i_622_ = v___x_634_;
v_b_623_ = v_a_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_sz_boxed_665_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_666_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_654_, v_sz_boxed_665_, v_i_boxed_666_, v_b_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_as_654_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; size_t v_sz_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_box(0);
v_sz_677_ = lean_array_size(v_preDefs_668_);
v___x_678_ = ((size_t)0ULL);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_668_, v_sz_677_, v___x_678_, v___x_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; 
lean_dec_ref(v___x_679_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_668_, v_sz_677_, v___x_678_, v___x_676_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; size_t v_sz_682_; lean_object* v___x_683_; 
lean_dec_ref(v___x_680_);
lean_inc_ref(v_preDefs_668_);
v___x_681_ = l_Array_reverse___redArg(v_preDefs_668_);
v_sz_682_ = lean_array_size(v___x_681_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_681_, v_sz_682_, v___x_678_, v___x_676_, v_a_673_, v_a_674_);
lean_dec_ref(v___x_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v___x_683_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_668_, v_sz_677_, v___x_678_, v___x_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec_ref(v_preDefs_668_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_692_);
v___x_686_ = v___x_684_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_dec(v___x_684_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_676_);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_676_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
return v___x_684_;
}
}
else
{
lean_dec_ref(v_preDefs_668_);
return v___x_683_;
}
}
else
{
lean_dec_ref(v_preDefs_668_);
return v___x_680_;
}
}
else
{
lean_dec_ref(v_preDefs_668_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_702_, uint8_t v_s_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_702_, v_s_703_, v___y_707_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_712_, lean_object* v_s_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
uint8_t v_s_boxed_721_; lean_object* v_res_722_; 
v_s_boxed_721_ = lean_unbox(v_s_713_);
v_res_722_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_712_, v_s_boxed_721_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_723_, v_sz_724_, v_i_725_, v_b_726_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_735_, lean_object* v_sz_736_, lean_object* v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
size_t v_sz_boxed_746_; size_t v_i_boxed_747_; lean_object* v_res_748_; 
v_sz_boxed_746_ = lean_unbox_usize(v_sz_736_);
lean_dec(v_sz_736_);
v_i_boxed_747_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_res_748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_735_, v_sz_boxed_746_, v_i_boxed_747_, v_b_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v_as_735_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_749_, size_t v_sz_750_, size_t v_i_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_749_, v_sz_750_, v_i_751_, v_b_752_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_761_, lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_sz_boxed_772_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_773_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_761_, v_sz_boxed_772_, v_i_boxed_773_, v_b_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v_as_761_);
return v_res_774_;
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
