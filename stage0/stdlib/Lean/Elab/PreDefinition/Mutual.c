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
lean_dec_ref(v___x_100_);
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
lean_dec_ref(v___x_100_);
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
lean_dec(v_declNames_175_);
lean_dec_ref(v_docCtx_174_);
return v___x_191_;
}
}
else
{
lean_object* v___x_196_; 
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
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
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
lean_object* v_declName_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_declName_237_; lean_object* v___x_238_; lean_object* v_fileName_239_; lean_object* v_fileMap_240_; lean_object* v_options_241_; lean_object* v_currRecDepth_242_; lean_object* v_ref_243_; lean_object* v_currNamespace_244_; lean_object* v_openDecls_245_; lean_object* v_initHeartbeats_246_; lean_object* v_maxHeartbeats_247_; lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_cancelTk_x3f_250_; uint8_t v_suppressElabErrors_251_; lean_object* v_inheritedTraceOptions_252_; lean_object* v_env_253_; lean_object* v___f_254_; uint8_t v___x_255_; lean_object* v_preDefNonRec_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_declNames_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v_fileName_266_; lean_object* v_fileMap_267_; lean_object* v_currRecDepth_268_; lean_object* v_ref_269_; lean_object* v_currNamespace_270_; lean_object* v_openDecls_271_; lean_object* v_initHeartbeats_272_; lean_object* v_maxHeartbeats_273_; lean_object* v_quotContext_274_; lean_object* v_currMacroScope_275_; lean_object* v_cancelTk_x3f_276_; uint8_t v_suppressElabErrors_277_; lean_object* v_inheritedTraceOptions_278_; lean_object* v___y_279_; uint8_t v___y_317_; uint8_t v___x_338_; 
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
v_env_253_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_env_253_);
lean_dec(v___x_238_);
v___f_254_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v___x_255_ = lean_name_eq(v_declName_233_, v_declName_237_);
v_preDefNonRec_256_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_224_, v___f_254_);
v___x_257_ = lean_array_to_list(v_preDefs_222_);
v___x_258_ = lean_box(0);
v_declNames_259_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_257_, v___x_258_);
v___x_260_ = l_Lean_allowUnsafeReducibility;
v___x_261_ = 1;
lean_inc_ref(v_options_241_);
v___x_262_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_options_241_, v___x_260_, v___x_261_);
v___x_263_ = l_Lean_diagnostics;
v___x_264_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v___x_262_, v___x_263_);
v___x_338_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_253_);
lean_dec_ref(v_env_253_);
if (v___x_338_ == 0)
{
if (v___x_264_ == 0)
{
v_fileName_266_ = v_fileName_239_;
v_fileMap_267_ = v_fileMap_240_;
v_currRecDepth_268_ = v_currRecDepth_242_;
v_ref_269_ = v_ref_243_;
v_currNamespace_270_ = v_currNamespace_244_;
v_openDecls_271_ = v_openDecls_245_;
v_initHeartbeats_272_ = v_initHeartbeats_246_;
v_maxHeartbeats_273_ = v_maxHeartbeats_247_;
v_quotContext_274_ = v_quotContext_248_;
v_currMacroScope_275_ = v_currMacroScope_249_;
v_cancelTk_x3f_276_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_277_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_278_ = v_inheritedTraceOptions_252_;
v___y_279_ = v_a_231_;
goto v___jp_265_;
}
else
{
v___y_317_ = v___x_338_;
goto v___jp_316_;
}
}
else
{
v___y_317_ = v___x_264_;
goto v___jp_316_;
}
v___jp_265_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = l_Lean_maxRecDepth;
v___x_281_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v___x_262_, v___x_280_);
lean_inc_ref(v_inheritedTraceOptions_278_);
lean_inc(v_cancelTk_x3f_276_);
lean_inc(v_currMacroScope_275_);
lean_inc(v_quotContext_274_);
lean_inc(v_maxHeartbeats_273_);
lean_inc(v_initHeartbeats_272_);
lean_inc(v_openDecls_271_);
lean_inc(v_currNamespace_270_);
lean_inc(v_ref_269_);
lean_inc(v_currRecDepth_268_);
lean_inc_ref(v_fileMap_267_);
lean_inc_ref(v_fileName_266_);
v___x_282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_282_, 0, v_fileName_266_);
lean_ctor_set(v___x_282_, 1, v_fileMap_267_);
lean_ctor_set(v___x_282_, 2, v___x_262_);
lean_ctor_set(v___x_282_, 3, v_currRecDepth_268_);
lean_ctor_set(v___x_282_, 4, v___x_281_);
lean_ctor_set(v___x_282_, 5, v_ref_269_);
lean_ctor_set(v___x_282_, 6, v_currNamespace_270_);
lean_ctor_set(v___x_282_, 7, v_openDecls_271_);
lean_ctor_set(v___x_282_, 8, v_initHeartbeats_272_);
lean_ctor_set(v___x_282_, 9, v_maxHeartbeats_273_);
lean_ctor_set(v___x_282_, 10, v_quotContext_274_);
lean_ctor_set(v___x_282_, 11, v_currMacroScope_275_);
lean_ctor_set(v___x_282_, 12, v_cancelTk_x3f_276_);
lean_ctor_set(v___x_282_, 13, v_inheritedTraceOptions_278_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14, v___x_264_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14 + 1, v_suppressElabErrors_277_);
if (v___x_255_ == 0)
{
lean_object* v_declName_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_declName_283_ = lean_ctor_get(v_preDefNonRec_256_, 3);
lean_inc(v_declName_283_);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v_declName_283_);
lean_ctor_set(v___x_284_, 1, v___x_258_);
v___x_285_ = lean_box(v___x_255_);
v___x_286_ = lean_box(v_cacheProofs_225_);
v___x_287_ = lean_box(v___x_255_);
v___x_288_ = lean_box(v___x_261_);
lean_inc_ref(v_docCtx_221_);
v___x_289_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 14, 7);
lean_closure_set(v___x_289_, 0, v_docCtx_221_);
lean_closure_set(v___x_289_, 1, v_preDefNonRec_256_);
lean_closure_set(v___x_289_, 2, v___x_285_);
lean_closure_set(v___x_289_, 3, v___x_284_);
lean_closure_set(v___x_289_, 4, v___x_286_);
lean_closure_set(v___x_289_, 5, v___x_287_);
lean_closure_set(v___x_289_, 6, v___x_288_);
v___x_290_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v___x_255_, v___x_289_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_282_, v___y_279_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_310_; 
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v___x_290_, 0);
lean_dec(v_unused_311_);
v___x_292_ = v___x_290_;
v_isShared_293_ = v_isSharedCheck_310_;
goto v_resetjp_291_;
}
else
{
lean_dec(v___x_290_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_310_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_array_get_size(v_preDefsNonrec_223_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_nat_dec_lt(v___x_235_, v___x_294_);
if (v___x_296_ == 0)
{
lean_object* v___x_298_; 
lean_dec_ref(v___x_282_);
lean_dec(v_declNames_259_);
lean_dec_ref(v_docCtx_221_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_295_);
v___x_298_ = v___x_292_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_295_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_le(v___x_294_, v___x_294_);
if (v___x_300_ == 0)
{
if (v___x_296_ == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_282_);
lean_dec(v_declNames_259_);
lean_dec_ref(v_docCtx_221_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_295_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_295_);
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
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
lean_del_object(v___x_292_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_294_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_221_, v_declNames_259_, v_cacheProofs_225_, v_preDefsNonrec_223_, v___x_304_, v___x_305_, v___x_295_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_282_, v___y_279_);
lean_dec_ref(v___x_282_);
return v___x_306_;
}
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
lean_del_object(v___x_292_);
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_294_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__5(v_docCtx_221_, v_declNames_259_, v_cacheProofs_225_, v_preDefsNonrec_223_, v___x_307_, v___x_308_, v___x_295_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_282_, v___y_279_);
lean_dec_ref(v___x_282_);
return v___x_309_;
}
}
}
}
else
{
lean_dec_ref(v___x_282_);
lean_dec(v_declNames_259_);
lean_dec_ref(v_docCtx_221_);
return v___x_290_;
}
}
else
{
lean_object* v_declName_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_declNames_259_);
v_declName_312_ = lean_ctor_get(v_preDefNonRec_256_, 3);
lean_inc(v_declName_312_);
v___x_313_ = 0;
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v_declName_312_);
lean_ctor_set(v___x_314_, 1, v___x_258_);
v___x_315_ = l_Lean_Elab_addNonRec(v_docCtx_221_, v_preDefNonRec_256_, v___x_313_, v___x_314_, v_cacheProofs_225_, v___x_313_, v___x_261_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v___x_282_, v___y_279_);
lean_dec_ref(v___x_282_);
return v___x_315_;
}
}
v___jp_316_:
{
if (v___y_317_ == 0)
{
lean_object* v___x_318_; lean_object* v_env_319_; lean_object* v_nextMacroScope_320_; lean_object* v_ngen_321_; lean_object* v_auxDeclNGen_322_; lean_object* v_traceState_323_; lean_object* v_messages_324_; lean_object* v_infoState_325_; lean_object* v_snapshotTasks_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_336_; 
v___x_318_ = lean_st_ref_take(v_a_231_);
v_env_319_ = lean_ctor_get(v___x_318_, 0);
v_nextMacroScope_320_ = lean_ctor_get(v___x_318_, 1);
v_ngen_321_ = lean_ctor_get(v___x_318_, 2);
v_auxDeclNGen_322_ = lean_ctor_get(v___x_318_, 3);
v_traceState_323_ = lean_ctor_get(v___x_318_, 4);
v_messages_324_ = lean_ctor_get(v___x_318_, 6);
v_infoState_325_ = lean_ctor_get(v___x_318_, 7);
v_snapshotTasks_326_ = lean_ctor_get(v___x_318_, 8);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_318_, 5);
lean_dec(v_unused_337_);
v___x_328_ = v___x_318_;
v_isShared_329_ = v_isSharedCheck_336_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snapshotTasks_326_);
lean_inc(v_infoState_325_);
lean_inc(v_messages_324_);
lean_inc(v_traceState_323_);
lean_inc(v_auxDeclNGen_322_);
lean_inc(v_ngen_321_);
lean_inc(v_nextMacroScope_320_);
lean_inc(v_env_319_);
lean_dec(v___x_318_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_336_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = l_Lean_Kernel_enableDiag(v_env_319_, v___x_264_);
v___x_331_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 5, v___x_331_);
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_nextMacroScope_320_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_ngen_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_auxDeclNGen_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_traceState_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 5, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_335_, 6, v_messages_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 7, v_infoState_325_);
lean_ctor_set(v_reuseFailAlloc_335_, 8, v_snapshotTasks_326_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_st_ref_set(v_a_231_, v___x_333_);
v_fileName_266_ = v_fileName_239_;
v_fileMap_267_ = v_fileMap_240_;
v_currRecDepth_268_ = v_currRecDepth_242_;
v_ref_269_ = v_ref_243_;
v_currNamespace_270_ = v_currNamespace_244_;
v_openDecls_271_ = v_openDecls_245_;
v_initHeartbeats_272_ = v_initHeartbeats_246_;
v_maxHeartbeats_273_ = v_maxHeartbeats_247_;
v_quotContext_274_ = v_quotContext_248_;
v_currMacroScope_275_ = v_currMacroScope_249_;
v_cancelTk_x3f_276_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_277_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_278_ = v_inheritedTraceOptions_252_;
v___y_279_ = v_a_231_;
goto v___jp_265_;
}
}
}
else
{
v_fileName_266_ = v_fileName_239_;
v_fileMap_267_ = v_fileMap_240_;
v_currRecDepth_268_ = v_currRecDepth_242_;
v_ref_269_ = v_ref_243_;
v_currNamespace_270_ = v_currNamespace_244_;
v_openDecls_271_ = v_openDecls_245_;
v_initHeartbeats_272_ = v_initHeartbeats_246_;
v_maxHeartbeats_273_ = v_maxHeartbeats_247_;
v_quotContext_274_ = v_quotContext_248_;
v_currMacroScope_275_ = v_currMacroScope_249_;
v_cancelTk_x3f_276_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_277_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_278_ = v_inheritedTraceOptions_252_;
v___y_279_ = v_a_231_;
goto v___jp_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_339_, lean_object* v_preDefs_340_, lean_object* v_preDefsNonrec_341_, lean_object* v_unaryPreDefNonRec_342_, lean_object* v_cacheProofs_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
uint8_t v_cacheProofs_boxed_351_; lean_object* v_res_352_; 
v_cacheProofs_boxed_351_ = lean_unbox(v_cacheProofs_343_);
v_res_352_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_339_, v_preDefs_340_, v_preDefsNonrec_341_, v_unaryPreDefNonRec_342_, v_cacheProofs_boxed_351_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_preDefsNonrec_341_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(uint8_t v_flag_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___redArg(v_flag_353_, v___y_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_flag_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_flag_boxed_370_; lean_object* v_res_371_; 
v_flag_boxed_370_ = lean_unbox(v_flag_362_);
v_res_371_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_flag_boxed_370_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_00_u03b1_372_, uint8_t v_flag_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___redArg(v_flag_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_00_u03b1_383_, lean_object* v_flag_384_, lean_object* v_x_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
uint8_t v_flag_boxed_393_; lean_object* v_res_394_; 
v_flag_boxed_393_ = lean_unbox(v_flag_384_);
v_res_394_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_00_u03b1_383_, v_flag_boxed_393_, v_x_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_395_, uint8_t v_cacheProofs_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_395_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
v___x_404_ = l_Lean_Elab_abstractNestedProofs(v_a_403_, v_cacheProofs_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
return v___x_404_;
}
else
{
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_405_, lean_object* v_cacheProofs_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
uint8_t v_cacheProofs_boxed_412_; lean_object* v_res_413_; 
v_cacheProofs_boxed_412_ = lean_unbox(v_cacheProofs_406_);
v_res_413_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_405_, v_cacheProofs_boxed_412_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_414_, size_t v_sz_415_, size_t v_i_416_, lean_object* v_b_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_416_, v_sz_415_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_b_417_);
return v___x_422_;
}
else
{
lean_object* v_a_423_; lean_object* v_declName_424_; lean_object* v___x_425_; 
v_a_423_ = lean_array_uget_borrowed(v_as_414_, v_i_416_);
v_declName_424_ = lean_ctor_get(v_a_423_, 3);
lean_inc(v_declName_424_);
v___x_425_ = l_Lean_enableRealizationsForConst(v_declName_424_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
lean_dec_ref(v___x_425_);
v___x_426_ = lean_box(0);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_416_, v___x_427_);
v_i_416_ = v___x_428_;
v_b_417_ = v___x_426_;
goto _start;
}
else
{
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_430_, lean_object* v_sz_431_, lean_object* v_i_432_, lean_object* v_b_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
size_t v_sz_boxed_437_; size_t v_i_boxed_438_; lean_object* v_res_439_; 
v_sz_boxed_437_ = lean_unbox_usize(v_sz_431_);
lean_dec(v_sz_431_);
v_i_boxed_438_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_430_, v_sz_boxed_437_, v_i_boxed_438_, v_b_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v_as_430_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_440_, size_t v_sz_441_, size_t v_i_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_lt(v_i_442_, v_sz_441_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_b_443_);
return v___x_450_;
}
else
{
lean_object* v_a_451_; lean_object* v_declName_452_; lean_object* v___x_453_; 
v_a_451_ = lean_array_uget_borrowed(v_as_440_, v_i_442_);
v_declName_452_ = lean_ctor_get(v_a_451_, 3);
lean_inc(v_declName_452_);
v___x_453_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_452_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v___x_454_; size_t v___x_455_; size_t v___x_456_; 
lean_dec_ref(v___x_453_);
v___x_454_ = lean_box(0);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_442_, v___x_455_);
v_i_442_ = v___x_456_;
v_b_443_ = v___x_454_;
goto _start;
}
else
{
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_458_, lean_object* v_sz_459_, lean_object* v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
size_t v_sz_boxed_467_; size_t v_i_boxed_468_; lean_object* v_res_469_; 
v_sz_boxed_467_ = lean_unbox_usize(v_sz_459_);
lean_dec(v_sz_459_);
v_i_boxed_468_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_458_, v_sz_boxed_467_, v_i_boxed_468_, v_b_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec_ref(v_as_458_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_470_, size_t v_sz_471_, size_t v_i_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_lt(v_i_472_, v_sz_471_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_b_473_);
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; 
v_a_483_ = lean_array_uget_borrowed(v_as_470_, v_i_472_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
lean_inc(v_a_483_);
v___x_486_ = lean_array_push(v___x_485_, v_a_483_);
v___x_487_ = 1;
v___x_488_ = l_Lean_Elab_applyAttributesOf(v___x_486_, v___x_487_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec_ref(v___x_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; 
lean_dec_ref(v___x_488_);
v___x_489_ = lean_box(0);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_472_, v___x_490_);
v_i_472_ = v___x_491_;
v_b_473_ = v___x_489_;
goto _start;
}
else
{
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_493_, lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_505_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_493_, v_sz_boxed_504_, v_i_boxed_505_, v_b_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec_ref(v_as_493_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_508_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
lean_ctor_set(v___x_508_, 3, v___x_507_);
lean_ctor_set(v___x_508_, 4, v___x_507_);
lean_ctor_set(v___x_508_, 5, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_509_, uint8_t v_s_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v_nextMacroScope_516_; lean_object* v_ngen_517_; lean_object* v_auxDeclNGen_518_; lean_object* v_traceState_519_; lean_object* v_messages_520_; lean_object* v_infoState_521_; lean_object* v_snapshotTasks_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_551_; 
v___x_514_ = lean_st_ref_take(v___y_512_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
v_nextMacroScope_516_ = lean_ctor_get(v___x_514_, 1);
v_ngen_517_ = lean_ctor_get(v___x_514_, 2);
v_auxDeclNGen_518_ = lean_ctor_get(v___x_514_, 3);
v_traceState_519_ = lean_ctor_get(v___x_514_, 4);
v_messages_520_ = lean_ctor_get(v___x_514_, 6);
v_infoState_521_ = lean_ctor_get(v___x_514_, 7);
v_snapshotTasks_522_ = lean_ctor_get(v___x_514_, 8);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_514_, 5);
lean_dec(v_unused_552_);
v___x_524_ = v___x_514_;
v_isShared_525_ = v_isSharedCheck_551_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_snapshotTasks_522_);
lean_inc(v_infoState_521_);
lean_inc(v_messages_520_);
lean_inc(v_traceState_519_);
lean_inc(v_auxDeclNGen_518_);
lean_inc(v_ngen_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_env_515_);
lean_dec(v___x_514_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_551_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_526_ = 0;
v___x_527_ = lean_box(0);
v___x_528_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_515_, v_declName_509_, v_s_510_, v___x_526_, v___x_527_);
v___x_529_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 5, v___x_529_);
lean_ctor_set(v___x_524_, 0, v___x_528_);
v___x_531_ = v___x_524_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_ngen_517_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_auxDeclNGen_518_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_traceState_519_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_messages_520_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_infoState_521_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_snapshotTasks_522_);
v___x_531_ = v_reuseFailAlloc_550_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_mctx_534_; lean_object* v_zetaDeltaFVarIds_535_; lean_object* v_postponed_536_; lean_object* v_diag_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v___x_532_ = lean_st_ref_set(v___y_512_, v___x_531_);
v___x_533_ = lean_st_ref_take(v___y_511_);
v_mctx_534_ = lean_ctor_get(v___x_533_, 0);
v_zetaDeltaFVarIds_535_ = lean_ctor_get(v___x_533_, 2);
v_postponed_536_ = lean_ctor_get(v___x_533_, 3);
v_diag_537_ = lean_ctor_get(v___x_533_, 4);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_533_, 1);
lean_dec(v_unused_549_);
v___x_539_ = v___x_533_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_diag_537_);
lean_inc(v_postponed_536_);
lean_inc(v_zetaDeltaFVarIds_535_);
lean_inc(v_mctx_534_);
lean_dec(v___x_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_mctx_534_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_zetaDeltaFVarIds_535_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_postponed_536_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_diag_537_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_st_ref_set(v___y_511_, v___x_543_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_553_, lean_object* v_s_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v_s_boxed_558_; lean_object* v_res_559_; 
v_s_boxed_558_ = lean_unbox(v_s_554_);
v_res_559_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_553_, v_s_boxed_558_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
uint8_t v___x_568_; lean_object* v___x_569_; 
v___x_568_ = 2;
v___x_569_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_560_, v___x_568_, v___y_564_, v___y_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_578_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v_as_591_, size_t v_i_592_, size_t v_stop_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_usize_dec_eq(v_i_592_, v_stop_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v_name_596_; uint8_t v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_595_ = lean_array_uget_borrowed(v_as_591_, v_i_592_);
v_name_596_ = lean_ctor_get(v___x_595_, 0);
v___x_597_ = 1;
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_599_ = lean_name_eq(v_name_596_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_601_ = lean_name_eq(v_name_596_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_603_ = lean_name_eq(v_name_596_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_605_ = lean_name_eq(v_name_596_, v___x_604_);
if (v___x_605_ == 0)
{
size_t v___x_606_; size_t v___x_607_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_592_, v___x_606_);
v_i_592_ = v___x_607_;
goto _start;
}
else
{
return v___x_597_;
}
}
else
{
return v___x_597_;
}
}
else
{
return v___x_597_;
}
}
else
{
return v___x_597_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_stop_612_){
_start:
{
size_t v_i_boxed_613_; size_t v_stop_boxed_614_; uint8_t v_res_615_; lean_object* v_r_616_; 
v_i_boxed_613_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_stop_boxed_614_ = lean_unbox_usize(v_stop_612_);
lean_dec(v_stop_612_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_as_610_, v_i_boxed_613_, v_stop_boxed_614_);
lean_dec_ref(v_as_610_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_a_629_; uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_b_620_);
return v___x_634_;
}
else
{
lean_object* v_a_635_; uint8_t v_kind_636_; lean_object* v_modifiers_637_; lean_object* v___x_638_; uint8_t v___y_640_; uint8_t v___x_643_; 
v_a_635_ = lean_array_uget_borrowed(v_as_617_, v_i_619_);
v_kind_636_ = lean_ctor_get_uint8(v_a_635_, sizeof(void*)*9);
v_modifiers_637_ = lean_ctor_get(v_a_635_, 2);
v___x_638_ = lean_box(0);
v___x_643_ = l_Lean_Elab_DefKind_isTheorem(v_kind_636_);
if (v___x_643_ == 0)
{
lean_object* v_attrs_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_attrs_644_ = lean_ctor_get(v_modifiers_637_, 2);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_array_get_size(v_attrs_644_);
v___x_647_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
v___y_640_ = v___x_643_;
goto v___jp_639_;
}
else
{
if (v___x_647_ == 0)
{
v___y_640_ = v___x_643_;
goto v___jp_639_;
}
else
{
size_t v___x_648_; size_t v___x_649_; uint8_t v___x_650_; 
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_646_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v_attrs_644_, v___x_648_, v___x_649_);
v___y_640_ = v___x_650_;
goto v___jp_639_;
}
}
}
else
{
v_a_629_ = v___x_638_;
goto v___jp_628_;
}
v___jp_639_:
{
if (v___y_640_ == 0)
{
lean_object* v_declName_641_; lean_object* v___x_642_; 
v_declName_641_ = lean_ctor_get(v_a_635_, 3);
lean_inc(v_declName_641_);
v___x_642_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_641_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_dec_ref(v___x_642_);
v_a_629_ = v___x_638_;
goto v___jp_628_;
}
else
{
return v___x_642_;
}
}
else
{
v_a_629_ = v___x_638_;
goto v___jp_628_;
}
}
}
v___jp_628_:
{
size_t v___x_630_; size_t v___x_631_; 
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_619_, v___x_630_);
v_i_619_ = v___x_631_;
v_b_620_ = v_a_629_;
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
lean_dec_ref(v___x_676_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_665_, v_sz_674_, v___x_675_, v___x_673_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; size_t v_sz_679_; lean_object* v___x_680_; 
lean_dec_ref(v___x_677_);
lean_inc_ref(v_preDefs_665_);
v___x_678_ = l_Array_reverse___redArg(v_preDefs_665_);
v_sz_679_ = lean_array_size(v___x_678_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_678_, v_sz_679_, v___x_675_, v___x_673_, v_a_670_, v_a_671_);
lean_dec_ref(v___x_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; 
lean_dec_ref(v___x_680_);
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
