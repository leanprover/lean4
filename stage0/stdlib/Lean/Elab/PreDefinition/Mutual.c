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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_filterAttrs(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_allowUnsafeReducibility;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
else
{
lean_object* v_val_7_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_7_) == 3)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_v_8_);
lean_dec_ref_known(v_val_7_, 1);
return v_v_8_;
}
else
{
lean_dec(v_val_7_);
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(lean_object* v_attr_15_){
_start:
{
lean_object* v_name_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v_name_16_ = lean_ctor_get(v_attr_15_, 0);
v___x_17_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1));
v___x_18_ = lean_name_eq(v_name_16_, v___x_17_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 1;
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(lean_object* v_attr_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(v_attr_21_);
lean_dec_ref(v_attr_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object* v_docCtx_24_, uint8_t v___x_25_, lean_object* v_declNames_26_, uint8_t v_cacheProofs_27_, lean_object* v_as_28_, size_t v_i_29_, size_t v_stop_30_, lean_object* v_b_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = lean_usize_dec_eq(v_i_29_, v_stop_30_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = 1;
v___x_41_ = lean_array_uget_borrowed(v_as_28_, v_i_29_);
lean_inc(v_declNames_26_);
lean_inc(v___x_41_);
lean_inc_ref(v_docCtx_24_);
v___x_42_ = l_Lean_Elab_addNonRec(v_docCtx_24_, v___x_41_, v___x_25_, v_declNames_26_, v_cacheProofs_27_, v___x_25_, v___x_40_, v___x_40_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; size_t v___x_44_; size_t v___x_45_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_add(v_i_29_, v___x_44_);
v_i_29_ = v___x_45_;
v_b_31_ = v_a_43_;
goto _start;
}
else
{
lean_dec(v_declNames_26_);
lean_dec_ref(v_docCtx_24_);
return v___x_42_;
}
}
else
{
lean_object* v___x_47_; 
lean_dec(v_declNames_26_);
lean_dec_ref(v_docCtx_24_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v_b_31_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object* v_docCtx_48_, lean_object* v___x_49_, lean_object* v_declNames_50_, lean_object* v_cacheProofs_51_, lean_object* v_as_52_, lean_object* v_i_53_, lean_object* v_stop_54_, lean_object* v_b_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
uint8_t v___x_4652__boxed_63_; uint8_t v_cacheProofs_boxed_64_; size_t v_i_boxed_65_; size_t v_stop_boxed_66_; lean_object* v_res_67_; 
v___x_4652__boxed_63_ = lean_unbox(v___x_49_);
v_cacheProofs_boxed_64_ = lean_unbox(v_cacheProofs_51_);
v_i_boxed_65_ = lean_unbox_usize(v_i_53_);
lean_dec(v_i_53_);
v_stop_boxed_66_ = lean_unbox_usize(v_stop_54_);
lean_dec(v_stop_54_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_48_, v___x_4652__boxed_63_, v_declNames_50_, v_cacheProofs_boxed_64_, v_as_52_, v_i_boxed_65_, v_stop_boxed_66_, v_b_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec_ref(v_as_52_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(uint8_t v_flag_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_infoState_72_; lean_object* v_env_73_; lean_object* v_nextMacroScope_74_; lean_object* v_ngen_75_; lean_object* v_auxDeclNGen_76_; lean_object* v_traceState_77_; lean_object* v_cache_78_; lean_object* v_recordedDeps_79_; lean_object* v_messages_80_; lean_object* v_snapshotTasks_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_101_; 
v___x_71_ = lean_st_ref_take(v___y_69_);
v_infoState_72_ = lean_ctor_get(v___x_71_, 8);
v_env_73_ = lean_ctor_get(v___x_71_, 0);
v_nextMacroScope_74_ = lean_ctor_get(v___x_71_, 1);
v_ngen_75_ = lean_ctor_get(v___x_71_, 2);
v_auxDeclNGen_76_ = lean_ctor_get(v___x_71_, 3);
v_traceState_77_ = lean_ctor_get(v___x_71_, 4);
v_cache_78_ = lean_ctor_get(v___x_71_, 5);
v_recordedDeps_79_ = lean_ctor_get(v___x_71_, 6);
v_messages_80_ = lean_ctor_get(v___x_71_, 7);
v_snapshotTasks_81_ = lean_ctor_get(v___x_71_, 9);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_101_ == 0)
{
v___x_83_ = v___x_71_;
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_snapshotTasks_81_);
lean_inc(v_infoState_72_);
lean_inc(v_messages_80_);
lean_inc(v_recordedDeps_79_);
lean_inc(v_cache_78_);
lean_inc(v_traceState_77_);
lean_inc(v_auxDeclNGen_76_);
lean_inc(v_ngen_75_);
lean_inc(v_nextMacroScope_74_);
lean_inc(v_env_73_);
lean_dec(v___x_71_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_assignment_85_; lean_object* v_lazyAssignment_86_; lean_object* v_trees_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_100_; 
v_assignment_85_ = lean_ctor_get(v_infoState_72_, 0);
v_lazyAssignment_86_ = lean_ctor_get(v_infoState_72_, 1);
v_trees_87_ = lean_ctor_get(v_infoState_72_, 2);
v_isSharedCheck_100_ = !lean_is_exclusive(v_infoState_72_);
if (v_isSharedCheck_100_ == 0)
{
v___x_89_ = v_infoState_72_;
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_trees_87_);
lean_inc(v_lazyAssignment_86_);
lean_inc(v_assignment_85_);
lean_dec(v_infoState_72_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
if (v_isShared_90_ == 0)
{
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_assignment_85_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_lazyAssignment_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_trees_87_);
v___x_93_ = v_reuseFailAlloc_99_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*3, v_flag_68_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 8, v___x_93_);
v___x_95_ = v___x_83_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_env_73_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_nextMacroScope_74_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_ngen_75_);
lean_ctor_set(v_reuseFailAlloc_98_, 3, v_auxDeclNGen_76_);
lean_ctor_set(v_reuseFailAlloc_98_, 4, v_traceState_77_);
lean_ctor_set(v_reuseFailAlloc_98_, 5, v_cache_78_);
lean_ctor_set(v_reuseFailAlloc_98_, 6, v_recordedDeps_79_);
lean_ctor_set(v_reuseFailAlloc_98_, 7, v_messages_80_);
lean_ctor_set(v_reuseFailAlloc_98_, 8, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_98_, 9, v_snapshotTasks_81_);
v___x_95_ = v_reuseFailAlloc_98_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_st_ref_put(v___y_69_, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_91_);
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg___boxed(lean_object* v_flag_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
uint8_t v_flag_boxed_105_; lean_object* v_res_106_; 
v_flag_boxed_105_ = lean_unbox(v_flag_102_);
v_res_106_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_boxed_105_, v___y_103_);
lean_dec(v___y_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(uint8_t v_flag_107_, lean_object* v_x_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; lean_object* v_infoState_117_; uint8_t v_enabled_118_; lean_object* v_a_120_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_116_ = lean_st_ref_get(v___y_114_);
v_infoState_117_ = lean_ctor_get(v___x_116_, 8);
lean_inc_ref(v_infoState_117_);
lean_dec(v___x_116_);
v_enabled_118_ = lean_ctor_get_uint8(v_infoState_117_, sizeof(void*)*3);
lean_dec_ref(v_infoState_117_);
v___x_130_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_107_, v___y_114_);
lean_dec_ref(v___x_130_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
v___x_131_ = lean_apply_7(v_x_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v___x_133_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_enabled_118_, v___y_114_);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_133_, 0);
lean_dec(v_unused_141_);
v___x_135_ = v___x_133_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_dec(v___x_133_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v_a_132_);
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_132_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_object* v_a_142_; 
v_a_142_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_131_, 1);
v_a_120_ = v_a_142_;
goto v___jp_119_;
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v___x_121_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_enabled_118_, v___y_114_);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_121_, 0);
lean_dec(v_unused_129_);
v___x_123_ = v___x_121_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_dec(v___x_121_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v_a_120_);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_120_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg___boxed(lean_object* v_flag_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v_flag_boxed_152_; lean_object* v_res_153_; 
v_flag_boxed_152_ = lean_unbox(v_flag_143_);
v_res_153_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_boxed_152_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
if (lean_obj_tag(v_a_154_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = l_List_reverse___redArg(v_a_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_167_; 
v_head_157_ = lean_ctor_get(v_a_154_, 0);
v_tail_158_ = lean_ctor_get(v_a_154_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_a_154_);
if (v_isSharedCheck_167_ == 0)
{
v___x_160_ = v_a_154_;
v_isShared_161_ = v_isSharedCheck_167_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_tail_158_);
lean_inc(v_head_157_);
lean_dec(v_a_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_167_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_declName_162_; lean_object* v___x_164_; 
v_declName_162_ = lean_ctor_get(v_head_157_, 3);
lean_inc(v_declName_162_);
lean_dec(v_head_157_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_a_155_);
lean_ctor_set(v___x_160_, 0, v_declName_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_declName_162_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_a_155_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
v_a_154_ = v_tail_158_;
v_a_155_ = v___x_164_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(lean_object* v_o_171_, lean_object* v_k_172_, uint8_t v_v_173_){
_start:
{
lean_object* v_map_174_; uint8_t v_hasTrace_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_189_; 
v_map_174_ = lean_ctor_get(v_o_171_, 0);
v_hasTrace_175_ = lean_ctor_get_uint8(v_o_171_, sizeof(void*)*1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_o_171_);
if (v_isSharedCheck_189_ == 0)
{
v___x_177_ = v_o_171_;
v_isShared_178_ = v_isSharedCheck_189_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_map_174_);
lean_dec(v_o_171_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_189_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_179_, 0, v_v_173_);
lean_inc(v_k_172_);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_172_, v___x_179_, v_map_174_);
if (v_hasTrace_175_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_184_; 
v___x_181_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__1));
v___x_182_ = l_Lean_Name_isPrefixOf(v___x_181_, v_k_172_);
lean_dec(v_k_172_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_180_);
v___x_184_ = v___x_177_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_180_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_182_);
return v___x_184_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v_k_172_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_180_);
v___x_187_ = v___x_177_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_188_, sizeof(void*)*1, v_hasTrace_175_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_o_190_, lean_object* v_k_191_, lean_object* v_v_192_){
_start:
{
uint8_t v_v_boxed_193_; lean_object* v_res_194_; 
v_v_boxed_193_ = lean_unbox(v_v_192_);
v_res_194_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_o_190_, v_k_191_, v_v_boxed_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_opts_195_, lean_object* v_opt_196_, uint8_t v_val_197_){
_start:
{
lean_object* v_name_198_; lean_object* v___x_199_; 
v_name_198_ = lean_ctor_get(v_opt_196_, 0);
lean_inc(v_name_198_);
lean_dec_ref(v_opt_196_);
v___x_199_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_opts_195_, v_name_198_, v_val_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_opts_200_, lean_object* v_opt_201_, lean_object* v_val_202_){
_start:
{
uint8_t v_val_boxed_203_; lean_object* v_res_204_; 
v_val_boxed_203_ = lean_unbox(v_val_202_);
v_res_204_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_opts_200_, v_opt_201_, v_val_boxed_203_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object* v_docCtx_211_, lean_object* v_preDefs_212_, lean_object* v_preDefsNonrec_213_, lean_object* v_unaryPreDefNonRec_214_, uint8_t v_cacheProofs_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_declName_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_toCold_227_; lean_object* v_declName_228_; lean_object* v_currRecDepth_229_; lean_object* v_ref_230_; uint8_t v_suppressElabErrors_231_; uint8_t v_checkDeprecated_232_; uint8_t v_isRecordingDeps_233_; lean_object* v_fileName_234_; lean_object* v_fileMap_235_; lean_object* v_options_236_; lean_object* v_currNamespace_237_; lean_object* v_openDecls_238_; lean_object* v_initHeartbeats_239_; lean_object* v_maxHeartbeats_240_; lean_object* v_quotContext_241_; lean_object* v_currMacroScope_242_; lean_object* v_cancelTk_x3f_243_; lean_object* v_inheritedTraceOptions_244_; lean_object* v___f_245_; lean_object* v_preDefNonRec_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_declNames_249_; uint8_t v___x_250_; lean_object* v___y_252_; uint16_t v___y_253_; lean_object* v_fileName_254_; lean_object* v_fileMap_255_; lean_object* v_currNamespace_256_; lean_object* v_openDecls_257_; lean_object* v_initHeartbeats_258_; lean_object* v_maxHeartbeats_259_; lean_object* v_quotContext_260_; lean_object* v_currMacroScope_261_; lean_object* v_cancelTk_x3f_262_; lean_object* v_inheritedTraceOptions_263_; lean_object* v_currRecDepth_264_; lean_object* v_ref_265_; uint8_t v_suppressElabErrors_266_; uint8_t v_checkDeprecated_267_; uint8_t v_isRecordingDeps_268_; lean_object* v___y_269_; lean_object* v___y_335_; uint16_t v___y_336_; uint8_t v___y_337_; lean_object* v___y_360_; 
v_declName_223_ = lean_ctor_get(v_unaryPreDefNonRec_214_, 3);
lean_inc(v_declName_223_);
v___x_224_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_array_get_borrowed(v___x_224_, v_preDefs_212_, v___x_225_);
v_toCold_227_ = lean_ctor_get(v_a_220_, 0);
v_declName_228_ = lean_ctor_get(v___x_226_, 3);
lean_inc(v_declName_228_);
v_currRecDepth_229_ = lean_ctor_get(v_a_220_, 1);
v_ref_230_ = lean_ctor_get(v_a_220_, 2);
v_suppressElabErrors_231_ = lean_ctor_get_uint8(v_a_220_, sizeof(void*)*3 + 2);
v_checkDeprecated_232_ = lean_ctor_get_uint8(v_a_220_, sizeof(void*)*3 + 3);
v_isRecordingDeps_233_ = lean_ctor_get_uint8(v_a_220_, sizeof(void*)*3 + 4);
v_fileName_234_ = lean_ctor_get(v_toCold_227_, 0);
v_fileMap_235_ = lean_ctor_get(v_toCold_227_, 1);
v_options_236_ = lean_ctor_get(v_toCold_227_, 2);
v_currNamespace_237_ = lean_ctor_get(v_toCold_227_, 4);
v_openDecls_238_ = lean_ctor_get(v_toCold_227_, 5);
v_initHeartbeats_239_ = lean_ctor_get(v_toCold_227_, 6);
v_maxHeartbeats_240_ = lean_ctor_get(v_toCold_227_, 7);
v_quotContext_241_ = lean_ctor_get(v_toCold_227_, 8);
v_currMacroScope_242_ = lean_ctor_get(v_toCold_227_, 9);
v_cancelTk_x3f_243_ = lean_ctor_get(v_toCold_227_, 10);
v_inheritedTraceOptions_244_ = lean_ctor_get(v_toCold_227_, 11);
v___f_245_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v_preDefNonRec_246_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_214_, v___f_245_);
v___x_247_ = lean_array_to_list(v_preDefs_212_);
v___x_248_ = lean_box(0);
v_declNames_249_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_247_, v___x_248_);
v___x_250_ = lean_name_eq(v_declName_223_, v_declName_228_);
lean_dec(v_declName_228_);
lean_dec(v_declName_223_);
if (v_isRecordingDeps_233_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = l_Lean_allowUnsafeReducibility;
v___x_372_ = 1;
lean_inc_ref(v_options_236_);
v___x_373_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_options_236_, v___x_371_, v___x_372_);
v___y_360_ = v___x_373_;
goto v___jp_359_;
}
else
{
lean_object* v___x_374_; 
lean_inc_ref(v_options_236_);
v___x_374_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_236_);
v___y_360_ = v___x_374_;
goto v___jp_359_;
}
v___jp_251_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = l_Lean_maxRecDepth;
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v___y_252_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_272_, 0, v_fileName_254_);
lean_ctor_set(v___x_272_, 1, v_fileMap_255_);
lean_ctor_set(v___x_272_, 2, v___y_252_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
lean_ctor_set(v___x_272_, 4, v_currNamespace_256_);
lean_ctor_set(v___x_272_, 5, v_openDecls_257_);
lean_ctor_set(v___x_272_, 6, v_initHeartbeats_258_);
lean_ctor_set(v___x_272_, 7, v_maxHeartbeats_259_);
lean_ctor_set(v___x_272_, 8, v_quotContext_260_);
lean_ctor_set(v___x_272_, 9, v_currMacroScope_261_);
lean_ctor_set(v___x_272_, 10, v_cancelTk_x3f_262_);
lean_ctor_set(v___x_272_, 11, v_inheritedTraceOptions_263_);
lean_inc(v_ref_265_);
lean_inc(v_currRecDepth_264_);
v___x_273_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_currRecDepth_264_);
lean_ctor_set(v___x_273_, 2, v_ref_265_);
lean_ctor_set_uint16(v___x_273_, sizeof(void*)*3, v___y_253_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 2, v_suppressElabErrors_266_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 3, v_checkDeprecated_267_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 4, v_isRecordingDeps_268_);
if (v___x_250_ == 0)
{
lean_object* v_modifiers_274_; lean_object* v_ref_275_; uint8_t v_kind_276_; lean_object* v_levelParams_277_; lean_object* v_declName_278_; lean_object* v_binders_279_; lean_object* v_numSectionVars_280_; lean_object* v_type_281_; lean_object* v_value_282_; lean_object* v_termination_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_329_; 
v_modifiers_274_ = lean_ctor_get(v_preDefNonRec_246_, 2);
v_ref_275_ = lean_ctor_get(v_preDefNonRec_246_, 0);
v_kind_276_ = lean_ctor_get_uint8(v_preDefNonRec_246_, sizeof(void*)*9);
v_levelParams_277_ = lean_ctor_get(v_preDefNonRec_246_, 1);
v_declName_278_ = lean_ctor_get(v_preDefNonRec_246_, 3);
v_binders_279_ = lean_ctor_get(v_preDefNonRec_246_, 4);
v_numSectionVars_280_ = lean_ctor_get(v_preDefNonRec_246_, 5);
v_type_281_ = lean_ctor_get(v_preDefNonRec_246_, 6);
v_value_282_ = lean_ctor_get(v_preDefNonRec_246_, 7);
v_termination_283_ = lean_ctor_get(v_preDefNonRec_246_, 8);
v_isSharedCheck_329_ = !lean_is_exclusive(v_preDefNonRec_246_);
if (v_isSharedCheck_329_ == 0)
{
v___x_285_ = v_preDefNonRec_246_;
v_isShared_286_ = v_isSharedCheck_329_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_termination_283_);
lean_inc(v_value_282_);
lean_inc(v_type_281_);
lean_inc(v_numSectionVars_280_);
lean_inc(v_binders_279_);
lean_inc(v_declName_278_);
lean_inc(v_modifiers_274_);
lean_inc(v_levelParams_277_);
lean_inc(v_ref_275_);
lean_dec(v_preDefNonRec_246_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_329_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_stx_287_; uint8_t v_visibility_288_; uint8_t v_isProtected_289_; uint8_t v_computeKind_290_; uint8_t v_recKind_291_; uint8_t v_isUnsafe_292_; lean_object* v_attrs_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_327_; 
v_stx_287_ = lean_ctor_get(v_modifiers_274_, 0);
v_visibility_288_ = lean_ctor_get_uint8(v_modifiers_274_, sizeof(void*)*3);
v_isProtected_289_ = lean_ctor_get_uint8(v_modifiers_274_, sizeof(void*)*3 + 1);
v_computeKind_290_ = lean_ctor_get_uint8(v_modifiers_274_, sizeof(void*)*3 + 2);
v_recKind_291_ = lean_ctor_get_uint8(v_modifiers_274_, sizeof(void*)*3 + 3);
v_isUnsafe_292_ = lean_ctor_get_uint8(v_modifiers_274_, sizeof(void*)*3 + 4);
v_attrs_293_ = lean_ctor_get(v_modifiers_274_, 2);
v_isSharedCheck_327_ = !lean_is_exclusive(v_modifiers_274_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_modifiers_274_, 1);
lean_dec(v_unused_328_);
v___x_295_ = v_modifiers_274_;
v_isShared_296_ = v_isSharedCheck_327_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_attrs_293_);
lean_inc(v_stx_287_);
lean_dec(v_modifiers_274_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_327_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_stx_287_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_attrs_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3, v_visibility_288_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 1, v_isProtected_289_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 2, v_computeKind_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 3, v_recKind_291_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 4, v_isUnsafe_292_);
v___x_299_ = v_reuseFailAlloc_326_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
lean_inc(v_declName_278_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 2, v___x_299_);
v___x_301_ = v___x_285_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_ref_275_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_levelParams_277_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_declName_278_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_binders_279_);
lean_ctor_set(v_reuseFailAlloc_325_, 5, v_numSectionVars_280_);
lean_ctor_set(v_reuseFailAlloc_325_, 6, v_type_281_);
lean_ctor_set(v_reuseFailAlloc_325_, 7, v_value_282_);
lean_ctor_set(v_reuseFailAlloc_325_, 8, v_termination_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_325_, sizeof(void*)*9, v_kind_276_);
v___x_301_ = v_reuseFailAlloc_325_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v_declName_278_);
lean_ctor_set(v___x_302_, 1, v___x_248_);
v___x_303_ = 1;
v___x_304_ = lean_box(v___x_250_);
v___x_305_ = lean_box(v_cacheProofs_215_);
v___x_306_ = lean_box(v___x_250_);
v___x_307_ = lean_box(v___x_303_);
v___x_308_ = lean_box(v___x_303_);
lean_inc_ref(v_docCtx_211_);
v___x_309_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 15, 8);
lean_closure_set(v___x_309_, 0, v_docCtx_211_);
lean_closure_set(v___x_309_, 1, v___x_301_);
lean_closure_set(v___x_309_, 2, v___x_304_);
lean_closure_set(v___x_309_, 3, v___x_302_);
lean_closure_set(v___x_309_, 4, v___x_305_);
lean_closure_set(v___x_309_, 5, v___x_306_);
lean_closure_set(v___x_309_, 6, v___x_307_);
lean_closure_set(v___x_309_, 7, v___x_308_);
v___x_310_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v___x_250_, v___x_309_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_323_; 
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v___x_310_, 0);
lean_dec(v_unused_324_);
v___x_312_ = v___x_310_;
v_isShared_313_ = v_isSharedCheck_323_;
goto v_resetjp_311_;
}
else
{
lean_dec(v___x_310_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_323_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_array_get_size(v_preDefsNonrec_213_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_nat_dec_lt(v___x_225_, v___x_314_);
if (v___x_316_ == 0)
{
lean_object* v___x_318_; 
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_249_);
lean_dec_ref(v_docCtx_211_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_315_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_315_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_312_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_314_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_211_, v___x_250_, v_declNames_249_, v_cacheProofs_215_, v_preDefsNonrec_213_, v___x_320_, v___x_321_, v___x_315_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_322_;
}
}
}
else
{
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_249_);
lean_dec_ref(v_docCtx_211_);
return v___x_310_;
}
}
}
}
}
}
else
{
lean_object* v_declName_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_declNames_249_);
v_declName_330_ = lean_ctor_get(v_preDefNonRec_246_, 3);
v___x_331_ = 0;
lean_inc(v_declName_330_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v_declName_330_);
lean_ctor_set(v___x_332_, 1, v___x_248_);
v___x_333_ = l_Lean_Elab_addNonRec(v_docCtx_211_, v_preDefNonRec_246_, v___x_331_, v___x_332_, v_cacheProofs_215_, v___x_331_, v___x_250_, v___x_250_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_333_;
}
}
v___jp_334_:
{
lean_object* v___x_338_; lean_object* v_env_339_; lean_object* v_nextMacroScope_340_; lean_object* v_ngen_341_; lean_object* v_auxDeclNGen_342_; lean_object* v_traceState_343_; lean_object* v_recordedDeps_344_; lean_object* v_messages_345_; lean_object* v_infoState_346_; lean_object* v_snapshotTasks_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_357_; 
v___x_338_ = lean_st_ref_take(v_a_221_);
v_env_339_ = lean_ctor_get(v___x_338_, 0);
v_nextMacroScope_340_ = lean_ctor_get(v___x_338_, 1);
v_ngen_341_ = lean_ctor_get(v___x_338_, 2);
v_auxDeclNGen_342_ = lean_ctor_get(v___x_338_, 3);
v_traceState_343_ = lean_ctor_get(v___x_338_, 4);
v_recordedDeps_344_ = lean_ctor_get(v___x_338_, 6);
v_messages_345_ = lean_ctor_get(v___x_338_, 7);
v_infoState_346_ = lean_ctor_get(v___x_338_, 8);
v_snapshotTasks_347_ = lean_ctor_get(v___x_338_, 9);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v___x_338_, 5);
lean_dec(v_unused_358_);
v___x_349_ = v___x_338_;
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snapshotTasks_347_);
lean_inc(v_infoState_346_);
lean_inc(v_messages_345_);
lean_inc(v_recordedDeps_344_);
lean_inc(v_traceState_343_);
lean_inc(v_auxDeclNGen_342_);
lean_inc(v_ngen_341_);
lean_inc(v_nextMacroScope_340_);
lean_inc(v_env_339_);
lean_dec(v___x_338_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = l_Lean_Kernel_enableDiag(v_env_339_, v___y_337_);
v___x_352_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 5, v___x_352_);
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_nextMacroScope_340_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_ngen_341_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_auxDeclNGen_342_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_traceState_343_);
lean_ctor_set(v_reuseFailAlloc_356_, 5, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_356_, 6, v_recordedDeps_344_);
lean_ctor_set(v_reuseFailAlloc_356_, 7, v_messages_345_);
lean_ctor_set(v_reuseFailAlloc_356_, 8, v_infoState_346_);
lean_ctor_set(v_reuseFailAlloc_356_, 9, v_snapshotTasks_347_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = lean_st_ref_put(v_a_221_, v___x_354_);
lean_inc_ref(v_inheritedTraceOptions_244_);
lean_inc(v_cancelTk_x3f_243_);
lean_inc(v_currMacroScope_242_);
lean_inc(v_quotContext_241_);
lean_inc(v_maxHeartbeats_240_);
lean_inc(v_initHeartbeats_239_);
lean_inc(v_openDecls_238_);
lean_inc(v_currNamespace_237_);
lean_inc_ref(v_fileMap_235_);
lean_inc_ref(v_fileName_234_);
v___y_252_ = v___y_335_;
v___y_253_ = v___y_336_;
v_fileName_254_ = v_fileName_234_;
v_fileMap_255_ = v_fileMap_235_;
v_currNamespace_256_ = v_currNamespace_237_;
v_openDecls_257_ = v_openDecls_238_;
v_initHeartbeats_258_ = v_initHeartbeats_239_;
v_maxHeartbeats_259_ = v_maxHeartbeats_240_;
v_quotContext_260_ = v_quotContext_241_;
v_currMacroScope_261_ = v_currMacroScope_242_;
v_cancelTk_x3f_262_ = v_cancelTk_x3f_243_;
v_inheritedTraceOptions_263_ = v_inheritedTraceOptions_244_;
v_currRecDepth_264_ = v_currRecDepth_229_;
v_ref_265_ = v_ref_230_;
v_suppressElabErrors_266_ = v_suppressElabErrors_231_;
v_checkDeprecated_267_ = v_checkDeprecated_232_;
v_isRecordingDeps_268_ = v_isRecordingDeps_233_;
v___y_269_ = v_a_221_;
goto v___jp_251_;
}
}
}
v___jp_359_:
{
uint16_t v___x_361_; lean_object* v___x_362_; lean_object* v_env_363_; uint8_t v___x_364_; uint16_t v___x_365_; uint16_t v___x_366_; uint16_t v___x_367_; uint8_t v___x_368_; 
v___x_361_ = l_Lean_OptionFlags_ofOptions(v___y_360_);
v___x_362_ = lean_st_ref_get(v_a_221_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_362_);
v___x_364_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_363_);
lean_dec_ref(v_env_363_);
v___x_365_ = 512;
v___x_366_ = lean_uint16_land(v___x_361_, v___x_365_);
v___x_367_ = 0;
v___x_368_ = lean_uint16_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
if (v___x_364_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = 1;
v___y_335_ = v___y_360_;
v___y_336_ = v___x_361_;
v___y_337_ = v___x_369_;
goto v___jp_334_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_244_);
lean_inc(v_cancelTk_x3f_243_);
lean_inc(v_currMacroScope_242_);
lean_inc(v_quotContext_241_);
lean_inc(v_maxHeartbeats_240_);
lean_inc(v_initHeartbeats_239_);
lean_inc(v_openDecls_238_);
lean_inc(v_currNamespace_237_);
lean_inc_ref(v_fileMap_235_);
lean_inc_ref(v_fileName_234_);
v___y_252_ = v___y_360_;
v___y_253_ = v___x_361_;
v_fileName_254_ = v_fileName_234_;
v_fileMap_255_ = v_fileMap_235_;
v_currNamespace_256_ = v_currNamespace_237_;
v_openDecls_257_ = v_openDecls_238_;
v_initHeartbeats_258_ = v_initHeartbeats_239_;
v_maxHeartbeats_259_ = v_maxHeartbeats_240_;
v_quotContext_260_ = v_quotContext_241_;
v_currMacroScope_261_ = v_currMacroScope_242_;
v_cancelTk_x3f_262_ = v_cancelTk_x3f_243_;
v_inheritedTraceOptions_263_ = v_inheritedTraceOptions_244_;
v_currRecDepth_264_ = v_currRecDepth_229_;
v_ref_265_ = v_ref_230_;
v_suppressElabErrors_266_ = v_suppressElabErrors_231_;
v_checkDeprecated_267_ = v_checkDeprecated_232_;
v_isRecordingDeps_268_ = v_isRecordingDeps_233_;
v___y_269_ = v_a_221_;
goto v___jp_251_;
}
}
else
{
if (v___x_364_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_244_);
lean_inc(v_cancelTk_x3f_243_);
lean_inc(v_currMacroScope_242_);
lean_inc(v_quotContext_241_);
lean_inc(v_maxHeartbeats_240_);
lean_inc(v_initHeartbeats_239_);
lean_inc(v_openDecls_238_);
lean_inc(v_currNamespace_237_);
lean_inc_ref(v_fileMap_235_);
lean_inc_ref(v_fileName_234_);
v___y_252_ = v___y_360_;
v___y_253_ = v___x_361_;
v_fileName_254_ = v_fileName_234_;
v_fileMap_255_ = v_fileMap_235_;
v_currNamespace_256_ = v_currNamespace_237_;
v_openDecls_257_ = v_openDecls_238_;
v_initHeartbeats_258_ = v_initHeartbeats_239_;
v_maxHeartbeats_259_ = v_maxHeartbeats_240_;
v_quotContext_260_ = v_quotContext_241_;
v_currMacroScope_261_ = v_currMacroScope_242_;
v_cancelTk_x3f_262_ = v_cancelTk_x3f_243_;
v_inheritedTraceOptions_263_ = v_inheritedTraceOptions_244_;
v_currRecDepth_264_ = v_currRecDepth_229_;
v_ref_265_ = v_ref_230_;
v_suppressElabErrors_266_ = v_suppressElabErrors_231_;
v_checkDeprecated_267_ = v_checkDeprecated_232_;
v_isRecordingDeps_268_ = v_isRecordingDeps_233_;
v___y_269_ = v_a_221_;
goto v___jp_251_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
v___y_335_ = v___y_360_;
v___y_336_ = v___x_361_;
v___y_337_ = v___x_370_;
goto v___jp_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_375_, lean_object* v_preDefs_376_, lean_object* v_preDefsNonrec_377_, lean_object* v_unaryPreDefNonRec_378_, lean_object* v_cacheProofs_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
uint8_t v_cacheProofs_boxed_387_; lean_object* v_res_388_; 
v_cacheProofs_boxed_387_ = lean_unbox(v_cacheProofs_379_);
v_res_388_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_375_, v_preDefs_376_, v_preDefsNonrec_377_, v_unaryPreDefNonRec_378_, v_cacheProofs_boxed_387_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec_ref(v_preDefsNonrec_377_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(uint8_t v_flag_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_389_, v___y_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___boxed(lean_object* v_flag_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v_flag_boxed_406_; lean_object* v_res_407_; 
v_flag_boxed_406_ = lean_unbox(v_flag_398_);
v_res_407_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(v_flag_boxed_406_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object* v_00_u03b1_408_, uint8_t v_flag_409_, lean_object* v_x_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_409_, v_x_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object* v_00_u03b1_419_, lean_object* v_flag_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v_flag_boxed_429_; lean_object* v_res_430_; 
v_flag_boxed_429_ = lean_unbox(v_flag_420_);
v_res_430_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v_00_u03b1_419_, v_flag_boxed_429_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_431_, uint8_t v_cacheProofs_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_431_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = l_Lean_Elab_abstractNestedProofs(v_a_439_, v_cacheProofs_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
return v___x_440_;
}
else
{
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_441_, lean_object* v_cacheProofs_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
uint8_t v_cacheProofs_boxed_448_; lean_object* v_res_449_; 
v_cacheProofs_boxed_448_ = lean_unbox(v_cacheProofs_442_);
v_res_449_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_441_, v_cacheProofs_boxed_448_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_450_, size_t v_sz_451_, size_t v_i_452_, lean_object* v_b_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_lt(v_i_452_, v_sz_451_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_b_453_);
return v___x_458_;
}
else
{
lean_object* v_a_459_; lean_object* v_declName_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_459_ = lean_array_uget_borrowed(v_as_450_, v_i_452_);
v_declName_460_ = lean_ctor_get(v_a_459_, 3);
v___x_461_ = lean_box(0);
lean_inc(v_declName_460_);
v___x_462_ = l_Lean_enableRealizationsForConst(v_declName_460_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_462_) == 0)
{
size_t v___x_463_; size_t v___x_464_; 
lean_dec_ref_known(v___x_462_, 1);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_452_, v___x_463_);
v_i_452_ = v___x_464_;
v_b_453_ = v___x_461_;
goto _start;
}
else
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_466_, lean_object* v_sz_467_, lean_object* v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
size_t v_sz_boxed_473_; size_t v_i_boxed_474_; lean_object* v_res_475_; 
v_sz_boxed_473_ = lean_unbox_usize(v_sz_467_);
lean_dec(v_sz_467_);
v_i_boxed_474_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_466_, v_sz_boxed_473_, v_i_boxed_474_, v_b_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec_ref(v_as_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_476_, size_t v_sz_477_, size_t v_i_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_lt(v_i_478_, v_sz_477_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_479_);
return v___x_486_;
}
else
{
lean_object* v_a_487_; lean_object* v_declName_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_487_ = lean_array_uget_borrowed(v_as_476_, v_i_478_);
v_declName_488_ = lean_ctor_get(v_a_487_, 3);
v___x_489_ = lean_box(0);
lean_inc(v_declName_488_);
v___x_490_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_488_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_490_) == 0)
{
size_t v___x_491_; size_t v___x_492_; 
lean_dec_ref_known(v___x_490_, 1);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_478_, v___x_491_);
v_i_478_ = v___x_492_;
v_b_479_ = v___x_489_;
goto _start;
}
else
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_494_, lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_504_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_494_, v_sz_boxed_503_, v_i_boxed_504_, v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v_as_494_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_506_, size_t v_sz_507_, size_t v_i_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_lt(v_i_508_, v_sz_507_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_b_509_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; 
v___x_519_ = lean_box(0);
v_a_520_ = lean_array_uget_borrowed(v_as_506_, v_i_508_);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_mk_empty_array_with_capacity(v___x_521_);
lean_inc(v_a_520_);
v___x_523_ = lean_array_push(v___x_522_, v_a_520_);
v___x_524_ = 1;
v___x_525_ = l_Lean_Elab_applyAttributesOf(v___x_523_, v___x_524_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec_ref(v___x_523_);
if (lean_obj_tag(v___x_525_) == 0)
{
size_t v___x_526_; size_t v___x_527_; 
lean_dec_ref_known(v___x_525_, 1);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_508_, v___x_526_);
v_i_508_ = v___x_527_;
v_b_509_ = v___x_519_;
goto _start;
}
else
{
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_529_, lean_object* v_sz_530_, lean_object* v_i_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_530_);
lean_dec(v_sz_530_);
v_i_boxed_541_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_529_, v_sz_boxed_540_, v_i_boxed_541_, v_b_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v_as_529_);
return v_res_542_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg(){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___closed__0);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v___dummy_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg();
return v_res_548_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7___redArg();
return v___x_549_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_551_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
v___x_552_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_550_);
lean_ctor_set(v___x_552_, 3, v___x_550_);
lean_ctor_set(v___x_552_, 4, v___x_550_);
lean_ctor_set(v___x_552_, 5, v___x_550_);
lean_ctor_set(v___x_552_, 6, v___x_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_553_, uint8_t v_s_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; lean_object* v_env_559_; lean_object* v_nextMacroScope_560_; lean_object* v_ngen_561_; lean_object* v_auxDeclNGen_562_; lean_object* v_traceState_563_; lean_object* v_recordedDeps_564_; lean_object* v_messages_565_; lean_object* v_infoState_566_; lean_object* v_snapshotTasks_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_596_; 
v___x_558_ = lean_st_ref_take(v___y_556_);
v_env_559_ = lean_ctor_get(v___x_558_, 0);
v_nextMacroScope_560_ = lean_ctor_get(v___x_558_, 1);
v_ngen_561_ = lean_ctor_get(v___x_558_, 2);
v_auxDeclNGen_562_ = lean_ctor_get(v___x_558_, 3);
v_traceState_563_ = lean_ctor_get(v___x_558_, 4);
v_recordedDeps_564_ = lean_ctor_get(v___x_558_, 6);
v_messages_565_ = lean_ctor_get(v___x_558_, 7);
v_infoState_566_ = lean_ctor_get(v___x_558_, 8);
v_snapshotTasks_567_ = lean_ctor_get(v___x_558_, 9);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_558_, 5);
lean_dec(v_unused_597_);
v___x_569_ = v___x_558_;
v_isShared_570_ = v_isSharedCheck_596_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snapshotTasks_567_);
lean_inc(v_infoState_566_);
lean_inc(v_messages_565_);
lean_inc(v_recordedDeps_564_);
lean_inc(v_traceState_563_);
lean_inc(v_auxDeclNGen_562_);
lean_inc(v_ngen_561_);
lean_inc(v_nextMacroScope_560_);
lean_inc(v_env_559_);
lean_dec(v___x_558_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_596_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_571_ = 0;
v___x_572_ = lean_box(0);
v___x_573_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_559_, v_declName_553_, v_s_554_, v___x_571_, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 5, v___x_574_);
lean_ctor_set(v___x_569_, 0, v___x_573_);
v___x_576_ = v___x_569_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_nextMacroScope_560_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_ngen_561_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_auxDeclNGen_562_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_traceState_563_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_recordedDeps_564_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_messages_565_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_infoState_566_);
lean_ctor_set(v_reuseFailAlloc_595_, 9, v_snapshotTasks_567_);
v___x_576_ = v_reuseFailAlloc_595_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_mctx_579_; lean_object* v_zetaDeltaFVarIds_580_; lean_object* v_postponed_581_; lean_object* v_diag_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_593_; 
v___x_577_ = lean_st_ref_put(v___y_556_, v___x_576_);
v___x_578_ = lean_st_ref_take(v___y_555_);
v_mctx_579_ = lean_ctor_get(v___x_578_, 0);
v_zetaDeltaFVarIds_580_ = lean_ctor_get(v___x_578_, 2);
v_postponed_581_ = lean_ctor_get(v___x_578_, 3);
v_diag_582_ = lean_ctor_get(v___x_578_, 4);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_578_, 1);
lean_dec(v_unused_594_);
v___x_584_ = v___x_578_;
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_diag_582_);
lean_inc(v_postponed_581_);
lean_inc(v_zetaDeltaFVarIds_580_);
lean_inc(v_mctx_579_);
lean_dec(v___x_578_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = lean_box(0);
v___x_587_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__1);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_mctx_579_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_zetaDeltaFVarIds_580_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_postponed_581_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v_diag_582_);
v___x_589_ = v_reuseFailAlloc_592_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_st_ref_put(v___y_555_, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_586_);
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_598_, lean_object* v_s_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v_s_boxed_603_; lean_object* v_res_604_; 
v_s_boxed_603_ = lean_unbox(v_s_599_);
v_res_604_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_598_, v_s_boxed_603_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec(v___y_600_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___x_613_; lean_object* v___x_614_; 
v___x_613_ = 2;
v___x_614_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_605_, v___x_613_, v___y_609_, v___y_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_623_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_636_, lean_object* v_as_637_, size_t v_i_638_, size_t v_stop_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_eq(v_i_638_, v_stop_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v_name_642_; lean_object* v___x_643_; uint8_t v___x_644_; uint8_t v___x_645_; uint8_t v___y_647_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_641_ = lean_array_uget_borrowed(v_as_637_, v_i_638_);
v_name_642_ = lean_ctor_get(v___x_641_, 0);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_nat_dec_lt(v___x_643_, v___x_636_);
v___x_645_ = 1;
v___x_651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_652_ = lean_name_eq(v_name_642_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_654_ = lean_name_eq(v_name_642_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_656_ = lean_name_eq(v_name_642_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_658_ = lean_name_eq(v_name_642_, v___x_657_);
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___x_644_;
goto v___jp_646_;
}
}
else
{
v___y_647_ = v___x_644_;
goto v___jp_646_;
}
}
else
{
v___y_647_ = v___x_644_;
goto v___jp_646_;
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
size_t v___x_648_; size_t v___x_649_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_638_, v___x_648_);
v_i_638_ = v___x_649_;
goto _start;
}
else
{
return v___x_645_;
}
}
}
else
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_660_, lean_object* v_as_661_, lean_object* v_i_662_, lean_object* v_stop_663_){
_start:
{
size_t v_i_boxed_664_; size_t v_stop_boxed_665_; uint8_t v_res_666_; lean_object* v_r_667_; 
v_i_boxed_664_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v_stop_boxed_665_ = lean_unbox_usize(v_stop_663_);
lean_dec(v_stop_663_);
v_res_666_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_660_, v_as_661_, v_i_boxed_664_, v_stop_boxed_665_);
lean_dec_ref(v_as_661_);
lean_dec(v___x_660_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_668_, size_t v_sz_669_, size_t v_i_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_a_680_; uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_670_, v_sz_669_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_671_);
return v___x_685_;
}
else
{
lean_object* v_a_686_; uint8_t v_kind_687_; lean_object* v_modifiers_688_; lean_object* v_declName_689_; lean_object* v___x_690_; uint8_t v___x_693_; 
v_a_686_ = lean_array_uget_borrowed(v_as_668_, v_i_670_);
v_kind_687_ = lean_ctor_get_uint8(v_a_686_, sizeof(void*)*9);
v_modifiers_688_ = lean_ctor_get(v_a_686_, 2);
v_declName_689_ = lean_ctor_get(v_a_686_, 3);
v___x_690_ = lean_box(0);
v___x_693_ = l_Lean_Elab_DefKind_isTheorem(v_kind_687_);
if (v___x_693_ == 0)
{
lean_object* v_attrs_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_attrs_694_ = lean_ctor_get(v_modifiers_688_, 2);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_array_get_size(v_attrs_694_);
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
goto v___jp_691_;
}
else
{
if (v___x_697_ == 0)
{
goto v___jp_691_;
}
else
{
size_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_696_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_696_, v_attrs_694_, v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
goto v___jp_691_;
}
else
{
v_a_680_ = v___x_690_;
goto v___jp_679_;
}
}
}
}
else
{
v_a_680_ = v___x_690_;
goto v___jp_679_;
}
v___jp_691_:
{
lean_object* v___x_692_; 
lean_inc(v_declName_689_);
v___x_692_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_689_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_dec_ref_known(v___x_692_, 1);
v_a_680_ = v___x_690_;
goto v___jp_679_;
}
else
{
return v___x_692_;
}
}
}
v___jp_679_:
{
size_t v___x_681_; size_t v___x_682_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_670_, v___x_681_);
v_i_670_ = v___x_682_;
v_b_671_ = v_a_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_701_, lean_object* v_sz_702_, lean_object* v_i_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
size_t v_sz_boxed_712_; size_t v_i_boxed_713_; lean_object* v_res_714_; 
v_sz_boxed_712_ = lean_unbox_usize(v_sz_702_);
lean_dec(v_sz_702_);
v_i_boxed_713_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_701_, v_sz_boxed_712_, v_i_boxed_713_, v_b_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v_as_701_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; size_t v_sz_724_; size_t v___x_725_; lean_object* v___x_726_; 
v___x_723_ = lean_box(0);
v_sz_724_ = lean_array_size(v_preDefs_715_);
v___x_725_ = ((size_t)0ULL);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_715_, v_sz_724_, v___x_725_, v___x_723_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; 
lean_dec_ref_known(v___x_726_, 1);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_715_, v_sz_724_, v___x_725_, v___x_723_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_728_; size_t v_sz_729_; lean_object* v___x_730_; 
lean_dec_ref_known(v___x_727_, 1);
lean_inc_ref(v_preDefs_715_);
v___x_728_ = l_Array_reverse___redArg(v_preDefs_715_);
v_sz_729_ = lean_array_size(v___x_728_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_728_, v_sz_729_, v___x_725_, v___x_723_, v_a_720_, v_a_721_);
lean_dec_ref(v___x_728_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v___x_731_; 
lean_dec_ref_known(v___x_730_, 1);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_715_, v_sz_724_, v___x_725_, v___x_723_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec_ref(v_preDefs_715_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_739_);
v___x_733_ = v___x_731_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_dec(v___x_731_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_723_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_723_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
return v___x_731_;
}
}
else
{
lean_dec_ref(v_preDefs_715_);
return v___x_730_;
}
}
else
{
lean_dec_ref(v_preDefs_715_);
return v___x_727_;
}
}
else
{
lean_dec_ref(v_preDefs_715_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_749_, size_t v_sz_750_, size_t v_i_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_749_, v_sz_750_, v_i_751_, v_b_752_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_761_, lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_sz_boxed_772_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_773_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_761_, v_sz_boxed_772_, v_i_boxed_773_, v_b_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_775_, size_t v_sz_776_, size_t v_i_777_, lean_object* v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_775_, v_sz_776_, v_i_777_, v_b_778_, v___y_783_, v___y_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_787_, lean_object* v_sz_788_, lean_object* v_i_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
size_t v_sz_boxed_798_; size_t v_i_boxed_799_; lean_object* v_res_800_; 
v_sz_boxed_798_ = lean_unbox_usize(v_sz_788_);
lean_dec(v_sz_788_);
v_i_boxed_799_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_787_, v_sz_boxed_798_, v_i_boxed_799_, v_b_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec_ref(v_as_787_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_801_, uint8_t v_s_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_801_, v_s_802_, v___y_806_, v___y_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_811_, lean_object* v_s_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v_s_boxed_820_; lean_object* v_res_821_; 
v_s_boxed_820_ = lean_unbox(v_s_812_);
v_res_821_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_811_, v_s_boxed_820_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1___redArg();
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
return v___x_829_;
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
