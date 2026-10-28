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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t v___x_4568__boxed_63_; uint8_t v_cacheProofs_boxed_64_; size_t v_i_boxed_65_; size_t v_stop_boxed_66_; lean_object* v_res_67_; 
v___x_4568__boxed_63_ = lean_unbox(v___x_49_);
v_cacheProofs_boxed_64_ = lean_unbox(v_cacheProofs_51_);
v_i_boxed_65_ = lean_unbox_usize(v_i_53_);
lean_dec(v_i_53_);
v_stop_boxed_66_ = lean_unbox_usize(v_stop_54_);
lean_dec(v_stop_54_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_48_, v___x_4568__boxed_63_, v_declNames_50_, v_cacheProofs_boxed_64_, v_as_52_, v_i_boxed_65_, v_stop_boxed_66_, v_b_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
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
lean_object* v_declName_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_toCold_227_; lean_object* v_declName_228_; lean_object* v_currRecDepth_229_; lean_object* v_ref_230_; uint8_t v_suppressElabErrors_231_; uint8_t v_checkDeprecated_232_; uint8_t v_isRecordingDeps_233_; lean_object* v_fileName_234_; lean_object* v_fileMap_235_; lean_object* v_options_236_; lean_object* v_currNamespace_237_; lean_object* v_openDecls_238_; lean_object* v_initHeartbeats_239_; lean_object* v_maxHeartbeats_240_; lean_object* v_quotContext_241_; lean_object* v_currMacroScope_242_; lean_object* v_cancelTk_x3f_243_; lean_object* v_inheritedTraceOptions_244_; lean_object* v___f_245_; lean_object* v_preDefNonRec_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_declNames_249_; uint8_t v___x_250_; uint16_t v___y_252_; lean_object* v___y_253_; lean_object* v_fileName_254_; lean_object* v_fileMap_255_; lean_object* v_currNamespace_256_; lean_object* v_openDecls_257_; lean_object* v_initHeartbeats_258_; lean_object* v_maxHeartbeats_259_; lean_object* v_quotContext_260_; lean_object* v_currMacroScope_261_; lean_object* v_cancelTk_x3f_262_; lean_object* v_inheritedTraceOptions_263_; lean_object* v_currRecDepth_264_; lean_object* v_ref_265_; uint8_t v_suppressElabErrors_266_; uint8_t v_checkDeprecated_267_; uint8_t v_isRecordingDeps_268_; lean_object* v___y_269_; uint8_t v___y_303_; uint16_t v___y_304_; lean_object* v___y_305_; lean_object* v___y_328_; 
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
lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Lean_allowUnsafeReducibility;
v___x_340_ = 1;
lean_inc_ref(v_options_236_);
v___x_341_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_options_236_, v___x_339_, v___x_340_);
v___y_328_ = v___x_341_;
goto v___jp_327_;
}
else
{
lean_object* v___x_342_; 
lean_inc_ref(v_options_236_);
v___x_342_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_236_);
v___y_328_ = v___x_342_;
goto v___jp_327_;
}
v___jp_251_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = l_Lean_maxRecDepth;
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v___y_253_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_272_, 0, v_fileName_254_);
lean_ctor_set(v___x_272_, 1, v_fileMap_255_);
lean_ctor_set(v___x_272_, 2, v___y_253_);
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
lean_ctor_set_uint16(v___x_273_, sizeof(void*)*3, v___y_252_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 2, v_suppressElabErrors_266_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 3, v_checkDeprecated_267_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 4, v_isRecordingDeps_268_);
if (v___x_250_ == 0)
{
lean_object* v_declName_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_declName_274_ = lean_ctor_get(v_preDefNonRec_246_, 3);
lean_inc(v_declName_274_);
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v_declName_274_);
lean_ctor_set(v___x_275_, 1, v___x_248_);
v___x_276_ = 1;
v___x_277_ = lean_box(v___x_250_);
v___x_278_ = lean_box(v_cacheProofs_215_);
v___x_279_ = lean_box(v___x_250_);
v___x_280_ = lean_box(v___x_276_);
v___x_281_ = lean_box(v___x_276_);
lean_inc_ref(v_docCtx_211_);
v___x_282_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 15, 8);
lean_closure_set(v___x_282_, 0, v_docCtx_211_);
lean_closure_set(v___x_282_, 1, v_preDefNonRec_246_);
lean_closure_set(v___x_282_, 2, v___x_277_);
lean_closure_set(v___x_282_, 3, v___x_275_);
lean_closure_set(v___x_282_, 4, v___x_278_);
lean_closure_set(v___x_282_, 5, v___x_279_);
lean_closure_set(v___x_282_, 6, v___x_280_);
lean_closure_set(v___x_282_, 7, v___x_281_);
v___x_283_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v___x_250_, v___x_282_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_283_, 0);
lean_dec(v_unused_297_);
v___x_285_ = v___x_283_;
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
else
{
lean_dec(v___x_283_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = lean_array_get_size(v_preDefsNonrec_213_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_nat_dec_lt(v___x_225_, v___x_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_291_; 
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_249_);
lean_dec_ref(v_docCtx_211_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_288_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
else
{
size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
lean_del_object(v___x_285_);
v___x_293_ = ((size_t)0ULL);
v___x_294_ = lean_usize_of_nat(v___x_287_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_211_, v___x_250_, v_declNames_249_, v_cacheProofs_215_, v_preDefsNonrec_213_, v___x_293_, v___x_294_, v___x_288_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_295_;
}
}
}
else
{
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_249_);
lean_dec_ref(v_docCtx_211_);
return v___x_283_;
}
}
else
{
lean_object* v_declName_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_declNames_249_);
v_declName_298_ = lean_ctor_get(v_preDefNonRec_246_, 3);
v___x_299_ = 0;
lean_inc(v_declName_298_);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v_declName_298_);
lean_ctor_set(v___x_300_, 1, v___x_248_);
v___x_301_ = l_Lean_Elab_addNonRec(v_docCtx_211_, v_preDefNonRec_246_, v___x_299_, v___x_300_, v_cacheProofs_215_, v___x_299_, v___x_250_, v___x_250_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_301_;
}
}
v___jp_302_:
{
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v_nextMacroScope_308_; lean_object* v_ngen_309_; lean_object* v_auxDeclNGen_310_; lean_object* v_traceState_311_; lean_object* v_recordedDeps_312_; lean_object* v_messages_313_; lean_object* v_infoState_314_; lean_object* v_snapshotTasks_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_325_; 
v___x_306_ = lean_st_ref_take(v_a_221_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
v_nextMacroScope_308_ = lean_ctor_get(v___x_306_, 1);
v_ngen_309_ = lean_ctor_get(v___x_306_, 2);
v_auxDeclNGen_310_ = lean_ctor_get(v___x_306_, 3);
v_traceState_311_ = lean_ctor_get(v___x_306_, 4);
v_recordedDeps_312_ = lean_ctor_get(v___x_306_, 6);
v_messages_313_ = lean_ctor_get(v___x_306_, 7);
v_infoState_314_ = lean_ctor_get(v___x_306_, 8);
v_snapshotTasks_315_ = lean_ctor_get(v___x_306_, 9);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v___x_306_, 5);
lean_dec(v_unused_326_);
v___x_317_ = v___x_306_;
v_isShared_318_ = v_isSharedCheck_325_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_snapshotTasks_315_);
lean_inc(v_infoState_314_);
lean_inc(v_messages_313_);
lean_inc(v_recordedDeps_312_);
lean_inc(v_traceState_311_);
lean_inc(v_auxDeclNGen_310_);
lean_inc(v_ngen_309_);
lean_inc(v_nextMacroScope_308_);
lean_inc(v_env_307_);
lean_dec(v___x_306_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_325_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = l_Lean_Kernel_enableDiag(v_env_307_, v___y_303_);
v___x_320_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 5, v___x_320_);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_nextMacroScope_308_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_ngen_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_auxDeclNGen_310_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_traceState_311_);
lean_ctor_set(v_reuseFailAlloc_324_, 5, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_324_, 6, v_recordedDeps_312_);
lean_ctor_set(v_reuseFailAlloc_324_, 7, v_messages_313_);
lean_ctor_set(v_reuseFailAlloc_324_, 8, v_infoState_314_);
lean_ctor_set(v_reuseFailAlloc_324_, 9, v_snapshotTasks_315_);
v___x_322_ = v_reuseFailAlloc_324_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_st_ref_put(v_a_221_, v___x_322_);
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
v___y_252_ = v___y_304_;
v___y_253_ = v___y_305_;
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
v___jp_327_:
{
uint16_t v___x_329_; lean_object* v___x_330_; lean_object* v_env_331_; uint8_t v___x_332_; uint16_t v___x_333_; uint16_t v___x_334_; uint16_t v___x_335_; uint8_t v___x_336_; 
v___x_329_ = l_Lean_OptionFlags_ofOptions(v___y_328_);
v___x_330_ = lean_st_ref_get(v_a_221_);
v_env_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_env_331_);
lean_dec(v___x_330_);
v___x_332_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_331_);
lean_dec_ref(v_env_331_);
v___x_333_ = 512;
v___x_334_ = lean_uint16_land(v___x_329_, v___x_333_);
v___x_335_ = 0;
v___x_336_ = lean_uint16_dec_eq(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
if (v___x_332_ == 0)
{
uint8_t v___x_337_; 
v___x_337_ = 1;
v___y_303_ = v___x_337_;
v___y_304_ = v___x_329_;
v___y_305_ = v___y_328_;
goto v___jp_302_;
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
v___y_252_ = v___x_329_;
v___y_253_ = v___y_328_;
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
if (v___x_332_ == 0)
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
v___y_252_ = v___x_329_;
v___y_253_ = v___y_328_;
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
uint8_t v___x_338_; 
v___x_338_ = 0;
v___y_303_ = v___x_338_;
v___y_304_ = v___x_329_;
v___y_305_ = v___y_328_;
goto v___jp_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_343_, lean_object* v_preDefs_344_, lean_object* v_preDefsNonrec_345_, lean_object* v_unaryPreDefNonRec_346_, lean_object* v_cacheProofs_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
uint8_t v_cacheProofs_boxed_355_; lean_object* v_res_356_; 
v_cacheProofs_boxed_355_ = lean_unbox(v_cacheProofs_347_);
v_res_356_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_343_, v_preDefs_344_, v_preDefsNonrec_345_, v_unaryPreDefNonRec_346_, v_cacheProofs_boxed_355_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec_ref(v_preDefsNonrec_345_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(uint8_t v_flag_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_357_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___boxed(lean_object* v_flag_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v_flag_boxed_374_; lean_object* v_res_375_; 
v_flag_boxed_374_ = lean_unbox(v_flag_366_);
v_res_375_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(v_flag_boxed_374_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object* v_00_u03b1_376_, uint8_t v_flag_377_, lean_object* v_x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_377_, v_x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object* v_00_u03b1_387_, lean_object* v_flag_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v_flag_boxed_397_; lean_object* v_res_398_; 
v_flag_boxed_397_ = lean_unbox(v_flag_388_);
v_res_398_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v_00_u03b1_387_, v_flag_boxed_397_, v_x_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_399_, uint8_t v_cacheProofs_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_399_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l_Lean_Elab_abstractNestedProofs(v_a_407_, v_cacheProofs_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_408_;
}
else
{
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_409_, lean_object* v_cacheProofs_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
uint8_t v_cacheProofs_boxed_416_; lean_object* v_res_417_; 
v_cacheProofs_boxed_416_ = lean_unbox(v_cacheProofs_410_);
v_res_417_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_409_, v_cacheProofs_boxed_416_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_418_, size_t v_sz_419_, size_t v_i_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_b_421_);
return v___x_426_;
}
else
{
lean_object* v_a_427_; lean_object* v_declName_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_427_ = lean_array_uget_borrowed(v_as_418_, v_i_420_);
v_declName_428_ = lean_ctor_get(v_a_427_, 3);
v___x_429_ = lean_box(0);
lean_inc(v_declName_428_);
v___x_430_ = l_Lean_enableRealizationsForConst(v_declName_428_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_430_) == 0)
{
size_t v___x_431_; size_t v___x_432_; 
lean_dec_ref_known(v___x_430_, 1);
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_420_, v___x_431_);
v_i_420_ = v___x_432_;
v_b_421_ = v___x_429_;
goto _start;
}
else
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_434_, lean_object* v_sz_435_, lean_object* v_i_436_, lean_object* v_b_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
size_t v_sz_boxed_441_; size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_sz_boxed_441_ = lean_unbox_usize(v_sz_435_);
lean_dec(v_sz_435_);
v_i_boxed_442_ = lean_unbox_usize(v_i_436_);
lean_dec(v_i_436_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_434_, v_sz_boxed_441_, v_i_boxed_442_, v_b_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec_ref(v_as_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_444_, size_t v_sz_445_, size_t v_i_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_lt(v_i_446_, v_sz_445_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_b_447_);
return v___x_454_;
}
else
{
lean_object* v_a_455_; lean_object* v_declName_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_a_455_ = lean_array_uget_borrowed(v_as_444_, v_i_446_);
v_declName_456_ = lean_ctor_get(v_a_455_, 3);
v___x_457_ = lean_box(0);
lean_inc(v_declName_456_);
v___x_458_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_456_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_458_) == 0)
{
size_t v___x_459_; size_t v___x_460_; 
lean_dec_ref_known(v___x_458_, 1);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_add(v_i_446_, v___x_459_);
v_i_446_ = v___x_460_;
v_b_447_ = v___x_457_;
goto _start;
}
else
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_462_, lean_object* v_sz_463_, lean_object* v_i_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_463_);
lean_dec(v_sz_463_);
v_i_boxed_472_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_462_, v_sz_boxed_471_, v_i_boxed_472_, v_b_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec_ref(v_as_462_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_474_, size_t v_sz_475_, size_t v_i_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_lt(v_i_476_, v_sz_475_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_477_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
v___x_487_ = lean_box(0);
v_a_488_ = lean_array_uget_borrowed(v_as_474_, v_i_476_);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_mk_empty_array_with_capacity(v___x_489_);
lean_inc(v_a_488_);
v___x_491_ = lean_array_push(v___x_490_, v_a_488_);
v___x_492_ = 1;
v___x_493_ = l_Lean_Elab_applyAttributesOf(v___x_491_, v___x_492_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec_ref(v___x_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
size_t v___x_494_; size_t v___x_495_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_476_, v___x_494_);
v_i_476_ = v___x_495_;
v_b_477_ = v___x_487_;
goto _start;
}
else
{
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_497_, lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
size_t v_sz_boxed_508_; size_t v_i_boxed_509_; lean_object* v_res_510_; 
v_sz_boxed_508_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_509_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_497_, v_sz_boxed_508_, v_i_boxed_509_, v_b_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v_as_497_);
return v_res_510_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_512_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
lean_ctor_set(v___x_512_, 2, v___x_511_);
lean_ctor_set(v___x_512_, 3, v___x_511_);
lean_ctor_set(v___x_512_, 4, v___x_511_);
lean_ctor_set(v___x_512_, 5, v___x_511_);
lean_ctor_set(v___x_512_, 6, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_513_, uint8_t v_s_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; lean_object* v_env_519_; lean_object* v_nextMacroScope_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_traceState_523_; lean_object* v_recordedDeps_524_; lean_object* v_messages_525_; lean_object* v_infoState_526_; lean_object* v_snapshotTasks_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_556_; 
v___x_518_ = lean_st_ref_take(v___y_516_);
v_env_519_ = lean_ctor_get(v___x_518_, 0);
v_nextMacroScope_520_ = lean_ctor_get(v___x_518_, 1);
v_ngen_521_ = lean_ctor_get(v___x_518_, 2);
v_auxDeclNGen_522_ = lean_ctor_get(v___x_518_, 3);
v_traceState_523_ = lean_ctor_get(v___x_518_, 4);
v_recordedDeps_524_ = lean_ctor_get(v___x_518_, 6);
v_messages_525_ = lean_ctor_get(v___x_518_, 7);
v_infoState_526_ = lean_ctor_get(v___x_518_, 8);
v_snapshotTasks_527_ = lean_ctor_get(v___x_518_, 9);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_518_, 5);
lean_dec(v_unused_557_);
v___x_529_ = v___x_518_;
v_isShared_530_ = v_isSharedCheck_556_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snapshotTasks_527_);
lean_inc(v_infoState_526_);
lean_inc(v_messages_525_);
lean_inc(v_recordedDeps_524_);
lean_inc(v_traceState_523_);
lean_inc(v_auxDeclNGen_522_);
lean_inc(v_ngen_521_);
lean_inc(v_nextMacroScope_520_);
lean_inc(v_env_519_);
lean_dec(v___x_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_556_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_531_ = 0;
v___x_532_ = lean_box(0);
v___x_533_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_519_, v_declName_513_, v_s_514_, v___x_531_, v___x_532_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 5, v___x_534_);
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_nextMacroScope_520_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_traceState_523_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_recordedDeps_524_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_messages_525_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_infoState_526_);
lean_ctor_set(v_reuseFailAlloc_555_, 9, v_snapshotTasks_527_);
v___x_536_ = v_reuseFailAlloc_555_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_mctx_539_; lean_object* v_zetaDeltaFVarIds_540_; lean_object* v_postponed_541_; lean_object* v_diag_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_553_; 
v___x_537_ = lean_st_ref_put(v___y_516_, v___x_536_);
v___x_538_ = lean_st_ref_take(v___y_515_);
v_mctx_539_ = lean_ctor_get(v___x_538_, 0);
v_zetaDeltaFVarIds_540_ = lean_ctor_get(v___x_538_, 2);
v_postponed_541_ = lean_ctor_get(v___x_538_, 3);
v_diag_542_ = lean_ctor_get(v___x_538_, 4);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v___x_538_, 1);
lean_dec(v_unused_554_);
v___x_544_ = v___x_538_;
v_isShared_545_ = v_isSharedCheck_553_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_diag_542_);
lean_inc(v_postponed_541_);
lean_inc(v_zetaDeltaFVarIds_540_);
lean_inc(v_mctx_539_);
lean_dec(v___x_538_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_553_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_box(0);
v___x_547_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_547_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_mctx_539_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_zetaDeltaFVarIds_540_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_postponed_541_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_diag_542_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_st_ref_put(v___y_515_, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_546_);
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_558_, lean_object* v_s_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
uint8_t v_s_boxed_563_; lean_object* v_res_564_; 
v_s_boxed_563_ = lean_unbox(v_s_559_);
v_res_564_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_558_, v_s_boxed_563_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec(v___y_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_573_; lean_object* v___x_574_; 
v___x_573_ = 2;
v___x_574_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_565_, v___x_573_, v___y_569_, v___y_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_596_, lean_object* v_as_597_, size_t v_i_598_, size_t v_stop_599_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_eq(v_i_598_, v_stop_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v_name_602_; lean_object* v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; uint8_t v___y_607_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_601_ = lean_array_uget_borrowed(v_as_597_, v_i_598_);
v_name_602_ = lean_ctor_get(v___x_601_, 0);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_nat_dec_lt(v___x_603_, v___x_596_);
v___x_605_ = 1;
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_612_ = lean_name_eq(v_name_602_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_614_ = lean_name_eq(v_name_602_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_616_ = lean_name_eq(v_name_602_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_618_ = lean_name_eq(v_name_602_, v___x_617_);
v___y_607_ = v___x_618_;
goto v___jp_606_;
}
else
{
v___y_607_ = v___x_604_;
goto v___jp_606_;
}
}
else
{
v___y_607_ = v___x_604_;
goto v___jp_606_;
}
}
else
{
v___y_607_ = v___x_604_;
goto v___jp_606_;
}
v___jp_606_:
{
if (v___y_607_ == 0)
{
size_t v___x_608_; size_t v___x_609_; 
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_598_, v___x_608_);
v_i_598_ = v___x_609_;
goto _start;
}
else
{
return v___x_605_;
}
}
}
else
{
uint8_t v___x_619_; 
v___x_619_ = 0;
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_620_, lean_object* v_as_621_, lean_object* v_i_622_, lean_object* v_stop_623_){
_start:
{
size_t v_i_boxed_624_; size_t v_stop_boxed_625_; uint8_t v_res_626_; lean_object* v_r_627_; 
v_i_boxed_624_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_stop_boxed_625_ = lean_unbox_usize(v_stop_623_);
lean_dec(v_stop_623_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_620_, v_as_621_, v_i_boxed_624_, v_stop_boxed_625_);
lean_dec_ref(v_as_621_);
lean_dec(v___x_620_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_628_, size_t v_sz_629_, size_t v_i_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_a_640_; uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_lt(v_i_630_, v_sz_629_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v_b_631_);
return v___x_645_;
}
else
{
lean_object* v_a_646_; uint8_t v_kind_647_; lean_object* v_modifiers_648_; lean_object* v_declName_649_; lean_object* v___x_650_; uint8_t v___x_653_; 
v_a_646_ = lean_array_uget_borrowed(v_as_628_, v_i_630_);
v_kind_647_ = lean_ctor_get_uint8(v_a_646_, sizeof(void*)*9);
v_modifiers_648_ = lean_ctor_get(v_a_646_, 2);
v_declName_649_ = lean_ctor_get(v_a_646_, 3);
v___x_650_ = lean_box(0);
v___x_653_ = l_Lean_Elab_DefKind_isTheorem(v_kind_647_);
if (v___x_653_ == 0)
{
lean_object* v_attrs_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_attrs_654_ = lean_ctor_get(v_modifiers_648_, 2);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_array_get_size(v_attrs_654_);
v___x_657_ = lean_nat_dec_lt(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
goto v___jp_651_;
}
else
{
if (v___x_657_ == 0)
{
goto v___jp_651_;
}
else
{
size_t v___x_658_; size_t v___x_659_; uint8_t v___x_660_; 
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_656_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_656_, v_attrs_654_, v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
goto v___jp_651_;
}
else
{
v_a_640_ = v___x_650_;
goto v___jp_639_;
}
}
}
}
else
{
v_a_640_ = v___x_650_;
goto v___jp_639_;
}
v___jp_651_:
{
lean_object* v___x_652_; 
lean_inc(v_declName_649_);
v___x_652_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_649_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_dec_ref_known(v___x_652_, 1);
v_a_640_ = v___x_650_;
goto v___jp_639_;
}
else
{
return v___x_652_;
}
}
}
v___jp_639_:
{
size_t v___x_641_; size_t v___x_642_; 
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_i_630_, v___x_641_);
v_i_630_ = v___x_642_;
v_b_631_ = v_a_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_661_, lean_object* v_sz_662_, lean_object* v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
size_t v_sz_boxed_672_; size_t v_i_boxed_673_; lean_object* v_res_674_; 
v_sz_boxed_672_ = lean_unbox_usize(v_sz_662_);
lean_dec(v_sz_662_);
v_i_boxed_673_ = lean_unbox_usize(v_i_663_);
lean_dec(v_i_663_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_661_, v_sz_boxed_672_, v_i_boxed_673_, v_b_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_as_661_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; size_t v_sz_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_box(0);
v_sz_684_ = lean_array_size(v_preDefs_675_);
v___x_685_ = ((size_t)0ULL);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_675_, v_sz_684_, v___x_685_, v___x_683_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v___x_687_; 
lean_dec_ref_known(v___x_686_, 1);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_675_, v_sz_684_, v___x_685_, v___x_683_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_688_; size_t v_sz_689_; lean_object* v___x_690_; 
lean_dec_ref_known(v___x_687_, 1);
lean_inc_ref(v_preDefs_675_);
v___x_688_ = l_Array_reverse___redArg(v_preDefs_675_);
v_sz_689_ = lean_array_size(v___x_688_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_688_, v_sz_689_, v___x_685_, v___x_683_, v_a_680_, v_a_681_);
lean_dec_ref(v___x_688_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_691_; 
lean_dec_ref_known(v___x_690_, 1);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_675_, v_sz_684_, v___x_685_, v___x_683_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec_ref(v_preDefs_675_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v___x_691_, 0);
lean_dec(v_unused_699_);
v___x_693_ = v___x_691_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_dec(v___x_691_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_683_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_683_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
return v___x_691_;
}
}
else
{
lean_dec_ref(v_preDefs_675_);
return v___x_690_;
}
}
else
{
lean_dec_ref(v_preDefs_675_);
return v___x_687_;
}
}
else
{
lean_dec_ref(v_preDefs_675_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_709_, uint8_t v_s_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_709_, v_s_710_, v___y_714_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_719_, lean_object* v_s_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
uint8_t v_s_boxed_728_; lean_object* v_res_729_; 
v_s_boxed_728_ = lean_unbox(v_s_720_);
v_res_729_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_719_, v_s_boxed_728_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_730_, size_t v_sz_731_, size_t v_i_732_, lean_object* v_b_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_730_, v_sz_731_, v_i_732_, v_b_733_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_742_, lean_object* v_sz_743_, lean_object* v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
size_t v_sz_boxed_753_; size_t v_i_boxed_754_; lean_object* v_res_755_; 
v_sz_boxed_753_ = lean_unbox_usize(v_sz_743_);
lean_dec(v_sz_743_);
v_i_boxed_754_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_742_, v_sz_boxed_753_, v_i_boxed_754_, v_b_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v_as_742_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_756_, v_sz_757_, v_i_758_, v_b_759_, v___y_764_, v___y_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_768_, lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_sz_boxed_779_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_780_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_768_, v_sz_boxed_779_, v_i_boxed_780_, v_b_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_as_768_);
return v_res_781_;
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
