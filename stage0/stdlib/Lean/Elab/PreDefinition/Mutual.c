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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t v___x_4560__boxed_63_; uint8_t v_cacheProofs_boxed_64_; size_t v_i_boxed_65_; size_t v_stop_boxed_66_; lean_object* v_res_67_; 
v___x_4560__boxed_63_ = lean_unbox(v___x_49_);
v_cacheProofs_boxed_64_ = lean_unbox(v_cacheProofs_51_);
v_i_boxed_65_ = lean_unbox_usize(v_i_53_);
lean_dec(v_i_53_);
v_stop_boxed_66_ = lean_unbox_usize(v_stop_54_);
lean_dec(v_stop_54_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_48_, v___x_4560__boxed_63_, v_declNames_50_, v_cacheProofs_boxed_64_, v_as_52_, v_i_boxed_65_, v_stop_boxed_66_, v_b_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
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
lean_object* v_declName_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_toCold_227_; lean_object* v_declName_228_; lean_object* v_currRecDepth_229_; lean_object* v_ref_230_; uint8_t v_suppressElabErrors_231_; uint8_t v_isRecordingDeps_232_; lean_object* v_fileName_233_; lean_object* v_fileMap_234_; lean_object* v_options_235_; lean_object* v_currNamespace_236_; lean_object* v_openDecls_237_; lean_object* v_initHeartbeats_238_; lean_object* v_maxHeartbeats_239_; lean_object* v_quotContext_240_; lean_object* v_currMacroScope_241_; lean_object* v_cancelTk_x3f_242_; lean_object* v_inheritedTraceOptions_243_; lean_object* v___f_244_; lean_object* v_preDefNonRec_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_declNames_248_; uint8_t v___x_249_; lean_object* v___y_251_; uint16_t v___y_252_; lean_object* v_fileName_253_; lean_object* v_fileMap_254_; lean_object* v_currNamespace_255_; lean_object* v_openDecls_256_; lean_object* v_initHeartbeats_257_; lean_object* v_maxHeartbeats_258_; lean_object* v_quotContext_259_; lean_object* v_currMacroScope_260_; lean_object* v_cancelTk_x3f_261_; lean_object* v_inheritedTraceOptions_262_; lean_object* v_currRecDepth_263_; lean_object* v_ref_264_; uint8_t v_suppressElabErrors_265_; uint8_t v_isRecordingDeps_266_; lean_object* v___y_267_; lean_object* v___y_308_; uint16_t v___y_309_; uint8_t v___y_310_; lean_object* v___y_333_; 
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
v_isRecordingDeps_232_ = lean_ctor_get_uint8(v_a_220_, sizeof(void*)*3 + 3);
v_fileName_233_ = lean_ctor_get(v_toCold_227_, 0);
v_fileMap_234_ = lean_ctor_get(v_toCold_227_, 1);
v_options_235_ = lean_ctor_get(v_toCold_227_, 2);
v_currNamespace_236_ = lean_ctor_get(v_toCold_227_, 4);
v_openDecls_237_ = lean_ctor_get(v_toCold_227_, 5);
v_initHeartbeats_238_ = lean_ctor_get(v_toCold_227_, 6);
v_maxHeartbeats_239_ = lean_ctor_get(v_toCold_227_, 7);
v_quotContext_240_ = lean_ctor_get(v_toCold_227_, 8);
v_currMacroScope_241_ = lean_ctor_get(v_toCold_227_, 9);
v_cancelTk_x3f_242_ = lean_ctor_get(v_toCold_227_, 10);
v_inheritedTraceOptions_243_ = lean_ctor_get(v_toCold_227_, 11);
v___f_244_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v_preDefNonRec_245_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_214_, v___f_244_);
v___x_246_ = lean_array_to_list(v_preDefs_212_);
v___x_247_ = lean_box(0);
v_declNames_248_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_246_, v___x_247_);
v___x_249_ = lean_name_eq(v_declName_223_, v_declName_228_);
lean_dec(v_declName_228_);
lean_dec(v_declName_223_);
if (v_isRecordingDeps_232_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_allowUnsafeReducibility;
v___x_345_ = 1;
lean_inc_ref(v_options_235_);
v___x_346_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_options_235_, v___x_344_, v___x_345_);
v___y_333_ = v___x_346_;
goto v___jp_332_;
}
else
{
lean_object* v___x_347_; 
lean_inc_ref(v_options_235_);
v___x_347_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_235_);
v___y_333_ = v___x_347_;
goto v___jp_332_;
}
v___jp_250_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = l_Lean_maxRecDepth;
v___x_269_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v___y_251_, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_270_, 0, v_fileName_253_);
lean_ctor_set(v___x_270_, 1, v_fileMap_254_);
lean_ctor_set(v___x_270_, 2, v___y_251_);
lean_ctor_set(v___x_270_, 3, v___x_269_);
lean_ctor_set(v___x_270_, 4, v_currNamespace_255_);
lean_ctor_set(v___x_270_, 5, v_openDecls_256_);
lean_ctor_set(v___x_270_, 6, v_initHeartbeats_257_);
lean_ctor_set(v___x_270_, 7, v_maxHeartbeats_258_);
lean_ctor_set(v___x_270_, 8, v_quotContext_259_);
lean_ctor_set(v___x_270_, 9, v_currMacroScope_260_);
lean_ctor_set(v___x_270_, 10, v_cancelTk_x3f_261_);
lean_ctor_set(v___x_270_, 11, v_inheritedTraceOptions_262_);
lean_inc(v_ref_264_);
lean_inc(v_currRecDepth_263_);
v___x_271_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_currRecDepth_263_);
lean_ctor_set(v___x_271_, 2, v_ref_264_);
lean_ctor_set_uint16(v___x_271_, sizeof(void*)*3, v___y_252_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*3 + 2, v_suppressElabErrors_265_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*3 + 3, v_isRecordingDeps_266_);
if (v___x_249_ == 0)
{
lean_object* v_declName_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_declName_272_ = lean_ctor_get(v_preDefNonRec_245_, 3);
lean_inc(v_declName_272_);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v_declName_272_);
lean_ctor_set(v___x_273_, 1, v___x_247_);
v___x_274_ = 1;
v___x_275_ = lean_box(v___x_249_);
v___x_276_ = lean_box(v_cacheProofs_215_);
v___x_277_ = lean_box(v___x_249_);
v___x_278_ = lean_box(v___x_274_);
v___x_279_ = lean_box(v___x_274_);
lean_inc_ref(v_docCtx_211_);
v___x_280_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 15, 8);
lean_closure_set(v___x_280_, 0, v_docCtx_211_);
lean_closure_set(v___x_280_, 1, v_preDefNonRec_245_);
lean_closure_set(v___x_280_, 2, v___x_275_);
lean_closure_set(v___x_280_, 3, v___x_273_);
lean_closure_set(v___x_280_, 4, v___x_276_);
lean_closure_set(v___x_280_, 5, v___x_277_);
lean_closure_set(v___x_280_, 6, v___x_278_);
lean_closure_set(v___x_280_, 7, v___x_279_);
v___x_281_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v___x_249_, v___x_280_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_271_, v___y_267_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_301_; 
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_302_);
v___x_283_ = v___x_281_;
v_isShared_284_ = v_isSharedCheck_301_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___x_281_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_301_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_array_get_size(v_preDefsNonrec_213_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_nat_dec_lt(v___x_225_, v___x_285_);
if (v___x_287_ == 0)
{
lean_object* v___x_289_; 
lean_dec_ref_known(v___x_271_, 3);
lean_dec(v_declNames_248_);
lean_dec_ref(v_docCtx_211_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_286_);
v___x_289_ = v___x_283_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_286_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
uint8_t v___x_291_; 
v___x_291_ = lean_nat_dec_le(v___x_285_, v___x_285_);
if (v___x_291_ == 0)
{
if (v___x_287_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref_known(v___x_271_, 3);
lean_dec(v_declNames_248_);
lean_dec_ref(v_docCtx_211_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_286_);
v___x_293_ = v___x_283_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_286_);
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
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
lean_del_object(v___x_283_);
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_285_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_211_, v___x_249_, v_declNames_248_, v_cacheProofs_215_, v_preDefsNonrec_213_, v___x_295_, v___x_296_, v___x_286_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_271_, v___y_267_);
lean_dec_ref_known(v___x_271_, 3);
return v___x_297_;
}
}
else
{
size_t v___x_298_; size_t v___x_299_; lean_object* v___x_300_; 
lean_del_object(v___x_283_);
v___x_298_ = ((size_t)0ULL);
v___x_299_ = lean_usize_of_nat(v___x_285_);
v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_211_, v___x_249_, v_declNames_248_, v_cacheProofs_215_, v_preDefsNonrec_213_, v___x_298_, v___x_299_, v___x_286_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_271_, v___y_267_);
lean_dec_ref_known(v___x_271_, 3);
return v___x_300_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_271_, 3);
lean_dec(v_declNames_248_);
lean_dec_ref(v_docCtx_211_);
return v___x_281_;
}
}
else
{
lean_object* v_declName_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_declNames_248_);
v_declName_303_ = lean_ctor_get(v_preDefNonRec_245_, 3);
v___x_304_ = 0;
lean_inc(v_declName_303_);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v_declName_303_);
lean_ctor_set(v___x_305_, 1, v___x_247_);
v___x_306_ = l_Lean_Elab_addNonRec(v_docCtx_211_, v_preDefNonRec_245_, v___x_304_, v___x_305_, v_cacheProofs_215_, v___x_304_, v___x_249_, v___x_249_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_271_, v___y_267_);
lean_dec_ref_known(v___x_271_, 3);
return v___x_306_;
}
}
v___jp_307_:
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v_nextMacroScope_313_; lean_object* v_ngen_314_; lean_object* v_auxDeclNGen_315_; lean_object* v_traceState_316_; lean_object* v_recordedDeps_317_; lean_object* v_messages_318_; lean_object* v_infoState_319_; lean_object* v_snapshotTasks_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v___x_311_ = lean_st_ref_take(v_a_221_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
v_nextMacroScope_313_ = lean_ctor_get(v___x_311_, 1);
v_ngen_314_ = lean_ctor_get(v___x_311_, 2);
v_auxDeclNGen_315_ = lean_ctor_get(v___x_311_, 3);
v_traceState_316_ = lean_ctor_get(v___x_311_, 4);
v_recordedDeps_317_ = lean_ctor_get(v___x_311_, 6);
v_messages_318_ = lean_ctor_get(v___x_311_, 7);
v_infoState_319_ = lean_ctor_get(v___x_311_, 8);
v_snapshotTasks_320_ = lean_ctor_get(v___x_311_, 9);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v___x_311_, 5);
lean_dec(v_unused_331_);
v___x_322_ = v___x_311_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_snapshotTasks_320_);
lean_inc(v_infoState_319_);
lean_inc(v_messages_318_);
lean_inc(v_recordedDeps_317_);
lean_inc(v_traceState_316_);
lean_inc(v_auxDeclNGen_315_);
lean_inc(v_ngen_314_);
lean_inc(v_nextMacroScope_313_);
lean_inc(v_env_312_);
lean_dec(v___x_311_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = l_Lean_Kernel_enableDiag(v_env_312_, v___y_310_);
v___x_325_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 5, v___x_325_);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_nextMacroScope_313_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_ngen_314_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_auxDeclNGen_315_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v_traceState_316_);
lean_ctor_set(v_reuseFailAlloc_329_, 5, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_329_, 6, v_recordedDeps_317_);
lean_ctor_set(v_reuseFailAlloc_329_, 7, v_messages_318_);
lean_ctor_set(v_reuseFailAlloc_329_, 8, v_infoState_319_);
lean_ctor_set(v_reuseFailAlloc_329_, 9, v_snapshotTasks_320_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; 
v___x_328_ = lean_st_ref_put(v_a_221_, v___x_327_);
lean_inc_ref(v_inheritedTraceOptions_243_);
lean_inc(v_cancelTk_x3f_242_);
lean_inc(v_currMacroScope_241_);
lean_inc(v_quotContext_240_);
lean_inc(v_maxHeartbeats_239_);
lean_inc(v_initHeartbeats_238_);
lean_inc(v_openDecls_237_);
lean_inc(v_currNamespace_236_);
lean_inc_ref(v_fileMap_234_);
lean_inc_ref(v_fileName_233_);
v___y_251_ = v___y_308_;
v___y_252_ = v___y_309_;
v_fileName_253_ = v_fileName_233_;
v_fileMap_254_ = v_fileMap_234_;
v_currNamespace_255_ = v_currNamespace_236_;
v_openDecls_256_ = v_openDecls_237_;
v_initHeartbeats_257_ = v_initHeartbeats_238_;
v_maxHeartbeats_258_ = v_maxHeartbeats_239_;
v_quotContext_259_ = v_quotContext_240_;
v_currMacroScope_260_ = v_currMacroScope_241_;
v_cancelTk_x3f_261_ = v_cancelTk_x3f_242_;
v_inheritedTraceOptions_262_ = v_inheritedTraceOptions_243_;
v_currRecDepth_263_ = v_currRecDepth_229_;
v_ref_264_ = v_ref_230_;
v_suppressElabErrors_265_ = v_suppressElabErrors_231_;
v_isRecordingDeps_266_ = v_isRecordingDeps_232_;
v___y_267_ = v_a_221_;
goto v___jp_250_;
}
}
}
v___jp_332_:
{
uint16_t v___x_334_; lean_object* v___x_335_; lean_object* v_env_336_; uint8_t v___x_337_; uint16_t v___x_338_; uint16_t v___x_339_; uint16_t v___x_340_; uint8_t v___x_341_; 
v___x_334_ = l_Lean_OptionFlags_ofOptions(v___y_333_);
v___x_335_ = lean_st_ref_get(v_a_221_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_env_336_);
lean_dec(v___x_335_);
v___x_337_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_336_);
lean_dec_ref(v_env_336_);
v___x_338_ = 512;
v___x_339_ = lean_uint16_land(v___x_334_, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_uint16_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
if (v___x_337_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = 1;
v___y_308_ = v___y_333_;
v___y_309_ = v___x_334_;
v___y_310_ = v___x_342_;
goto v___jp_307_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_243_);
lean_inc(v_cancelTk_x3f_242_);
lean_inc(v_currMacroScope_241_);
lean_inc(v_quotContext_240_);
lean_inc(v_maxHeartbeats_239_);
lean_inc(v_initHeartbeats_238_);
lean_inc(v_openDecls_237_);
lean_inc(v_currNamespace_236_);
lean_inc_ref(v_fileMap_234_);
lean_inc_ref(v_fileName_233_);
v___y_251_ = v___y_333_;
v___y_252_ = v___x_334_;
v_fileName_253_ = v_fileName_233_;
v_fileMap_254_ = v_fileMap_234_;
v_currNamespace_255_ = v_currNamespace_236_;
v_openDecls_256_ = v_openDecls_237_;
v_initHeartbeats_257_ = v_initHeartbeats_238_;
v_maxHeartbeats_258_ = v_maxHeartbeats_239_;
v_quotContext_259_ = v_quotContext_240_;
v_currMacroScope_260_ = v_currMacroScope_241_;
v_cancelTk_x3f_261_ = v_cancelTk_x3f_242_;
v_inheritedTraceOptions_262_ = v_inheritedTraceOptions_243_;
v_currRecDepth_263_ = v_currRecDepth_229_;
v_ref_264_ = v_ref_230_;
v_suppressElabErrors_265_ = v_suppressElabErrors_231_;
v_isRecordingDeps_266_ = v_isRecordingDeps_232_;
v___y_267_ = v_a_221_;
goto v___jp_250_;
}
}
else
{
if (v___x_337_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_243_);
lean_inc(v_cancelTk_x3f_242_);
lean_inc(v_currMacroScope_241_);
lean_inc(v_quotContext_240_);
lean_inc(v_maxHeartbeats_239_);
lean_inc(v_initHeartbeats_238_);
lean_inc(v_openDecls_237_);
lean_inc(v_currNamespace_236_);
lean_inc_ref(v_fileMap_234_);
lean_inc_ref(v_fileName_233_);
v___y_251_ = v___y_333_;
v___y_252_ = v___x_334_;
v_fileName_253_ = v_fileName_233_;
v_fileMap_254_ = v_fileMap_234_;
v_currNamespace_255_ = v_currNamespace_236_;
v_openDecls_256_ = v_openDecls_237_;
v_initHeartbeats_257_ = v_initHeartbeats_238_;
v_maxHeartbeats_258_ = v_maxHeartbeats_239_;
v_quotContext_259_ = v_quotContext_240_;
v_currMacroScope_260_ = v_currMacroScope_241_;
v_cancelTk_x3f_261_ = v_cancelTk_x3f_242_;
v_inheritedTraceOptions_262_ = v_inheritedTraceOptions_243_;
v_currRecDepth_263_ = v_currRecDepth_229_;
v_ref_264_ = v_ref_230_;
v_suppressElabErrors_265_ = v_suppressElabErrors_231_;
v_isRecordingDeps_266_ = v_isRecordingDeps_232_;
v___y_267_ = v_a_221_;
goto v___jp_250_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = 0;
v___y_308_ = v___y_333_;
v___y_309_ = v___x_334_;
v___y_310_ = v___x_343_;
goto v___jp_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_348_, lean_object* v_preDefs_349_, lean_object* v_preDefsNonrec_350_, lean_object* v_unaryPreDefNonRec_351_, lean_object* v_cacheProofs_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
uint8_t v_cacheProofs_boxed_360_; lean_object* v_res_361_; 
v_cacheProofs_boxed_360_ = lean_unbox(v_cacheProofs_352_);
v_res_361_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_348_, v_preDefs_349_, v_preDefsNonrec_350_, v_unaryPreDefNonRec_351_, v_cacheProofs_boxed_360_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec_ref(v_preDefsNonrec_350_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(uint8_t v_flag_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_362_, v___y_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___boxed(lean_object* v_flag_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v_flag_boxed_379_; lean_object* v_res_380_; 
v_flag_boxed_379_ = lean_unbox(v_flag_371_);
v_res_380_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(v_flag_boxed_379_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object* v_00_u03b1_381_, uint8_t v_flag_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_382_, v_x_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object* v_00_u03b1_392_, lean_object* v_flag_393_, lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v_flag_boxed_402_; lean_object* v_res_403_; 
v_flag_boxed_402_ = lean_unbox(v_flag_393_);
v_res_403_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v_00_u03b1_392_, v_flag_boxed_402_, v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_404_, uint8_t v_cacheProofs_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_404_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Elab_abstractNestedProofs(v_a_412_, v_cacheProofs_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_413_;
}
else
{
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_414_, lean_object* v_cacheProofs_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
uint8_t v_cacheProofs_boxed_421_; lean_object* v_res_422_; 
v_cacheProofs_boxed_421_ = lean_unbox(v_cacheProofs_415_);
v_res_422_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_414_, v_cacheProofs_boxed_421_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_426_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v_declName_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_a_432_ = lean_array_uget_borrowed(v_as_423_, v_i_425_);
v_declName_433_ = lean_ctor_get(v_a_432_, 3);
v___x_434_ = lean_box(0);
lean_inc(v_declName_433_);
v___x_435_ = l_Lean_enableRealizationsForConst(v_declName_433_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_435_) == 0)
{
size_t v___x_436_; size_t v___x_437_; 
lean_dec_ref_known(v___x_435_, 1);
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_425_, v___x_436_);
v_i_425_ = v___x_437_;
v_b_426_ = v___x_434_;
goto _start;
}
else
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_439_, lean_object* v_sz_440_, lean_object* v_i_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_440_);
lean_dec(v_sz_440_);
v_i_boxed_447_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_439_, v_sz_boxed_446_, v_i_boxed_447_, v_b_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_as_439_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_449_, size_t v_sz_450_, size_t v_i_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_451_, v_sz_450_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_b_452_);
return v___x_459_;
}
else
{
lean_object* v_a_460_; lean_object* v_declName_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_460_ = lean_array_uget_borrowed(v_as_449_, v_i_451_);
v_declName_461_ = lean_ctor_get(v_a_460_, 3);
v___x_462_ = lean_box(0);
lean_inc(v_declName_461_);
v___x_463_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_461_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_463_) == 0)
{
size_t v___x_464_; size_t v___x_465_; 
lean_dec_ref_known(v___x_463_, 1);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_add(v_i_451_, v___x_464_);
v_i_451_ = v___x_465_;
v_b_452_ = v___x_462_;
goto _start;
}
else
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_467_, lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_477_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_467_, v_sz_boxed_476_, v_i_boxed_477_, v_b_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec_ref(v_as_467_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_b_482_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; 
v___x_492_ = lean_box(0);
v_a_493_ = lean_array_uget_borrowed(v_as_479_, v_i_481_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_mk_empty_array_with_capacity(v___x_494_);
lean_inc(v_a_493_);
v___x_496_ = lean_array_push(v___x_495_, v_a_493_);
v___x_497_ = 1;
v___x_498_ = l_Lean_Elab_applyAttributesOf(v___x_496_, v___x_497_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec_ref(v___x_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
size_t v___x_499_; size_t v___x_500_; 
lean_dec_ref_known(v___x_498_, 1);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_481_, v___x_499_);
v_i_481_ = v___x_500_;
v_b_482_ = v___x_492_;
goto _start;
}
else
{
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_502_, lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
size_t v_sz_boxed_513_; size_t v_i_boxed_514_; lean_object* v_res_515_; 
v_sz_boxed_513_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_514_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_502_, v_sz_boxed_513_, v_i_boxed_514_, v_b_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_as_502_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_517_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
lean_ctor_set(v___x_517_, 2, v___x_516_);
lean_ctor_set(v___x_517_, 3, v___x_516_);
lean_ctor_set(v___x_517_, 4, v___x_516_);
lean_ctor_set(v___x_517_, 5, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_518_, uint8_t v_s_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v_nextMacroScope_525_; lean_object* v_ngen_526_; lean_object* v_auxDeclNGen_527_; lean_object* v_traceState_528_; lean_object* v_recordedDeps_529_; lean_object* v_messages_530_; lean_object* v_infoState_531_; lean_object* v_snapshotTasks_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_561_; 
v___x_523_ = lean_st_ref_take(v___y_521_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
v_nextMacroScope_525_ = lean_ctor_get(v___x_523_, 1);
v_ngen_526_ = lean_ctor_get(v___x_523_, 2);
v_auxDeclNGen_527_ = lean_ctor_get(v___x_523_, 3);
v_traceState_528_ = lean_ctor_get(v___x_523_, 4);
v_recordedDeps_529_ = lean_ctor_get(v___x_523_, 6);
v_messages_530_ = lean_ctor_get(v___x_523_, 7);
v_infoState_531_ = lean_ctor_get(v___x_523_, 8);
v_snapshotTasks_532_ = lean_ctor_get(v___x_523_, 9);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v___x_523_, 5);
lean_dec(v_unused_562_);
v___x_534_ = v___x_523_;
v_isShared_535_ = v_isSharedCheck_561_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snapshotTasks_532_);
lean_inc(v_infoState_531_);
lean_inc(v_messages_530_);
lean_inc(v_recordedDeps_529_);
lean_inc(v_traceState_528_);
lean_inc(v_auxDeclNGen_527_);
lean_inc(v_ngen_526_);
lean_inc(v_nextMacroScope_525_);
lean_inc(v_env_524_);
lean_dec(v___x_523_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_561_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_536_ = 0;
v___x_537_ = lean_box(0);
v___x_538_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_524_, v_declName_518_, v_s_519_, v___x_536_, v___x_537_);
v___x_539_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 5, v___x_539_);
lean_ctor_set(v___x_534_, 0, v___x_538_);
v___x_541_ = v___x_534_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_nextMacroScope_525_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_ngen_526_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_auxDeclNGen_527_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_traceState_528_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_560_, 6, v_recordedDeps_529_);
lean_ctor_set(v_reuseFailAlloc_560_, 7, v_messages_530_);
lean_ctor_set(v_reuseFailAlloc_560_, 8, v_infoState_531_);
lean_ctor_set(v_reuseFailAlloc_560_, 9, v_snapshotTasks_532_);
v___x_541_ = v_reuseFailAlloc_560_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_mctx_544_; lean_object* v_zetaDeltaFVarIds_545_; lean_object* v_postponed_546_; lean_object* v_diag_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_558_; 
v___x_542_ = lean_st_ref_put(v___y_521_, v___x_541_);
v___x_543_ = lean_st_ref_take(v___y_520_);
v_mctx_544_ = lean_ctor_get(v___x_543_, 0);
v_zetaDeltaFVarIds_545_ = lean_ctor_get(v___x_543_, 2);
v_postponed_546_ = lean_ctor_get(v___x_543_, 3);
v_diag_547_ = lean_ctor_get(v___x_543_, 4);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_543_, 1);
lean_dec(v_unused_559_);
v___x_549_ = v___x_543_;
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_diag_547_);
lean_inc(v_postponed_546_);
lean_inc(v_zetaDeltaFVarIds_545_);
lean_inc(v_mctx_544_);
lean_dec(v___x_543_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = lean_box(0);
v___x_552_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_mctx_544_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_zetaDeltaFVarIds_545_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_postponed_546_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_diag_547_);
v___x_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_st_ref_put(v___y_520_, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_551_);
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_563_, lean_object* v_s_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v_s_boxed_568_; lean_object* v_res_569_; 
v_s_boxed_568_ = lean_unbox(v_s_564_);
v_res_569_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_563_, v_s_boxed_568_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec(v___y_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v___x_578_; lean_object* v___x_579_; 
v___x_578_ = 2;
v___x_579_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_570_, v___x_578_, v___y_574_, v___y_576_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_588_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_601_, lean_object* v_as_602_, size_t v_i_603_, size_t v_stop_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_603_, v_stop_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v_name_607_; lean_object* v___x_608_; uint8_t v___x_609_; uint8_t v___x_610_; uint8_t v___y_612_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_606_ = lean_array_uget_borrowed(v_as_602_, v_i_603_);
v_name_607_ = lean_ctor_get(v___x_606_, 0);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_nat_dec_lt(v___x_608_, v___x_601_);
v___x_610_ = 1;
v___x_616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_617_ = lean_name_eq(v_name_607_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_619_ = lean_name_eq(v_name_607_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_621_ = lean_name_eq(v_name_607_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_623_ = lean_name_eq(v_name_607_, v___x_622_);
v___y_612_ = v___x_623_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___x_609_;
goto v___jp_611_;
}
}
else
{
v___y_612_ = v___x_609_;
goto v___jp_611_;
}
}
else
{
v___y_612_ = v___x_609_;
goto v___jp_611_;
}
v___jp_611_:
{
if (v___y_612_ == 0)
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_603_, v___x_613_);
v_i_603_ = v___x_614_;
goto _start;
}
else
{
return v___x_610_;
}
}
}
else
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_625_, lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_){
_start:
{
size_t v_i_boxed_629_; size_t v_stop_boxed_630_; uint8_t v_res_631_; lean_object* v_r_632_; 
v_i_boxed_629_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_630_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_625_, v_as_626_, v_i_boxed_629_, v_stop_boxed_630_);
lean_dec_ref(v_as_626_);
lean_dec(v___x_625_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_a_645_; uint8_t v___x_649_; 
v___x_649_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_b_636_);
return v___x_650_;
}
else
{
lean_object* v_a_651_; uint8_t v_kind_652_; lean_object* v_modifiers_653_; lean_object* v___x_654_; uint8_t v___x_658_; 
v_a_651_ = lean_array_uget_borrowed(v_as_633_, v_i_635_);
v_kind_652_ = lean_ctor_get_uint8(v_a_651_, sizeof(void*)*9);
v_modifiers_653_ = lean_ctor_get(v_a_651_, 2);
v___x_654_ = lean_box(0);
v___x_658_ = l_Lean_Elab_DefKind_isTheorem(v_kind_652_);
if (v___x_658_ == 0)
{
lean_object* v_attrs_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_attrs_659_ = lean_ctor_get(v_modifiers_653_, 2);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_attrs_659_);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
goto v___jp_655_;
}
else
{
if (v___x_662_ == 0)
{
goto v___jp_655_;
}
else
{
size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_661_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_661_, v_attrs_659_, v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
goto v___jp_655_;
}
else
{
v_a_645_ = v___x_654_;
goto v___jp_644_;
}
}
}
}
else
{
v_a_645_ = v___x_654_;
goto v___jp_644_;
}
v___jp_655_:
{
lean_object* v_declName_656_; lean_object* v___x_657_; 
v_declName_656_ = lean_ctor_get(v_a_651_, 3);
lean_inc(v_declName_656_);
v___x_657_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_656_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref_known(v___x_657_, 1);
v_a_645_ = v___x_654_;
goto v___jp_644_;
}
else
{
return v___x_657_;
}
}
}
v___jp_644_:
{
size_t v___x_646_; size_t v___x_647_; 
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_635_, v___x_646_);
v_i_635_ = v___x_647_;
v_b_636_ = v_a_645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_666_, lean_object* v_sz_667_, lean_object* v_i_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v_i_boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_678_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_666_, v_sz_boxed_677_, v_i_boxed_678_, v_b_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v_as_666_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_box(0);
v_sz_689_ = lean_array_size(v_preDefs_680_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_680_, v_sz_689_, v___x_690_, v___x_688_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; 
lean_dec_ref_known(v___x_691_, 1);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_680_, v_sz_689_, v___x_690_, v___x_688_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; size_t v_sz_694_; lean_object* v___x_695_; 
lean_dec_ref_known(v___x_692_, 1);
lean_inc_ref(v_preDefs_680_);
v___x_693_ = l_Array_reverse___redArg(v_preDefs_680_);
v_sz_694_ = lean_array_size(v___x_693_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_693_, v_sz_694_, v___x_690_, v___x_688_, v_a_685_, v_a_686_);
lean_dec_ref(v___x_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; 
lean_dec_ref_known(v___x_695_, 1);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_680_, v_sz_689_, v___x_690_, v___x_688_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec_ref(v_preDefs_680_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_704_);
v___x_698_ = v___x_696_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_696_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_688_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_688_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
return v___x_696_;
}
}
else
{
lean_dec_ref(v_preDefs_680_);
return v___x_695_;
}
}
else
{
lean_dec_ref(v_preDefs_680_);
return v___x_692_;
}
}
else
{
lean_dec_ref(v_preDefs_680_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_714_, uint8_t v_s_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_714_, v_s_715_, v___y_719_, v___y_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_724_, lean_object* v_s_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_s_boxed_733_; lean_object* v_res_734_; 
v_s_boxed_733_ = lean_unbox(v_s_725_);
v_res_734_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_724_, v_s_boxed_733_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_735_, size_t v_sz_736_, size_t v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_735_, v_sz_736_, v_i_737_, v_b_738_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_747_, lean_object* v_sz_748_, lean_object* v_i_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
size_t v_sz_boxed_758_; size_t v_i_boxed_759_; lean_object* v_res_760_; 
v_sz_boxed_758_ = lean_unbox_usize(v_sz_748_);
lean_dec(v_sz_748_);
v_i_boxed_759_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_747_, v_sz_boxed_758_, v_i_boxed_759_, v_b_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v_as_747_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_761_, size_t v_sz_762_, size_t v_i_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_761_, v_sz_762_, v_i_763_, v_b_764_, v___y_769_, v___y_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_773_, lean_object* v_sz_774_, lean_object* v_i_775_, lean_object* v_b_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
size_t v_sz_boxed_784_; size_t v_i_boxed_785_; lean_object* v_res_786_; 
v_sz_boxed_784_ = lean_unbox_usize(v_sz_774_);
lean_dec(v_sz_774_);
v_i_boxed_785_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_773_, v_sz_boxed_784_, v_i_boxed_785_, v_b_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec_ref(v_as_773_);
return v_res_786_;
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
