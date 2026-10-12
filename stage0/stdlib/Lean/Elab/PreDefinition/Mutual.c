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
uint8_t l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(lean_object* v_attr_15_){
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
LEAN_EXPORT void l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_15_ = stack[0].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(v_attr_15_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(lean_object* v_attr_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(v_attr_22_);
lean_dec_ref(v_attr_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object* v_docCtx_25_, uint8_t v___x_26_, lean_object* v_declNames_27_, uint8_t v_cacheProofs_28_, lean_object* v_as_29_, size_t v_i_30_, size_t v_stop_31_, lean_object* v_b_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = lean_usize_dec_eq(v_i_30_, v_stop_31_);
if (v___x_40_ == 0)
{
uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = 1;
v___x_42_ = lean_array_uget_borrowed(v_as_29_, v_i_30_);
lean_inc(v_declNames_27_);
lean_inc(v___x_42_);
lean_inc_ref(v_docCtx_25_);
v___x_43_ = l_Lean_Elab_addNonRec(v_docCtx_25_, v___x_42_, v___x_26_, v_declNames_27_, v_cacheProofs_28_, v___x_26_, v___x_41_, v___x_41_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; size_t v___x_45_; size_t v___x_46_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_44_);
lean_dec_ref_known(v___x_43_, 1);
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_30_, v___x_45_);
v_i_30_ = v___x_46_;
v_b_32_ = v_a_44_;
goto _start;
}
else
{
lean_dec(v_declNames_27_);
lean_dec_ref(v_docCtx_25_);
return v___x_43_;
}
}
else
{
lean_object* v___x_48_; 
lean_dec(v_declNames_27_);
lean_dec_ref(v_docCtx_25_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v_b_32_);
return v___x_48_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_docCtx_25_ = stack[0].m_obj;
uint8_t v___x_26_ = stack[1].m_num;
lean_object* v_declNames_27_ = stack[2].m_obj;
uint8_t v_cacheProofs_28_ = stack[3].m_num;
lean_object* v_as_29_ = stack[4].m_obj;
size_t v_i_30_ = stack[5].m_num;
size_t v_stop_31_ = stack[6].m_num;
lean_object* v_b_32_ = stack[7].m_obj;
lean_object* v___y_33_ = stack[8].m_obj;
lean_object* v___y_34_ = stack[9].m_obj;
lean_object* v___y_35_ = stack[10].m_obj;
lean_object* v___y_36_ = stack[11].m_obj;
lean_object* v___y_37_ = stack[12].m_obj;
lean_object* v___y_38_ = stack[13].m_obj;
lean_object* v_res_49_;
v_res_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_25_, v___x_26_, v_declNames_27_, v_cacheProofs_28_, v_as_29_, v_i_30_, v_stop_31_, v_b_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object* v_docCtx_50_, lean_object* v___x_51_, lean_object* v_declNames_52_, lean_object* v_cacheProofs_53_, lean_object* v_as_54_, lean_object* v_i_55_, lean_object* v_stop_56_, lean_object* v_b_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
uint8_t v___x_4570__boxed_65_; uint8_t v_cacheProofs_boxed_66_; size_t v_i_boxed_67_; size_t v_stop_boxed_68_; lean_object* v_res_69_; 
v___x_4570__boxed_65_ = lean_unbox(v___x_51_);
v_cacheProofs_boxed_66_ = lean_unbox(v_cacheProofs_53_);
v_i_boxed_67_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_56_);
lean_dec(v_stop_56_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_50_, v___x_4570__boxed_65_, v_declNames_52_, v_cacheProofs_boxed_66_, v_as_54_, v_i_boxed_67_, v_stop_boxed_68_, v_b_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec_ref(v_as_54_);
return v_res_69_;
}
}
lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(uint8_t v_flag_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; lean_object* v_infoState_74_; lean_object* v_env_75_; lean_object* v_nextMacroScope_76_; lean_object* v_ngen_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_traceState_79_; lean_object* v_cache_80_; lean_object* v_recordedDeps_81_; lean_object* v_messages_82_; lean_object* v_snapshotTasks_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_103_; 
v___x_73_ = lean_st_ref_take(v___y_71_);
v_infoState_74_ = lean_ctor_get(v___x_73_, 8);
v_env_75_ = lean_ctor_get(v___x_73_, 0);
v_nextMacroScope_76_ = lean_ctor_get(v___x_73_, 1);
v_ngen_77_ = lean_ctor_get(v___x_73_, 2);
v_auxDeclNGen_78_ = lean_ctor_get(v___x_73_, 3);
v_traceState_79_ = lean_ctor_get(v___x_73_, 4);
v_cache_80_ = lean_ctor_get(v___x_73_, 5);
v_recordedDeps_81_ = lean_ctor_get(v___x_73_, 6);
v_messages_82_ = lean_ctor_get(v___x_73_, 7);
v_snapshotTasks_83_ = lean_ctor_get(v___x_73_, 9);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_103_ == 0)
{
v___x_85_ = v___x_73_;
v_isShared_86_ = v_isSharedCheck_103_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snapshotTasks_83_);
lean_inc(v_infoState_74_);
lean_inc(v_messages_82_);
lean_inc(v_recordedDeps_81_);
lean_inc(v_cache_80_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_78_);
lean_inc(v_ngen_77_);
lean_inc(v_nextMacroScope_76_);
lean_inc(v_env_75_);
lean_dec(v___x_73_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_103_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v_assignment_87_; lean_object* v_lazyAssignment_88_; lean_object* v_trees_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_102_; 
v_assignment_87_ = lean_ctor_get(v_infoState_74_, 0);
v_lazyAssignment_88_ = lean_ctor_get(v_infoState_74_, 1);
v_trees_89_ = lean_ctor_get(v_infoState_74_, 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_infoState_74_);
if (v_isSharedCheck_102_ == 0)
{
v___x_91_ = v_infoState_74_;
v_isShared_92_ = v_isSharedCheck_102_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_trees_89_);
lean_inc(v_lazyAssignment_88_);
lean_inc(v_assignment_87_);
lean_dec(v_infoState_74_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_102_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
if (v_isShared_92_ == 0)
{
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_assignment_87_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_lazyAssignment_88_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_trees_89_);
v___x_95_ = v_reuseFailAlloc_101_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_97_; 
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*3, v_flag_70_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 8, v___x_95_);
v___x_97_ = v___x_85_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_env_75_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_nextMacroScope_76_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_ngen_77_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v_traceState_79_);
lean_ctor_set(v_reuseFailAlloc_100_, 5, v_cache_80_);
lean_ctor_set(v_reuseFailAlloc_100_, 6, v_recordedDeps_81_);
lean_ctor_set(v_reuseFailAlloc_100_, 7, v_messages_82_);
lean_ctor_set(v_reuseFailAlloc_100_, 8, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_100_, 9, v_snapshotTasks_83_);
v___x_97_ = v_reuseFailAlloc_100_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_st_ref_put(v___y_71_, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_93_);
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_70_ = stack[0].m_num;
lean_object* v___y_71_ = stack[1].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_70_, v___y_71_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg___boxed(lean_object* v_flag_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
uint8_t v_flag_boxed_108_; lean_object* v_res_109_; 
v_flag_boxed_108_ = lean_unbox(v_flag_105_);
v_res_109_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_boxed_108_, v___y_106_);
lean_dec(v___y_106_);
return v_res_109_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(uint8_t v_flag_110_, lean_object* v_x_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; lean_object* v_infoState_120_; uint8_t v_enabled_121_; lean_object* v_a_123_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_119_ = lean_st_ref_get(v___y_117_);
v_infoState_120_ = lean_ctor_get(v___x_119_, 8);
lean_inc_ref(v_infoState_120_);
lean_dec(v___x_119_);
v_enabled_121_ = lean_ctor_get_uint8(v_infoState_120_, sizeof(void*)*3);
lean_dec_ref(v_infoState_120_);
v___x_133_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_110_, v___y_117_);
lean_dec_ref(v___x_133_);
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
v___x_134_ = lean_apply_7(v_x_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, lean_box(0));
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_136_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_enabled_121_, v___y_117_);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_136_, 0);
lean_dec(v_unused_144_);
v___x_138_ = v___x_136_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_dec(v___x_136_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v_a_135_);
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_135_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_145_; 
v_a_145_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_145_);
lean_dec_ref_known(v___x_134_, 1);
v_a_123_ = v_a_145_;
goto v___jp_122_;
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v___x_124_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_enabled_121_, v___y_117_);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_132_);
v___x_126_ = v___x_124_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_dec(v___x_124_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v_a_123_);
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_123_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_110_ = stack[0].m_num;
lean_object* v_x_111_ = stack[1].m_obj;
lean_object* v___y_112_ = stack[2].m_obj;
lean_object* v___y_113_ = stack[3].m_obj;
lean_object* v___y_114_ = stack[4].m_obj;
lean_object* v___y_115_ = stack[5].m_obj;
lean_object* v___y_116_ = stack[6].m_obj;
lean_object* v___y_117_ = stack[7].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_110_, v_x_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg___boxed(lean_object* v_flag_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_flag_boxed_156_; lean_object* v_res_157_; 
v_flag_boxed_156_ = lean_unbox(v_flag_147_);
v_res_157_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_boxed_156_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
if (lean_obj_tag(v_a_158_) == 0)
{
lean_object* v___x_160_; 
v___x_160_ = l_List_reverse___redArg(v_a_159_);
return v___x_160_;
}
else
{
lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_171_; 
v_head_161_ = lean_ctor_get(v_a_158_, 0);
v_tail_162_ = lean_ctor_get(v_a_158_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_158_);
if (v_isSharedCheck_171_ == 0)
{
v___x_164_ = v_a_158_;
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_tail_162_);
lean_inc(v_head_161_);
lean_dec(v_a_158_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_declName_166_; lean_object* v___x_168_; 
v_declName_166_ = lean_ctor_get(v_head_161_, 3);
lean_inc(v_declName_166_);
lean_dec(v_head_161_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_a_159_);
lean_ctor_set(v___x_164_, 0, v_declName_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_declName_166_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_a_159_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_a_158_ = v_tail_162_;
v_a_159_ = v___x_168_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(lean_object* v_o_175_, lean_object* v_k_176_, uint8_t v_v_177_){
_start:
{
lean_object* v_map_178_; uint8_t v_hasTrace_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_193_; 
v_map_178_ = lean_ctor_get(v_o_175_, 0);
v_hasTrace_179_ = lean_ctor_get_uint8(v_o_175_, sizeof(void*)*1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_o_175_);
if (v_isSharedCheck_193_ == 0)
{
v___x_181_ = v_o_175_;
v_isShared_182_ = v_isSharedCheck_193_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_map_178_);
lean_dec(v_o_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_193_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_183_, 0, v_v_177_);
lean_inc(v_k_176_);
v___x_184_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_176_, v___x_183_, v_map_178_);
if (v_hasTrace_179_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; lean_object* v___x_188_; 
v___x_185_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___closed__1));
v___x_186_ = l_Lean_Name_isPrefixOf(v___x_185_, v_k_176_);
lean_dec(v_k_176_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_184_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*1, v___x_186_);
return v___x_188_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v_k_176_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_191_ = v___x_181_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_192_, sizeof(void*)*1, v_hasTrace_179_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_175_ = stack[0].m_obj;
lean_object* v_k_176_ = stack[1].m_obj;
uint8_t v_v_177_ = stack[2].m_num;
lean_object* v_res_194_;
v_res_194_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_o_175_, v_k_176_, v_v_177_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5___boxed(lean_object* v_o_195_, lean_object* v_k_196_, lean_object* v_v_197_){
_start:
{
uint8_t v_v_boxed_198_; lean_object* v_res_199_; 
v_v_boxed_198_ = lean_unbox(v_v_197_);
v_res_199_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_o_195_, v_k_196_, v_v_boxed_198_);
return v_res_199_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_opts_200_, lean_object* v_opt_201_, uint8_t v_val_202_){
_start:
{
lean_object* v_name_203_; lean_object* v___x_204_; 
v_name_203_ = lean_ctor_get(v_opt_201_, 0);
lean_inc(v_name_203_);
lean_dec_ref(v_opt_201_);
v___x_204_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_spec__5(v_opts_200_, v_name_203_, v_val_202_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_200_ = stack[0].m_obj;
lean_object* v_opt_201_ = stack[1].m_obj;
uint8_t v_val_202_ = stack[2].m_num;
lean_object* v_res_205_;
v_res_205_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_opts_200_, v_opt_201_, v_val_202_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_opts_206_, lean_object* v_opt_207_, lean_object* v_val_208_){
_start:
{
uint8_t v_val_boxed_209_; lean_object* v_res_210_; 
v_val_boxed_209_ = lean_unbox(v_val_208_);
v_res_210_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_opts_206_, v_opt_207_, v_val_boxed_209_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__1);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
}
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object* v_docCtx_217_, lean_object* v_preDefs_218_, lean_object* v_preDefsNonrec_219_, lean_object* v_unaryPreDefNonRec_220_, uint8_t v_cacheProofs_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_declName_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_toCold_233_; lean_object* v_declName_234_; lean_object* v_currRecDepth_235_; lean_object* v_ref_236_; uint8_t v_suppressElabErrors_237_; uint8_t v_isRecordingDeps_238_; lean_object* v_fileName_239_; lean_object* v_fileMap_240_; lean_object* v_options_241_; lean_object* v_currNamespace_242_; lean_object* v_openDecls_243_; lean_object* v_initHeartbeats_244_; lean_object* v_maxHeartbeats_245_; lean_object* v_quotContext_246_; lean_object* v_currMacroScope_247_; lean_object* v_cancelTk_x3f_248_; lean_object* v_inheritedTraceOptions_249_; lean_object* v___f_250_; lean_object* v_preDefNonRec_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_declNames_254_; uint8_t v___x_255_; lean_object* v___y_257_; uint16_t v___y_258_; lean_object* v_fileName_259_; lean_object* v_fileMap_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; lean_object* v_cancelTk_x3f_267_; lean_object* v_inheritedTraceOptions_268_; lean_object* v_currRecDepth_269_; lean_object* v_ref_270_; uint8_t v_suppressElabErrors_271_; uint8_t v_isRecordingDeps_272_; lean_object* v___y_273_; lean_object* v___y_314_; uint16_t v___y_315_; uint8_t v___y_316_; lean_object* v___y_339_; 
v_declName_229_ = lean_ctor_get(v_unaryPreDefNonRec_220_, 3);
lean_inc(v_declName_229_);
v___x_230_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_array_get_borrowed(v___x_230_, v_preDefs_218_, v___x_231_);
v_toCold_233_ = lean_ctor_get(v_a_226_, 0);
v_declName_234_ = lean_ctor_get(v___x_232_, 3);
lean_inc(v_declName_234_);
v_currRecDepth_235_ = lean_ctor_get(v_a_226_, 1);
v_ref_236_ = lean_ctor_get(v_a_226_, 2);
v_suppressElabErrors_237_ = lean_ctor_get_uint8(v_a_226_, sizeof(void*)*3 + 2);
v_isRecordingDeps_238_ = lean_ctor_get_uint8(v_a_226_, sizeof(void*)*3 + 3);
v_fileName_239_ = lean_ctor_get(v_toCold_233_, 0);
v_fileMap_240_ = lean_ctor_get(v_toCold_233_, 1);
v_options_241_ = lean_ctor_get(v_toCold_233_, 2);
v_currNamespace_242_ = lean_ctor_get(v_toCold_233_, 4);
v_openDecls_243_ = lean_ctor_get(v_toCold_233_, 5);
v_initHeartbeats_244_ = lean_ctor_get(v_toCold_233_, 6);
v_maxHeartbeats_245_ = lean_ctor_get(v_toCold_233_, 7);
v_quotContext_246_ = lean_ctor_get(v_toCold_233_, 8);
v_currMacroScope_247_ = lean_ctor_get(v_toCold_233_, 9);
v_cancelTk_x3f_248_ = lean_ctor_get(v_toCold_233_, 10);
v_inheritedTraceOptions_249_ = lean_ctor_get(v_toCold_233_, 11);
v___f_250_ = ((lean_object*)(l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__0));
v_preDefNonRec_251_ = l_Lean_Elab_PreDefinition_filterAttrs(v_unaryPreDefNonRec_220_, v___f_250_);
v___x_252_ = lean_array_to_list(v_preDefs_218_);
v___x_253_ = lean_box(0);
v_declNames_254_ = l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(v___x_252_, v___x_253_);
v___x_255_ = lean_name_eq(v_declName_229_, v_declName_234_);
lean_dec(v_declName_234_);
lean_dec(v_declName_229_);
if (v_isRecordingDeps_238_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_allowUnsafeReducibility;
v___x_351_ = 1;
lean_inc_ref(v_options_241_);
v___x_352_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_options_241_, v___x_350_, v___x_351_);
v___y_339_ = v___x_352_;
goto v___jp_338_;
}
else
{
lean_object* v___x_353_; 
lean_inc_ref(v_options_241_);
v___x_353_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_241_);
v___y_339_ = v___x_353_;
goto v___jp_338_;
}
v___jp_256_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = l_Lean_maxRecDepth;
v___x_275_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v___y_257_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_276_, 0, v_fileName_259_);
lean_ctor_set(v___x_276_, 1, v_fileMap_260_);
lean_ctor_set(v___x_276_, 2, v___y_257_);
lean_ctor_set(v___x_276_, 3, v___x_275_);
lean_ctor_set(v___x_276_, 4, v_currNamespace_261_);
lean_ctor_set(v___x_276_, 5, v_openDecls_262_);
lean_ctor_set(v___x_276_, 6, v_initHeartbeats_263_);
lean_ctor_set(v___x_276_, 7, v_maxHeartbeats_264_);
lean_ctor_set(v___x_276_, 8, v_quotContext_265_);
lean_ctor_set(v___x_276_, 9, v_currMacroScope_266_);
lean_ctor_set(v___x_276_, 10, v_cancelTk_x3f_267_);
lean_ctor_set(v___x_276_, 11, v_inheritedTraceOptions_268_);
lean_inc(v_ref_270_);
lean_inc(v_currRecDepth_269_);
v___x_277_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_currRecDepth_269_);
lean_ctor_set(v___x_277_, 2, v_ref_270_);
lean_ctor_set_uint16(v___x_277_, sizeof(void*)*3, v___y_258_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*3 + 2, v_suppressElabErrors_271_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*3 + 3, v_isRecordingDeps_272_);
if (v___x_255_ == 0)
{
lean_object* v_declName_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_declName_278_ = lean_ctor_get(v_preDefNonRec_251_, 3);
lean_inc(v_declName_278_);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v_declName_278_);
lean_ctor_set(v___x_279_, 1, v___x_253_);
v___x_280_ = 1;
v___x_281_ = lean_box(v___x_255_);
v___x_282_ = lean_box(v_cacheProofs_221_);
v___x_283_ = lean_box(v___x_255_);
v___x_284_ = lean_box(v___x_280_);
v___x_285_ = lean_box(v___x_280_);
lean_inc_ref(v_docCtx_217_);
v___x_286_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 15, 8);
lean_closure_set(v___x_286_, 0, v_docCtx_217_);
lean_closure_set(v___x_286_, 1, v_preDefNonRec_251_);
lean_closure_set(v___x_286_, 2, v___x_281_);
lean_closure_set(v___x_286_, 3, v___x_279_);
lean_closure_set(v___x_286_, 4, v___x_282_);
lean_closure_set(v___x_286_, 5, v___x_283_);
lean_closure_set(v___x_286_, 6, v___x_284_);
lean_closure_set(v___x_286_, 7, v___x_285_);
v___x_287_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v___x_255_, v___x_286_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v___x_277_, v___y_273_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_307_; 
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_308_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_307_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_307_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = lean_array_get_size(v_preDefsNonrec_219_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_nat_dec_lt(v___x_231_, v___x_291_);
if (v___x_293_ == 0)
{
lean_object* v___x_295_; 
lean_dec_ref_known(v___x_277_, 3);
lean_dec(v_declNames_254_);
lean_dec_ref(v_docCtx_217_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_295_ = v___x_289_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_292_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
uint8_t v___x_297_; 
v___x_297_ = lean_nat_dec_le(v___x_291_, v___x_291_);
if (v___x_297_ == 0)
{
if (v___x_293_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref_known(v___x_277_, 3);
lean_dec(v_declNames_254_);
lean_dec_ref(v_docCtx_217_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_299_ = v___x_289_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_292_);
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
size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
lean_del_object(v___x_289_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = lean_usize_of_nat(v___x_291_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_217_, v___x_255_, v_declNames_254_, v_cacheProofs_221_, v_preDefsNonrec_219_, v___x_301_, v___x_302_, v___x_292_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v___x_277_, v___y_273_);
lean_dec_ref_known(v___x_277_, 3);
return v___x_303_;
}
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
lean_del_object(v___x_289_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_291_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_docCtx_217_, v___x_255_, v_declNames_254_, v_cacheProofs_221_, v_preDefsNonrec_219_, v___x_304_, v___x_305_, v___x_292_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v___x_277_, v___y_273_);
lean_dec_ref_known(v___x_277_, 3);
return v___x_306_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_277_, 3);
lean_dec(v_declNames_254_);
lean_dec_ref(v_docCtx_217_);
return v___x_287_;
}
}
else
{
lean_object* v_declName_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_declNames_254_);
v_declName_309_ = lean_ctor_get(v_preDefNonRec_251_, 3);
v___x_310_ = 0;
lean_inc(v_declName_309_);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v_declName_309_);
lean_ctor_set(v___x_311_, 1, v___x_253_);
v___x_312_ = l_Lean_Elab_addNonRec(v_docCtx_217_, v_preDefNonRec_251_, v___x_310_, v___x_311_, v_cacheProofs_221_, v___x_310_, v___x_255_, v___x_255_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v___x_277_, v___y_273_);
lean_dec_ref_known(v___x_277_, 3);
return v___x_312_;
}
}
v___jp_313_:
{
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v_nextMacroScope_319_; lean_object* v_ngen_320_; lean_object* v_auxDeclNGen_321_; lean_object* v_traceState_322_; lean_object* v_recordedDeps_323_; lean_object* v_messages_324_; lean_object* v_infoState_325_; lean_object* v_snapshotTasks_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_336_; 
v___x_317_ = lean_st_ref_take(v_a_227_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
v_nextMacroScope_319_ = lean_ctor_get(v___x_317_, 1);
v_ngen_320_ = lean_ctor_get(v___x_317_, 2);
v_auxDeclNGen_321_ = lean_ctor_get(v___x_317_, 3);
v_traceState_322_ = lean_ctor_get(v___x_317_, 4);
v_recordedDeps_323_ = lean_ctor_get(v___x_317_, 6);
v_messages_324_ = lean_ctor_get(v___x_317_, 7);
v_infoState_325_ = lean_ctor_get(v___x_317_, 8);
v_snapshotTasks_326_ = lean_ctor_get(v___x_317_, 9);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_317_, 5);
lean_dec(v_unused_337_);
v___x_328_ = v___x_317_;
v_isShared_329_ = v_isSharedCheck_336_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snapshotTasks_326_);
lean_inc(v_infoState_325_);
lean_inc(v_messages_324_);
lean_inc(v_recordedDeps_323_);
lean_inc(v_traceState_322_);
lean_inc(v_auxDeclNGen_321_);
lean_inc(v_ngen_320_);
lean_inc(v_nextMacroScope_319_);
lean_inc(v_env_318_);
lean_dec(v___x_317_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_336_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = l_Lean_Kernel_enableDiag(v_env_318_, v___y_316_);
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
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_nextMacroScope_319_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_ngen_320_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_auxDeclNGen_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_traceState_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 5, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_335_, 6, v_recordedDeps_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 7, v_messages_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 8, v_infoState_325_);
lean_ctor_set(v_reuseFailAlloc_335_, 9, v_snapshotTasks_326_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_st_ref_put(v_a_227_, v___x_333_);
lean_inc_ref(v_inheritedTraceOptions_249_);
lean_inc(v_cancelTk_x3f_248_);
lean_inc(v_currMacroScope_247_);
lean_inc(v_quotContext_246_);
lean_inc(v_maxHeartbeats_245_);
lean_inc(v_initHeartbeats_244_);
lean_inc(v_openDecls_243_);
lean_inc(v_currNamespace_242_);
lean_inc_ref(v_fileMap_240_);
lean_inc_ref(v_fileName_239_);
v___y_257_ = v___y_314_;
v___y_258_ = v___y_315_;
v_fileName_259_ = v_fileName_239_;
v_fileMap_260_ = v_fileMap_240_;
v_currNamespace_261_ = v_currNamespace_242_;
v_openDecls_262_ = v_openDecls_243_;
v_initHeartbeats_263_ = v_initHeartbeats_244_;
v_maxHeartbeats_264_ = v_maxHeartbeats_245_;
v_quotContext_265_ = v_quotContext_246_;
v_currMacroScope_266_ = v_currMacroScope_247_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_248_;
v_inheritedTraceOptions_268_ = v_inheritedTraceOptions_249_;
v_currRecDepth_269_ = v_currRecDepth_235_;
v_ref_270_ = v_ref_236_;
v_suppressElabErrors_271_ = v_suppressElabErrors_237_;
v_isRecordingDeps_272_ = v_isRecordingDeps_238_;
v___y_273_ = v_a_227_;
goto v___jp_256_;
}
}
}
v___jp_338_:
{
uint16_t v___x_340_; lean_object* v___x_341_; lean_object* v_env_342_; uint8_t v___x_343_; uint16_t v___x_344_; uint16_t v___x_345_; uint16_t v___x_346_; uint8_t v___x_347_; 
v___x_340_ = l_Lean_OptionFlags_ofOptions(v___y_339_);
v___x_341_ = lean_st_ref_get(v_a_227_);
v_env_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_env_342_);
lean_dec(v___x_341_);
v___x_343_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_342_);
lean_dec_ref(v_env_342_);
v___x_344_ = 512;
v___x_345_ = lean_uint16_land(v___x_340_, v___x_344_);
v___x_346_ = 0;
v___x_347_ = lean_uint16_dec_eq(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
if (v___x_343_ == 0)
{
uint8_t v___x_348_; 
v___x_348_ = 1;
v___y_314_ = v___y_339_;
v___y_315_ = v___x_340_;
v___y_316_ = v___x_348_;
goto v___jp_313_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_249_);
lean_inc(v_cancelTk_x3f_248_);
lean_inc(v_currMacroScope_247_);
lean_inc(v_quotContext_246_);
lean_inc(v_maxHeartbeats_245_);
lean_inc(v_initHeartbeats_244_);
lean_inc(v_openDecls_243_);
lean_inc(v_currNamespace_242_);
lean_inc_ref(v_fileMap_240_);
lean_inc_ref(v_fileName_239_);
v___y_257_ = v___y_339_;
v___y_258_ = v___x_340_;
v_fileName_259_ = v_fileName_239_;
v_fileMap_260_ = v_fileMap_240_;
v_currNamespace_261_ = v_currNamespace_242_;
v_openDecls_262_ = v_openDecls_243_;
v_initHeartbeats_263_ = v_initHeartbeats_244_;
v_maxHeartbeats_264_ = v_maxHeartbeats_245_;
v_quotContext_265_ = v_quotContext_246_;
v_currMacroScope_266_ = v_currMacroScope_247_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_248_;
v_inheritedTraceOptions_268_ = v_inheritedTraceOptions_249_;
v_currRecDepth_269_ = v_currRecDepth_235_;
v_ref_270_ = v_ref_236_;
v_suppressElabErrors_271_ = v_suppressElabErrors_237_;
v_isRecordingDeps_272_ = v_isRecordingDeps_238_;
v___y_273_ = v_a_227_;
goto v___jp_256_;
}
}
else
{
if (v___x_343_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_249_);
lean_inc(v_cancelTk_x3f_248_);
lean_inc(v_currMacroScope_247_);
lean_inc(v_quotContext_246_);
lean_inc(v_maxHeartbeats_245_);
lean_inc(v_initHeartbeats_244_);
lean_inc(v_openDecls_243_);
lean_inc(v_currNamespace_242_);
lean_inc_ref(v_fileMap_240_);
lean_inc_ref(v_fileName_239_);
v___y_257_ = v___y_339_;
v___y_258_ = v___x_340_;
v_fileName_259_ = v_fileName_239_;
v_fileMap_260_ = v_fileMap_240_;
v_currNamespace_261_ = v_currNamespace_242_;
v_openDecls_262_ = v_openDecls_243_;
v_initHeartbeats_263_ = v_initHeartbeats_244_;
v_maxHeartbeats_264_ = v_maxHeartbeats_245_;
v_quotContext_265_ = v_quotContext_246_;
v_currMacroScope_266_ = v_currMacroScope_247_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_248_;
v_inheritedTraceOptions_268_ = v_inheritedTraceOptions_249_;
v_currRecDepth_269_ = v_currRecDepth_235_;
v_ref_270_ = v_ref_236_;
v_suppressElabErrors_271_ = v_suppressElabErrors_237_;
v_isRecordingDeps_272_ = v_isRecordingDeps_238_;
v___y_273_ = v_a_227_;
goto v___jp_256_;
}
else
{
uint8_t v___x_349_; 
v___x_349_ = 0;
v___y_314_ = v___y_339_;
v___y_315_ = v___x_340_;
v___y_316_ = v___x_349_;
goto v___jp_313_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Mutual_addPreDefsFromUnary_0interp(lean_interpreter_value* stack)
{
lean_object* v_docCtx_217_ = stack[0].m_obj;
lean_object* v_preDefs_218_ = stack[1].m_obj;
lean_object* v_preDefsNonrec_219_ = stack[2].m_obj;
lean_object* v_unaryPreDefNonRec_220_ = stack[3].m_obj;
uint8_t v_cacheProofs_221_ = stack[4].m_num;
lean_object* v_a_222_ = stack[5].m_obj;
lean_object* v_a_223_ = stack[6].m_obj;
lean_object* v_a_224_ = stack[7].m_obj;
lean_object* v_a_225_ = stack[8].m_obj;
lean_object* v_a_226_ = stack[9].m_obj;
lean_object* v_a_227_ = stack[10].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_217_, v_preDefs_218_, v_preDefsNonrec_219_, v_unaryPreDefNonRec_220_, v_cacheProofs_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___boxed(lean_object* v_docCtx_355_, lean_object* v_preDefs_356_, lean_object* v_preDefsNonrec_357_, lean_object* v_unaryPreDefNonRec_358_, lean_object* v_cacheProofs_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_cacheProofs_boxed_367_; lean_object* v_res_368_; 
v_cacheProofs_boxed_367_ = lean_unbox(v_cacheProofs_359_);
v_res_368_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_355_, v_preDefs_356_, v_preDefsNonrec_357_, v_unaryPreDefNonRec_358_, v_cacheProofs_boxed_367_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec_ref(v_preDefsNonrec_357_);
return v_res_368_;
}
}
lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(uint8_t v_flag_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___redArg(v_flag_369_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_369_ = stack[0].m_num;
lean_object* v___y_370_ = stack[1].m_obj;
lean_object* v___y_371_ = stack[2].m_obj;
lean_object* v___y_372_ = stack[3].m_obj;
lean_object* v___y_373_ = stack[4].m_obj;
lean_object* v___y_374_ = stack[5].m_obj;
lean_object* v___y_375_ = stack[6].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(v_flag_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2___boxed(lean_object* v_flag_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v_flag_boxed_387_; lean_object* v_res_388_; 
v_flag_boxed_387_ = lean_unbox(v_flag_379_);
v_res_388_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_spec__2(v_flag_boxed_387_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_388_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object* v_00_u03b1_389_, uint8_t v_flag_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___redArg(v_flag_390_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_390_ = stack[1].m_num;
lean_object* v_x_391_ = stack[2].m_obj;
lean_object* v___y_392_ = stack[3].m_obj;
lean_object* v___y_393_ = stack[4].m_obj;
lean_object* v___y_394_ = stack[5].m_obj;
lean_object* v___y_395_ = stack[6].m_obj;
lean_object* v___y_396_ = stack[7].m_obj;
lean_object* v___y_397_ = stack[8].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_box(0), v_flag_390_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object* v_00_u03b1_401_, lean_object* v_flag_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v_flag_boxed_411_; lean_object* v_res_412_; 
v_flag_boxed_411_ = lean_unbox(v_flag_402_);
v_res_412_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v_00_u03b1_401_, v_flag_boxed_411_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_412_;
}
}
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object* v_preDef_413_, uint8_t v_cacheProofs_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Elab_eraseRecAppSyntax(v_preDef_413_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = l_Lean_Elab_abstractNestedProofs(v_a_421_, v_cacheProofs_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
return v___x_422_;
}
else
{
return v___x_420_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Mutual_cleanPreDef_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDef_413_ = stack[0].m_obj;
uint8_t v_cacheProofs_414_ = stack[1].m_num;
lean_object* v_a_415_ = stack[2].m_obj;
lean_object* v_a_416_ = stack[3].m_obj;
lean_object* v_a_417_ = stack[4].m_obj;
lean_object* v_a_418_ = stack[5].m_obj;
lean_object* v_res_423_;
v_res_423_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_413_, v_cacheProofs_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_cleanPreDef___boxed(lean_object* v_preDef_424_, lean_object* v_cacheProofs_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
uint8_t v_cacheProofs_boxed_431_; lean_object* v_res_432_; 
v_cacheProofs_boxed_431_ = lean_unbox(v_cacheProofs_425_);
v_res_432_ = l_Lean_Elab_Mutual_cleanPreDef(v_preDef_424_, v_cacheProofs_boxed_431_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_432_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(lean_object* v_as_433_, size_t v_sz_434_, size_t v_i_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v_b_436_);
return v___x_441_;
}
else
{
lean_object* v_a_442_; lean_object* v_declName_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_442_ = lean_array_uget_borrowed(v_as_433_, v_i_435_);
v_declName_443_ = lean_ctor_get(v_a_442_, 3);
v___x_444_ = lean_box(0);
lean_inc(v_declName_443_);
v___x_445_ = l_Lean_enableRealizationsForConst(v_declName_443_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_445_) == 0)
{
size_t v___x_446_; size_t v___x_447_; 
lean_dec_ref_known(v___x_445_, 1);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_435_, v___x_446_);
v_i_435_ = v___x_447_;
v_b_436_ = v___x_444_;
goto _start;
}
else
{
return v___x_445_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_433_ = stack[0].m_obj;
size_t v_sz_434_ = stack[1].m_num;
size_t v_i_435_ = stack[2].m_num;
lean_object* v_b_436_ = stack[3].m_obj;
lean_object* v___y_437_ = stack[4].m_obj;
lean_object* v___y_438_ = stack[5].m_obj;
lean_object* v_res_449_;
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_433_, v_sz_434_, v_i_435_, v_b_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg___boxed(lean_object* v_as_450_, lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_b_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
size_t v_sz_boxed_457_; size_t v_i_boxed_458_; lean_object* v_res_459_; 
v_sz_boxed_457_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_458_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_450_, v_sz_boxed_457_, v_i_boxed_458_, v_b_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_as_450_);
return v_res_459_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(lean_object* v_as_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_462_, v_sz_461_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_b_463_);
return v___x_470_;
}
else
{
lean_object* v_a_471_; lean_object* v_declName_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_a_471_ = lean_array_uget_borrowed(v_as_460_, v_i_462_);
v_declName_472_ = lean_ctor_get(v_a_471_, 3);
v___x_473_ = lean_box(0);
lean_inc(v_declName_472_);
v___x_474_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_472_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_474_) == 0)
{
size_t v___x_475_; size_t v___x_476_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_add(v_i_462_, v___x_475_);
v_i_462_ = v___x_476_;
v_b_463_ = v___x_473_;
goto _start;
}
else
{
return v___x_474_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_460_ = stack[0].m_obj;
size_t v_sz_461_ = stack[1].m_num;
size_t v_i_462_ = stack[2].m_num;
lean_object* v_b_463_ = stack[3].m_obj;
lean_object* v___y_464_ = stack[4].m_obj;
lean_object* v___y_465_ = stack[5].m_obj;
lean_object* v___y_466_ = stack[6].m_obj;
lean_object* v___y_467_ = stack[7].m_obj;
lean_object* v_res_478_;
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_460_, v_sz_461_, v_i_462_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg___boxed(lean_object* v_as_479_, lean_object* v_sz_480_, lean_object* v_i_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_480_);
lean_dec(v_sz_480_);
v_i_boxed_489_ = lean_unbox_usize(v_i_481_);
lean_dec(v_i_481_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_479_, v_sz_boxed_488_, v_i_boxed_489_, v_b_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_as_479_);
return v_res_490_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(lean_object* v_as_491_, size_t v_sz_492_, size_t v_i_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v_b_494_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; 
v___x_504_ = lean_box(0);
v_a_505_ = lean_array_uget_borrowed(v_as_491_, v_i_493_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_506_);
lean_inc(v_a_505_);
v___x_508_ = lean_array_push(v___x_507_, v_a_505_);
v___x_509_ = 1;
v___x_510_ = l_Lean_Elab_applyAttributesOf(v___x_508_, v___x_509_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec_ref(v___x_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
size_t v___x_511_; size_t v___x_512_; 
lean_dec_ref_known(v___x_510_, 1);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_493_, v___x_511_);
v_i_493_ = v___x_512_;
v_b_494_ = v___x_504_;
goto _start;
}
else
{
return v___x_510_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_491_ = stack[0].m_obj;
size_t v_sz_492_ = stack[1].m_num;
size_t v_i_493_ = stack[2].m_num;
lean_object* v_b_494_ = stack[3].m_obj;
lean_object* v___y_495_ = stack[4].m_obj;
lean_object* v___y_496_ = stack[5].m_obj;
lean_object* v___y_497_ = stack[6].m_obj;
lean_object* v___y_498_ = stack[7].m_obj;
lean_object* v___y_499_ = stack[8].m_obj;
lean_object* v___y_500_ = stack[9].m_obj;
lean_object* v_res_514_;
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_491_, v_sz_492_, v_i_493_, v_b_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5___boxed(lean_object* v_as_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_b_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_527_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_as_515_, v_sz_boxed_526_, v_i_boxed_527_, v_b_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_as_515_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__2);
v___x_530_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_ctor_set(v___x_530_, 2, v___x_529_);
lean_ctor_set(v___x_530_, 3, v___x_529_);
lean_ctor_set(v___x_530_, 4, v___x_529_);
lean_ctor_set(v___x_530_, 5, v___x_529_);
return v___x_530_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(lean_object* v_declName_531_, uint8_t v_s_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v_env_537_; lean_object* v_nextMacroScope_538_; lean_object* v_ngen_539_; lean_object* v_auxDeclNGen_540_; lean_object* v_traceState_541_; lean_object* v_recordedDeps_542_; lean_object* v_messages_543_; lean_object* v_infoState_544_; lean_object* v_snapshotTasks_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_574_; 
v___x_536_ = lean_st_ref_take(v___y_534_);
v_env_537_ = lean_ctor_get(v___x_536_, 0);
v_nextMacroScope_538_ = lean_ctor_get(v___x_536_, 1);
v_ngen_539_ = lean_ctor_get(v___x_536_, 2);
v_auxDeclNGen_540_ = lean_ctor_get(v___x_536_, 3);
v_traceState_541_ = lean_ctor_get(v___x_536_, 4);
v_recordedDeps_542_ = lean_ctor_get(v___x_536_, 6);
v_messages_543_ = lean_ctor_get(v___x_536_, 7);
v_infoState_544_ = lean_ctor_get(v___x_536_, 8);
v_snapshotTasks_545_ = lean_ctor_get(v___x_536_, 9);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v___x_536_, 5);
lean_dec(v_unused_575_);
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_574_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snapshotTasks_545_);
lean_inc(v_infoState_544_);
lean_inc(v_messages_543_);
lean_inc(v_recordedDeps_542_);
lean_inc(v_traceState_541_);
lean_inc(v_auxDeclNGen_540_);
lean_inc(v_ngen_539_);
lean_inc(v_nextMacroScope_538_);
lean_inc(v_env_537_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_574_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_549_ = 0;
v___x_550_ = lean_box(0);
v___x_551_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_537_, v_declName_531_, v_s_532_, v___x_549_, v___x_550_);
v___x_552_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 5, v___x_552_);
lean_ctor_set(v___x_547_, 0, v___x_551_);
v___x_554_ = v___x_547_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_nextMacroScope_538_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_ngen_539_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_auxDeclNGen_540_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_traceState_541_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_recordedDeps_542_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_messages_543_);
lean_ctor_set(v_reuseFailAlloc_573_, 8, v_infoState_544_);
lean_ctor_set(v_reuseFailAlloc_573_, 9, v_snapshotTasks_545_);
v___x_554_ = v_reuseFailAlloc_573_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_mctx_557_; lean_object* v_zetaDeltaFVarIds_558_; lean_object* v_postponed_559_; lean_object* v_diag_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_571_; 
v___x_555_ = lean_st_ref_put(v___y_534_, v___x_554_);
v___x_556_ = lean_st_ref_take(v___y_533_);
v_mctx_557_ = lean_ctor_get(v___x_556_, 0);
v_zetaDeltaFVarIds_558_ = lean_ctor_get(v___x_556_, 2);
v_postponed_559_ = lean_ctor_get(v___x_556_, 3);
v_diag_560_ = lean_ctor_get(v___x_556_, 4);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_556_, 1);
lean_dec(v_unused_572_);
v___x_562_ = v___x_556_;
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_diag_560_);
lean_inc(v_postponed_559_);
lean_inc(v_zetaDeltaFVarIds_558_);
lean_inc(v_mctx_557_);
lean_dec(v___x_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_mctx_557_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_zetaDeltaFVarIds_558_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_postponed_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_diag_560_);
v___x_567_ = v_reuseFailAlloc_570_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_st_ref_put(v___y_533_, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_564_);
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_531_ = stack[0].m_obj;
uint8_t v_s_532_ = stack[1].m_num;
lean_object* v___y_533_ = stack[2].m_obj;
lean_object* v___y_534_ = stack[3].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_531_, v_s_532_, v___y_533_, v___y_534_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_577_, lean_object* v_s_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v_s_boxed_582_; lean_object* v_res_583_; 
v_s_boxed_582_ = lean_unbox(v_s_578_);
v_res_583_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_577_, v_s_boxed_582_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
return v_res_583_;
}
}
lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_592_ = 2;
v___x_593_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_584_, v___x_592_, v___y_588_, v___y_590_);
return v___x_593_;
}
}
LEAN_EXPORT void l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_584_ = stack[0].m_obj;
lean_object* v___y_585_ = stack[1].m_obj;
lean_object* v___y_586_ = stack[2].m_obj;
lean_object* v___y_587_ = stack[3].m_obj;
lean_object* v___y_588_ = stack[4].m_obj;
lean_object* v___y_589_ = stack[5].m_obj;
lean_object* v___y_590_ = stack[6].m_obj;
lean_object* v_res_594_;
v_res_594_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_603_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_616_, lean_object* v_as_617_, size_t v_i_618_, size_t v_stop_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_eq(v_i_618_, v_stop_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v_name_622_; lean_object* v___x_623_; uint8_t v___x_624_; uint8_t v___x_625_; uint8_t v___y_627_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_621_ = lean_array_uget_borrowed(v_as_617_, v_i_618_);
v_name_622_ = lean_ctor_get(v___x_621_, 0);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_dec_lt(v___x_623_, v___x_616_);
v___x_625_ = 1;
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_632_ = lean_name_eq(v_name_622_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_634_ = lean_name_eq(v_name_622_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_636_ = lean_name_eq(v_name_622_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_638_ = lean_name_eq(v_name_622_, v___x_637_);
v___y_627_ = v___x_638_;
goto v___jp_626_;
}
else
{
v___y_627_ = v___x_624_;
goto v___jp_626_;
}
}
else
{
v___y_627_ = v___x_624_;
goto v___jp_626_;
}
}
else
{
v___y_627_ = v___x_624_;
goto v___jp_626_;
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
size_t v___x_628_; size_t v___x_629_; 
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_618_, v___x_628_);
v_i_618_ = v___x_629_;
goto _start;
}
else
{
return v___x_625_;
}
}
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_616_ = stack[0].m_obj;
lean_object* v_as_617_ = stack[1].m_obj;
size_t v_i_618_ = stack[2].m_num;
size_t v_stop_619_ = stack[3].m_num;
uint8_t v_res_640_;
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_616_, v_as_617_, v_i_618_, v_stop_619_);
stack->m_num = v_res_640_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_641_, lean_object* v_as_642_, lean_object* v_i_643_, lean_object* v_stop_644_){
_start:
{
size_t v_i_boxed_645_; size_t v_stop_boxed_646_; uint8_t v_res_647_; lean_object* v_r_648_; 
v_i_boxed_645_ = lean_unbox_usize(v_i_643_);
lean_dec(v_i_643_);
v_stop_boxed_646_ = lean_unbox_usize(v_stop_644_);
lean_dec(v_stop_644_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_641_, v_as_642_, v_i_boxed_645_, v_stop_boxed_646_);
lean_dec_ref(v_as_642_);
lean_dec(v___x_641_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_649_, size_t v_sz_650_, size_t v_i_651_, lean_object* v_b_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_a_661_; uint8_t v___x_665_; 
v___x_665_ = lean_usize_dec_lt(v_i_651_, v_sz_650_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_b_652_);
return v___x_666_;
}
else
{
lean_object* v_a_667_; uint8_t v_kind_668_; lean_object* v_modifiers_669_; lean_object* v___x_670_; uint8_t v___x_674_; 
v_a_667_ = lean_array_uget_borrowed(v_as_649_, v_i_651_);
v_kind_668_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*9);
v_modifiers_669_ = lean_ctor_get(v_a_667_, 2);
v___x_670_ = lean_box(0);
v___x_674_ = l_Lean_Elab_DefKind_isTheorem(v_kind_668_);
if (v___x_674_ == 0)
{
lean_object* v_attrs_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_attrs_675_ = lean_ctor_get(v_modifiers_669_, 2);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_array_get_size(v_attrs_675_);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
goto v___jp_671_;
}
else
{
if (v___x_678_ == 0)
{
goto v___jp_671_;
}
else
{
size_t v___x_679_; size_t v___x_680_; uint8_t v___x_681_; 
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_677_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_677_, v_attrs_675_, v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
goto v___jp_671_;
}
else
{
v_a_661_ = v___x_670_;
goto v___jp_660_;
}
}
}
}
else
{
v_a_661_ = v___x_670_;
goto v___jp_660_;
}
v___jp_671_:
{
lean_object* v_declName_672_; lean_object* v___x_673_; 
v_declName_672_ = lean_ctor_get(v_a_667_, 3);
lean_inc(v_declName_672_);
v___x_673_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_672_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_dec_ref_known(v___x_673_, 1);
v_a_661_ = v___x_670_;
goto v___jp_660_;
}
else
{
return v___x_673_;
}
}
}
v___jp_660_:
{
size_t v___x_662_; size_t v___x_663_; 
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_651_, v___x_662_);
v_i_651_ = v___x_663_;
v_b_652_ = v_a_661_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_649_ = stack[0].m_obj;
size_t v_sz_650_ = stack[1].m_num;
size_t v_i_651_ = stack[2].m_num;
lean_object* v_b_652_ = stack[3].m_obj;
lean_object* v___y_653_ = stack[4].m_obj;
lean_object* v___y_654_ = stack[5].m_obj;
lean_object* v___y_655_ = stack[6].m_obj;
lean_object* v___y_656_ = stack[7].m_obj;
lean_object* v___y_657_ = stack[8].m_obj;
lean_object* v___y_658_ = stack[9].m_obj;
lean_object* v_res_682_;
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_649_, v_sz_650_, v_i_651_, v_b_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_683_, lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
size_t v_sz_boxed_694_; size_t v_i_boxed_695_; lean_object* v_res_696_; 
v_sz_boxed_694_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_695_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_683_, v_sz_boxed_694_, v_i_boxed_695_, v_b_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v_as_683_);
return v_res_696_;
}
}
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; size_t v_sz_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_705_ = lean_box(0);
v_sz_706_ = lean_array_size(v_preDefs_697_);
v___x_707_ = ((size_t)0ULL);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_697_, v_sz_706_, v___x_707_, v___x_705_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_709_; 
lean_dec_ref_known(v___x_708_, 1);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_697_, v_sz_706_, v___x_707_, v___x_705_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; size_t v_sz_711_; lean_object* v___x_712_; 
lean_dec_ref_known(v___x_709_, 1);
lean_inc_ref(v_preDefs_697_);
v___x_710_ = l_Array_reverse___redArg(v_preDefs_697_);
v_sz_711_ = lean_array_size(v___x_710_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_710_, v_sz_711_, v___x_707_, v___x_705_, v_a_702_, v_a_703_);
lean_dec_ref(v___x_710_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; 
lean_dec_ref_known(v___x_712_, 1);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_697_, v_sz_706_, v___x_707_, v___x_705_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec_ref(v_preDefs_697_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_721_);
v___x_715_ = v___x_713_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_dec(v___x_713_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_705_);
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_705_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
else
{
return v___x_713_;
}
}
else
{
lean_dec_ref(v_preDefs_697_);
return v___x_712_;
}
}
else
{
lean_dec_ref(v_preDefs_697_);
return v___x_709_;
}
}
else
{
lean_dec_ref(v_preDefs_697_);
return v___x_708_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Mutual_addPreDefAttributes_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_697_ = stack[0].m_obj;
lean_object* v_a_698_ = stack[1].m_obj;
lean_object* v_a_699_ = stack[2].m_obj;
lean_object* v_a_700_ = stack[3].m_obj;
lean_object* v_a_701_ = stack[4].m_obj;
lean_object* v_a_702_ = stack[5].m_obj;
lean_object* v_a_703_ = stack[6].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
return v_res_731_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_732_, uint8_t v_s_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_732_, v_s_733_, v___y_737_, v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_732_ = stack[0].m_obj;
uint8_t v_s_733_ = stack[1].m_num;
lean_object* v___y_734_ = stack[2].m_obj;
lean_object* v___y_735_ = stack[3].m_obj;
lean_object* v___y_736_ = stack[4].m_obj;
lean_object* v___y_737_ = stack[5].m_obj;
lean_object* v___y_738_ = stack[6].m_obj;
lean_object* v___y_739_ = stack[7].m_obj;
lean_object* v_res_742_;
v_res_742_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_732_, v_s_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_743_, lean_object* v_s_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
uint8_t v_s_boxed_752_; lean_object* v_res_753_; 
v_s_boxed_752_ = lean_unbox(v_s_744_);
v_res_753_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_743_, v_s_boxed_752_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_753_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_754_, v_sz_755_, v_i_756_, v_b_757_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v___x_765_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_754_ = stack[0].m_obj;
size_t v_sz_755_ = stack[1].m_num;
size_t v_i_756_ = stack[2].m_num;
lean_object* v_b_757_ = stack[3].m_obj;
lean_object* v___y_758_ = stack[4].m_obj;
lean_object* v___y_759_ = stack[5].m_obj;
lean_object* v___y_760_ = stack[6].m_obj;
lean_object* v___y_761_ = stack[7].m_obj;
lean_object* v___y_762_ = stack[8].m_obj;
lean_object* v___y_763_ = stack[9].m_obj;
lean_object* v_res_766_;
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_754_, v_sz_755_, v_i_756_, v_b_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_767_, lean_object* v_sz_768_, lean_object* v_i_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_768_);
lean_dec(v_sz_768_);
v_i_boxed_779_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_767_, v_sz_boxed_778_, v_i_boxed_779_, v_b_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v_as_767_);
return v_res_780_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_781_, v_sz_782_, v_i_783_, v_b_784_, v___y_789_, v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_781_ = stack[0].m_obj;
size_t v_sz_782_ = stack[1].m_num;
size_t v_i_783_ = stack[2].m_num;
lean_object* v_b_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v___y_786_ = stack[5].m_obj;
lean_object* v___y_787_ = stack[6].m_obj;
lean_object* v___y_788_ = stack[7].m_obj;
lean_object* v___y_789_ = stack[8].m_obj;
lean_object* v___y_790_ = stack[9].m_obj;
lean_object* v_res_793_;
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_781_, v_sz_782_, v_i_783_, v_b_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_794_, lean_object* v_sz_795_, lean_object* v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_795_);
lean_dec(v_sz_795_);
v_i_boxed_806_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_794_, v_sz_boxed_805_, v_i_boxed_806_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_as_794_);
return v_res_807_;
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
