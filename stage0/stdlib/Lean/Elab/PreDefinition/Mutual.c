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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_filterAttrs(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_allowUnsafeReducibility;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v_opts_9_, v_opt_10_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(uint8_t v_flag_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v_infoState_28_; lean_object* v_env_29_; lean_object* v_nextMacroScope_30_; lean_object* v_ngen_31_; lean_object* v_auxDeclNGen_32_; lean_object* v_traceState_33_; lean_object* v_cache_34_; lean_object* v_recordedDeps_35_; lean_object* v_messages_36_; lean_object* v_snapshotTasks_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_57_; 
v___x_27_ = lean_st_ref_take(v___y_25_);
v_infoState_28_ = lean_ctor_get(v___x_27_, 8);
v_env_29_ = lean_ctor_get(v___x_27_, 0);
v_nextMacroScope_30_ = lean_ctor_get(v___x_27_, 1);
v_ngen_31_ = lean_ctor_get(v___x_27_, 2);
v_auxDeclNGen_32_ = lean_ctor_get(v___x_27_, 3);
v_traceState_33_ = lean_ctor_get(v___x_27_, 4);
v_cache_34_ = lean_ctor_get(v___x_27_, 5);
v_recordedDeps_35_ = lean_ctor_get(v___x_27_, 6);
v_messages_36_ = lean_ctor_get(v___x_27_, 7);
v_snapshotTasks_37_ = lean_ctor_get(v___x_27_, 9);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_57_ == 0)
{
v___x_39_ = v___x_27_;
v_isShared_40_ = v_isSharedCheck_57_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_snapshotTasks_37_);
lean_inc(v_infoState_28_);
lean_inc(v_messages_36_);
lean_inc(v_recordedDeps_35_);
lean_inc(v_cache_34_);
lean_inc(v_traceState_33_);
lean_inc(v_auxDeclNGen_32_);
lean_inc(v_ngen_31_);
lean_inc(v_nextMacroScope_30_);
lean_inc(v_env_29_);
lean_dec(v___x_27_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_57_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_assignment_41_; lean_object* v_lazyAssignment_42_; lean_object* v_trees_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_56_; 
v_assignment_41_ = lean_ctor_get(v_infoState_28_, 0);
v_lazyAssignment_42_ = lean_ctor_get(v_infoState_28_, 1);
v_trees_43_ = lean_ctor_get(v_infoState_28_, 2);
v_isSharedCheck_56_ = !lean_is_exclusive(v_infoState_28_);
if (v_isSharedCheck_56_ == 0)
{
v___x_45_ = v_infoState_28_;
v_isShared_46_ = v_isSharedCheck_56_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_trees_43_);
lean_inc(v_lazyAssignment_42_);
lean_inc(v_assignment_41_);
lean_dec(v_infoState_28_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_56_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_box(0);
if (v_isShared_46_ == 0)
{
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_assignment_41_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_lazyAssignment_42_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v_trees_43_);
v___x_49_ = v_reuseFailAlloc_55_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_51_; 
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*3, v_flag_24_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 8, v___x_49_);
v___x_51_ = v___x_39_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_env_29_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_nextMacroScope_30_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v_ngen_31_);
lean_ctor_set(v_reuseFailAlloc_54_, 3, v_auxDeclNGen_32_);
lean_ctor_set(v_reuseFailAlloc_54_, 4, v_traceState_33_);
lean_ctor_set(v_reuseFailAlloc_54_, 5, v_cache_34_);
lean_ctor_set(v_reuseFailAlloc_54_, 6, v_recordedDeps_35_);
lean_ctor_set(v_reuseFailAlloc_54_, 7, v_messages_36_);
lean_ctor_set(v_reuseFailAlloc_54_, 8, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_54_, 9, v_snapshotTasks_37_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_st_ref_put(v___y_25_, v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_47_);
return v___x_53_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg___boxed(lean_object* v_flag_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
uint8_t v_flag_boxed_61_; lean_object* v_res_62_; 
v_flag_boxed_61_ = lean_unbox(v_flag_58_);
v_res_62_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(v_flag_boxed_61_, v___y_59_);
lean_dec(v___y_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg(uint8_t v_flag_63_, lean_object* v_x_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v_infoState_73_; uint8_t v_enabled_74_; lean_object* v_a_76_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_72_ = lean_st_ref_get(v___y_70_);
v_infoState_73_ = lean_ctor_get(v___x_72_, 8);
lean_inc_ref(v_infoState_73_);
lean_dec(v___x_72_);
v_enabled_74_ = lean_ctor_get_uint8(v_infoState_73_, sizeof(void*)*3);
lean_dec_ref(v_infoState_73_);
v___x_86_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(v_flag_63_, v___y_70_);
lean_dec_ref(v___x_86_);
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
lean_inc(v___y_68_);
lean_inc_ref(v___y_67_);
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
v___x_87_ = lean_apply_7(v_x_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(v_enabled_74_, v___y_70_);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v___x_89_, 0);
lean_dec(v_unused_97_);
v___x_91_ = v___x_89_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_dec(v___x_89_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v_a_88_);
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_88_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_98_; 
v_a_98_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_87_, 1);
v_a_76_ = v_a_98_;
goto v___jp_75_;
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v___x_77_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(v_enabled_74_, v___y_70_);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v___x_77_, 0);
lean_dec(v_unused_85_);
v___x_79_ = v___x_77_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_dec(v___x_77_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 1);
lean_ctor_set(v___x_79_, 0, v_a_76_);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_76_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg___boxed(lean_object* v_flag_99_, lean_object* v_x_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
uint8_t v_flag_boxed_108_; lean_object* v_res_109_; 
v_flag_boxed_108_ = lean_unbox(v_flag_99_);
v_res_109_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg(v_flag_boxed_108_, v_x_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(lean_object* v_docCtx_110_, uint8_t v___x_111_, lean_object* v_declNames_112_, uint8_t v_cacheProofs_113_, lean_object* v_as_114_, size_t v_i_115_, size_t v_stop_116_, lean_object* v_b_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_eq(v_i_115_, v_stop_116_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = 1;
v___x_127_ = lean_array_uget_borrowed(v_as_114_, v_i_115_);
lean_inc(v_declNames_112_);
lean_inc(v___x_127_);
lean_inc_ref(v_docCtx_110_);
v___x_128_ = l_Lean_Elab_addNonRec(v_docCtx_110_, v___x_127_, v___x_111_, v_declNames_112_, v_cacheProofs_113_, v___x_111_, v___x_126_, v___x_126_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; size_t v___x_130_; size_t v___x_131_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_i_115_, v___x_130_);
v_i_115_ = v___x_131_;
v_b_117_ = v_a_129_;
goto _start;
}
else
{
lean_dec(v_declNames_112_);
lean_dec_ref(v_docCtx_110_);
return v___x_128_;
}
}
else
{
lean_object* v___x_133_; 
lean_dec(v_declNames_112_);
lean_dec_ref(v_docCtx_110_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_b_117_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4___boxed(lean_object* v_docCtx_134_, lean_object* v___x_135_, lean_object* v_declNames_136_, lean_object* v_cacheProofs_137_, lean_object* v_as_138_, lean_object* v_i_139_, lean_object* v_stop_140_, lean_object* v_b_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v___x_4581__boxed_149_; uint8_t v_cacheProofs_boxed_150_; size_t v_i_boxed_151_; size_t v_stop_boxed_152_; lean_object* v_res_153_; 
v___x_4581__boxed_149_ = lean_unbox(v___x_135_);
v_cacheProofs_boxed_150_ = lean_unbox(v_cacheProofs_137_);
v_i_boxed_151_ = lean_unbox_usize(v_i_139_);
lean_dec(v_i_139_);
v_stop_boxed_152_ = lean_unbox_usize(v_stop_140_);
lean_dec(v_stop_140_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_docCtx_134_, v___x_4581__boxed_149_, v_declNames_136_, v_cacheProofs_boxed_150_, v_as_138_, v_i_boxed_151_, v_stop_boxed_152_, v_b_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_as_138_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(lean_object* v_o_171_, lean_object* v_k_172_, uint8_t v_v_173_){
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
v___x_181_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1___boxed(lean_object* v_o_190_, lean_object* v_k_191_, lean_object* v_v_192_){
_start:
{
uint8_t v_v_boxed_193_; lean_object* v_res_194_; 
v_v_boxed_193_ = lean_unbox(v_v_192_);
v_res_194_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_o_190_, v_k_191_, v_v_boxed_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(lean_object* v_opts_195_, lean_object* v_opt_196_, uint8_t v_val_197_){
_start:
{
lean_object* v_name_198_; lean_object* v___x_199_; 
v_name_198_ = lean_ctor_get(v_opt_196_, 0);
lean_inc(v_name_198_);
lean_dec_ref(v_opt_196_);
v___x_199_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1_spec__1(v_opts_195_, v_name_198_, v_val_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1___boxed(lean_object* v_opts_200_, lean_object* v_opt_201_, lean_object* v_val_202_){
_start:
{
uint8_t v_val_boxed_203_; lean_object* v_res_204_; 
v_val_boxed_203_ = lean_unbox(v_val_202_);
v_res_204_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_opts_200_, v_opt_201_, v_val_boxed_203_);
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
lean_object* v_declName_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_toCold_227_; lean_object* v_declName_228_; lean_object* v_currRecDepth_229_; lean_object* v_ref_230_; uint8_t v_suppressElabErrors_231_; uint8_t v_isRecordingDeps_232_; lean_object* v_fileName_233_; lean_object* v_fileMap_234_; lean_object* v_options_235_; lean_object* v_currNamespace_236_; lean_object* v_openDecls_237_; lean_object* v_initHeartbeats_238_; lean_object* v_maxHeartbeats_239_; lean_object* v_quotContext_240_; lean_object* v_currMacroScope_241_; lean_object* v_cancelTk_x3f_242_; lean_object* v_inheritedTraceOptions_243_; lean_object* v___f_244_; lean_object* v_preDefNonRec_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_declNames_248_; uint8_t v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; uint16_t v___x_253_; lean_object* v_fileName_255_; lean_object* v_fileMap_256_; lean_object* v_currNamespace_257_; lean_object* v_openDecls_258_; lean_object* v_initHeartbeats_259_; lean_object* v_maxHeartbeats_260_; lean_object* v_quotContext_261_; lean_object* v_currMacroScope_262_; lean_object* v_cancelTk_x3f_263_; lean_object* v_inheritedTraceOptions_264_; lean_object* v_currRecDepth_265_; lean_object* v_ref_266_; uint8_t v_suppressElabErrors_267_; uint8_t v_isRecordingDeps_268_; lean_object* v___y_269_; lean_object* v___x_308_; uint8_t v___y_310_; lean_object* v_env_332_; uint8_t v___x_333_; uint16_t v___x_334_; uint16_t v___x_335_; uint16_t v___x_336_; uint8_t v___x_337_; 
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
v___x_250_ = l_Lean_allowUnsafeReducibility;
v___x_251_ = 1;
lean_inc_ref(v_options_235_);
v___x_252_ = l_Lean_Option_set___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__1(v_options_235_, v___x_250_, v___x_251_);
v___x_253_ = l_Lean_OptionFlags_ofOptions(v___x_252_);
v___x_308_ = lean_st_ref_get(v_a_221_);
v_env_332_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_env_332_);
lean_dec(v___x_308_);
v___x_333_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_332_);
lean_dec_ref(v_env_332_);
v___x_334_ = 512;
v___x_335_ = lean_uint16_land(v___x_253_, v___x_334_);
v___x_336_ = 0;
v___x_337_ = lean_uint16_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
if (v___x_333_ == 0)
{
v___y_310_ = v___x_251_;
goto v___jp_309_;
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
v_fileName_255_ = v_fileName_233_;
v_fileMap_256_ = v_fileMap_234_;
v_currNamespace_257_ = v_currNamespace_236_;
v_openDecls_258_ = v_openDecls_237_;
v_initHeartbeats_259_ = v_initHeartbeats_238_;
v_maxHeartbeats_260_ = v_maxHeartbeats_239_;
v_quotContext_261_ = v_quotContext_240_;
v_currMacroScope_262_ = v_currMacroScope_241_;
v_cancelTk_x3f_263_ = v_cancelTk_x3f_242_;
v_inheritedTraceOptions_264_ = v_inheritedTraceOptions_243_;
v_currRecDepth_265_ = v_currRecDepth_229_;
v_ref_266_ = v_ref_230_;
v_suppressElabErrors_267_ = v_suppressElabErrors_231_;
v_isRecordingDeps_268_ = v_isRecordingDeps_232_;
v___y_269_ = v_a_221_;
goto v___jp_254_;
}
}
else
{
if (v___x_333_ == 0)
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
v_fileName_255_ = v_fileName_233_;
v_fileMap_256_ = v_fileMap_234_;
v_currNamespace_257_ = v_currNamespace_236_;
v_openDecls_258_ = v_openDecls_237_;
v_initHeartbeats_259_ = v_initHeartbeats_238_;
v_maxHeartbeats_260_ = v_maxHeartbeats_239_;
v_quotContext_261_ = v_quotContext_240_;
v_currMacroScope_262_ = v_currMacroScope_241_;
v_cancelTk_x3f_263_ = v_cancelTk_x3f_242_;
v_inheritedTraceOptions_264_ = v_inheritedTraceOptions_243_;
v_currRecDepth_265_ = v_currRecDepth_229_;
v_ref_266_ = v_ref_230_;
v_suppressElabErrors_267_ = v_suppressElabErrors_231_;
v_isRecordingDeps_268_ = v_isRecordingDeps_232_;
v___y_269_ = v_a_221_;
goto v___jp_254_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
v___y_310_ = v___x_338_;
goto v___jp_309_;
}
}
v___jp_254_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = l_Lean_maxRecDepth;
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__2(v___x_252_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_272_, 0, v_fileName_255_);
lean_ctor_set(v___x_272_, 1, v_fileMap_256_);
lean_ctor_set(v___x_272_, 2, v___x_252_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
lean_ctor_set(v___x_272_, 4, v_currNamespace_257_);
lean_ctor_set(v___x_272_, 5, v_openDecls_258_);
lean_ctor_set(v___x_272_, 6, v_initHeartbeats_259_);
lean_ctor_set(v___x_272_, 7, v_maxHeartbeats_260_);
lean_ctor_set(v___x_272_, 8, v_quotContext_261_);
lean_ctor_set(v___x_272_, 9, v_currMacroScope_262_);
lean_ctor_set(v___x_272_, 10, v_cancelTk_x3f_263_);
lean_ctor_set(v___x_272_, 11, v_inheritedTraceOptions_264_);
lean_inc(v_ref_266_);
lean_inc(v_currRecDepth_265_);
v___x_273_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_currRecDepth_265_);
lean_ctor_set(v___x_273_, 2, v_ref_266_);
lean_ctor_set_uint16(v___x_273_, sizeof(void*)*3, v___x_253_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 2, v_suppressElabErrors_267_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 3, v_isRecordingDeps_268_);
if (v___x_249_ == 0)
{
lean_object* v_declName_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_declName_274_ = lean_ctor_get(v_preDefNonRec_245_, 3);
lean_inc(v_declName_274_);
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v_declName_274_);
lean_ctor_set(v___x_275_, 1, v___x_247_);
v___x_276_ = lean_box(v___x_249_);
v___x_277_ = lean_box(v_cacheProofs_215_);
v___x_278_ = lean_box(v___x_249_);
v___x_279_ = lean_box(v___x_251_);
v___x_280_ = lean_box(v___x_251_);
lean_inc_ref(v_docCtx_211_);
v___x_281_ = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 15, 8);
lean_closure_set(v___x_281_, 0, v_docCtx_211_);
lean_closure_set(v___x_281_, 1, v_preDefNonRec_245_);
lean_closure_set(v___x_281_, 2, v___x_276_);
lean_closure_set(v___x_281_, 3, v___x_275_);
lean_closure_set(v___x_281_, 4, v___x_277_);
lean_closure_set(v___x_281_, 5, v___x_278_);
lean_closure_set(v___x_281_, 6, v___x_279_);
lean_closure_set(v___x_281_, 7, v___x_280_);
v___x_282_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg(v___x_249_, v___x_281_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_302_; 
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v___x_282_, 0);
lean_dec(v_unused_303_);
v___x_284_ = v___x_282_;
v_isShared_285_ = v_isSharedCheck_302_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___x_282_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_302_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_array_get_size(v_preDefsNonrec_213_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_nat_dec_lt(v___x_225_, v___x_286_);
if (v___x_288_ == 0)
{
lean_object* v___x_290_; 
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_248_);
lean_dec_ref(v_docCtx_211_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_290_ = v___x_284_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_287_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
else
{
uint8_t v___x_292_; 
v___x_292_ = lean_nat_dec_le(v___x_286_, v___x_286_);
if (v___x_292_ == 0)
{
if (v___x_288_ == 0)
{
lean_object* v___x_294_; 
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_248_);
lean_dec_ref(v_docCtx_211_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_287_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
lean_del_object(v___x_284_);
v___x_296_ = ((size_t)0ULL);
v___x_297_ = lean_usize_of_nat(v___x_286_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_docCtx_211_, v___x_249_, v_declNames_248_, v_cacheProofs_215_, v_preDefsNonrec_213_, v___x_296_, v___x_297_, v___x_287_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_298_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
lean_del_object(v___x_284_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_286_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__4(v_docCtx_211_, v___x_249_, v_declNames_248_, v_cacheProofs_215_, v_preDefsNonrec_213_, v___x_299_, v___x_300_, v___x_287_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_301_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v_declNames_248_);
lean_dec_ref(v_docCtx_211_);
return v___x_282_;
}
}
else
{
lean_object* v_declName_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_declNames_248_);
v_declName_304_ = lean_ctor_get(v_preDefNonRec_245_, 3);
lean_inc(v_declName_304_);
v___x_305_ = 0;
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v_declName_304_);
lean_ctor_set(v___x_306_, 1, v___x_247_);
v___x_307_ = l_Lean_Elab_addNonRec(v_docCtx_211_, v_preDefNonRec_245_, v___x_305_, v___x_306_, v_cacheProofs_215_, v___x_305_, v___x_249_, v___x_249_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v___x_273_, v___y_269_);
lean_dec_ref_known(v___x_273_, 3);
return v___x_307_;
}
}
v___jp_309_:
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
v_fileName_255_ = v_fileName_233_;
v_fileMap_256_ = v_fileMap_234_;
v_currNamespace_257_ = v_currNamespace_236_;
v_openDecls_258_ = v_openDecls_237_;
v_initHeartbeats_259_ = v_initHeartbeats_238_;
v_maxHeartbeats_260_ = v_maxHeartbeats_239_;
v_quotContext_261_ = v_quotContext_240_;
v_currMacroScope_262_ = v_currMacroScope_241_;
v_cancelTk_x3f_263_ = v_cancelTk_x3f_242_;
v_inheritedTraceOptions_264_ = v_inheritedTraceOptions_243_;
v_currRecDepth_265_ = v_currRecDepth_229_;
v_ref_266_ = v_ref_230_;
v_suppressElabErrors_267_ = v_suppressElabErrors_231_;
v_isRecordingDeps_268_ = v_isRecordingDeps_232_;
v___y_269_ = v_a_221_;
goto v___jp_254_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4(uint8_t v_flag_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___redArg(v_flag_353_, v___y_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4___boxed(lean_object* v_flag_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_flag_boxed_370_; lean_object* v_res_371_; 
v_flag_boxed_370_ = lean_unbox(v_flag_362_);
v_res_371_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3_spec__4(v_flag_boxed_370_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(lean_object* v_00_u03b1_372_, uint8_t v_flag_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___redArg(v_flag_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3___boxed(lean_object* v_00_u03b1_383_, lean_object* v_flag_384_, lean_object* v_x_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
uint8_t v_flag_boxed_393_; lean_object* v_res_394_; 
v_flag_boxed_393_ = lean_unbox(v_flag_384_);
v_res_394_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Elab_Mutual_addPreDefsFromUnary_spec__3(v_00_u03b1_383_, v_flag_boxed_393_, v_x_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
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
lean_dec_ref_known(v___x_402_, 1);
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
lean_object* v_a_423_; lean_object* v_declName_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_a_423_ = lean_array_uget_borrowed(v_as_414_, v_i_416_);
v_declName_424_ = lean_ctor_get(v_a_423_, 3);
v___x_425_ = lean_box(0);
lean_inc(v_declName_424_);
v___x_426_ = l_Lean_enableRealizationsForConst(v_declName_424_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_426_) == 0)
{
size_t v___x_427_; size_t v___x_428_; 
lean_dec_ref_known(v___x_426_, 1);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_416_, v___x_427_);
v_i_416_ = v___x_428_;
v_b_417_ = v___x_425_;
goto _start;
}
else
{
return v___x_426_;
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
lean_object* v_a_451_; lean_object* v_declName_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_a_451_ = lean_array_uget_borrowed(v_as_440_, v_i_442_);
v_declName_452_ = lean_ctor_get(v_a_451_, 3);
v___x_453_ = lean_box(0);
lean_inc(v_declName_452_);
v___x_454_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_452_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_454_) == 0)
{
size_t v___x_455_; size_t v___x_456_; 
lean_dec_ref_known(v___x_454_, 1);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_442_, v___x_455_);
v_i_442_ = v___x_456_;
v_b_443_ = v___x_453_;
goto _start;
}
else
{
return v___x_454_;
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
lean_object* v___x_483_; lean_object* v_a_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_483_ = lean_box(0);
v_a_484_ = lean_array_uget_borrowed(v_as_470_, v_i_472_);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_mk_empty_array_with_capacity(v___x_485_);
lean_inc(v_a_484_);
v___x_487_ = lean_array_push(v___x_486_, v_a_484_);
v___x_488_ = 1;
v___x_489_ = l_Lean_Elab_applyAttributesOf(v___x_487_, v___x_488_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec_ref(v___x_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
size_t v___x_490_; size_t v___x_491_; 
lean_dec_ref_known(v___x_489_, 1);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_472_, v___x_490_);
v_i_472_ = v___x_491_;
v_b_473_ = v___x_483_;
goto _start;
}
else
{
return v___x_489_;
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
lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v_nextMacroScope_516_; lean_object* v_ngen_517_; lean_object* v_auxDeclNGen_518_; lean_object* v_traceState_519_; lean_object* v_recordedDeps_520_; lean_object* v_messages_521_; lean_object* v_infoState_522_; lean_object* v_snapshotTasks_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_552_; 
v___x_514_ = lean_st_ref_take(v___y_512_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
v_nextMacroScope_516_ = lean_ctor_get(v___x_514_, 1);
v_ngen_517_ = lean_ctor_get(v___x_514_, 2);
v_auxDeclNGen_518_ = lean_ctor_get(v___x_514_, 3);
v_traceState_519_ = lean_ctor_get(v___x_514_, 4);
v_recordedDeps_520_ = lean_ctor_get(v___x_514_, 6);
v_messages_521_ = lean_ctor_get(v___x_514_, 7);
v_infoState_522_ = lean_ctor_get(v___x_514_, 8);
v_snapshotTasks_523_ = lean_ctor_get(v___x_514_, 9);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v___x_514_, 5);
lean_dec(v_unused_553_);
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_552_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snapshotTasks_523_);
lean_inc(v_infoState_522_);
lean_inc(v_messages_521_);
lean_inc(v_recordedDeps_520_);
lean_inc(v_traceState_519_);
lean_inc(v_auxDeclNGen_518_);
lean_inc(v_ngen_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_env_515_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_552_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_527_ = 0;
v___x_528_ = lean_box(0);
v___x_529_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_515_, v_declName_509_, v_s_510_, v___x_527_, v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3, &l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3_once, _init_l_Lean_Elab_Mutual_addPreDefsFromUnary___closed__3);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 5, v___x_530_);
lean_ctor_set(v___x_525_, 0, v___x_529_);
v___x_532_ = v___x_525_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_ngen_517_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_auxDeclNGen_518_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_traceState_519_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_recordedDeps_520_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_messages_521_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_infoState_522_);
lean_ctor_set(v_reuseFailAlloc_551_, 9, v_snapshotTasks_523_);
v___x_532_ = v_reuseFailAlloc_551_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_mctx_535_; lean_object* v_zetaDeltaFVarIds_536_; lean_object* v_postponed_537_; lean_object* v_diag_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_549_; 
v___x_533_ = lean_st_ref_put(v___y_512_, v___x_532_);
v___x_534_ = lean_st_ref_take(v___y_511_);
v_mctx_535_ = lean_ctor_get(v___x_534_, 0);
v_zetaDeltaFVarIds_536_ = lean_ctor_get(v___x_534_, 2);
v_postponed_537_ = lean_ctor_get(v___x_534_, 3);
v_diag_538_ = lean_ctor_get(v___x_534_, 4);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_534_, 1);
lean_dec(v_unused_550_);
v___x_540_ = v___x_534_;
v_isShared_541_ = v_isSharedCheck_549_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_diag_538_);
lean_inc(v_postponed_537_);
lean_inc(v_zetaDeltaFVarIds_536_);
lean_inc(v_mctx_535_);
lean_dec(v___x_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_549_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = lean_box(0);
v___x_543_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___closed__0);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_543_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_mctx_535_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_zetaDeltaFVarIds_536_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_postponed_537_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_diag_538_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_st_ref_put(v___y_511_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_542_);
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg___boxed(lean_object* v_declName_554_, lean_object* v_s_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v_s_boxed_559_; lean_object* v_res_560_; 
v_s_boxed_559_ = lean_unbox(v_s_555_);
v_res_560_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_554_, v_s_boxed_559_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec(v___y_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(lean_object* v_declName_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v___x_569_; lean_object* v___x_570_; 
v___x_569_ = 2;
v___x_570_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_561_, v___x_569_, v___y_565_, v___y_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0___boxed(lean_object* v_declName_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_579_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(lean_object* v___x_592_, lean_object* v_as_593_, size_t v_i_594_, size_t v_stop_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = lean_usize_dec_eq(v_i_594_, v_stop_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v_name_598_; lean_object* v___x_599_; uint8_t v___x_600_; uint8_t v___x_601_; uint8_t v___y_603_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_597_ = lean_array_uget_borrowed(v_as_593_, v_i_594_);
v_name_598_ = lean_ctor_get(v___x_597_, 0);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_nat_dec_lt(v___x_599_, v___x_592_);
v___x_601_ = 1;
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__1));
v___x_608_ = lean_name_eq(v_name_598_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__3));
v___x_610_ = lean_name_eq(v_name_598_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__5));
v___x_612_ = lean_name_eq(v_name_598_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___closed__7));
v___x_614_ = lean_name_eq(v_name_598_, v___x_613_);
v___y_603_ = v___x_614_;
goto v___jp_602_;
}
else
{
v___y_603_ = v___x_600_;
goto v___jp_602_;
}
}
else
{
v___y_603_ = v___x_600_;
goto v___jp_602_;
}
}
else
{
v___y_603_ = v___x_600_;
goto v___jp_602_;
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
size_t v___x_604_; size_t v___x_605_; 
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_add(v_i_594_, v___x_604_);
v_i_594_ = v___x_605_;
goto _start;
}
else
{
return v___x_601_;
}
}
}
else
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1___boxed(lean_object* v___x_616_, lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_stop_619_){
_start:
{
size_t v_i_boxed_620_; size_t v_stop_boxed_621_; uint8_t v_res_622_; lean_object* v_r_623_; 
v_i_boxed_620_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_stop_boxed_621_ = lean_unbox_usize(v_stop_619_);
lean_dec(v_stop_619_);
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_616_, v_as_617_, v_i_boxed_620_, v_stop_boxed_621_);
lean_dec_ref(v_as_617_);
lean_dec(v___x_616_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object* v_as_624_, size_t v_sz_625_, size_t v_i_626_, lean_object* v_b_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_a_636_; uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_626_, v_sz_625_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_b_627_);
return v___x_641_;
}
else
{
lean_object* v_a_642_; uint8_t v_kind_643_; lean_object* v_modifiers_644_; lean_object* v___x_645_; uint8_t v___x_649_; 
v_a_642_ = lean_array_uget_borrowed(v_as_624_, v_i_626_);
v_kind_643_ = lean_ctor_get_uint8(v_a_642_, sizeof(void*)*9);
v_modifiers_644_ = lean_ctor_get(v_a_642_, 2);
v___x_645_ = lean_box(0);
v___x_649_ = l_Lean_Elab_DefKind_isTheorem(v_kind_643_);
if (v___x_649_ == 0)
{
lean_object* v_attrs_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_attrs_650_ = lean_ctor_get(v_modifiers_644_, 2);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_attrs_650_);
v___x_653_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
goto v___jp_646_;
}
else
{
if (v___x_653_ == 0)
{
goto v___jp_646_;
}
else
{
size_t v___x_654_; size_t v___x_655_; uint8_t v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_652_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__1(v___x_652_, v_attrs_650_, v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
goto v___jp_646_;
}
else
{
v_a_636_ = v___x_645_;
goto v___jp_635_;
}
}
}
}
else
{
v_a_636_ = v___x_645_;
goto v___jp_635_;
}
v___jp_646_:
{
lean_object* v_declName_647_; lean_object* v___x_648_; 
v_declName_647_ = lean_ctor_get(v_a_642_, 3);
lean_inc(v_declName_647_);
v___x_648_ = l_Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0(v_declName_647_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_dec_ref_known(v___x_648_, 1);
v_a_636_ = v___x_645_;
goto v___jp_635_;
}
else
{
return v___x_648_;
}
}
}
v___jp_635_:
{
size_t v___x_637_; size_t v___x_638_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_626_, v___x_637_);
v_i_626_ = v___x_638_;
v_b_627_ = v_a_636_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2___boxed(lean_object* v_as_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_b_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
size_t v_sz_boxed_668_; size_t v_i_boxed_669_; lean_object* v_res_670_; 
v_sz_boxed_668_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_669_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_as_657_, v_sz_boxed_668_, v_i_boxed_669_, v_b_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v_as_657_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object* v_preDefs_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; size_t v_sz_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(0);
v_sz_680_ = lean_array_size(v_preDefs_671_);
v___x_681_ = ((size_t)0ULL);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__2(v_preDefs_671_, v_sz_680_, v___x_681_, v___x_679_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; 
lean_dec_ref_known(v___x_682_, 1);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_preDefs_671_, v_sz_680_, v___x_681_, v___x_679_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; size_t v_sz_685_; lean_object* v___x_686_; 
lean_dec_ref_known(v___x_683_, 1);
lean_inc_ref(v_preDefs_671_);
v___x_684_ = l_Array_reverse___redArg(v_preDefs_671_);
v_sz_685_ = lean_array_size(v___x_684_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v___x_684_, v_sz_685_, v___x_681_, v___x_679_, v_a_676_, v_a_677_);
lean_dec_ref(v___x_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v___x_687_; 
lean_dec_ref_known(v___x_686_, 1);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__5(v_preDefs_671_, v_sz_680_, v___x_681_, v___x_679_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
lean_dec_ref(v_preDefs_671_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_695_);
v___x_689_ = v___x_687_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_dec(v___x_687_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_679_);
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_679_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
return v___x_687_;
}
}
else
{
lean_dec_ref(v_preDefs_671_);
return v___x_686_;
}
}
else
{
lean_dec_ref(v_preDefs_671_);
return v___x_683_;
}
}
else
{
lean_dec_ref(v_preDefs_671_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Mutual_addPreDefAttributes___boxed(lean_object* v_preDefs_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_preDefs_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(lean_object* v_declName_705_, uint8_t v_s_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___redArg(v_declName_705_, v_s_706_, v___y_710_, v___y_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0___boxed(lean_object* v_declName_715_, lean_object* v_s_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v_s_boxed_724_; lean_object* v_res_725_; 
v_s_boxed_724_ = lean_unbox(v_s_716_);
v_res_725_ = l_Lean_setReducibilityStatus___at___00Lean_setIrreducibleAttribute___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__0_spec__0(v_declName_715_, v_s_boxed_724_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(lean_object* v_as_726_, size_t v_sz_727_, size_t v_i_728_, lean_object* v_b_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___redArg(v_as_726_, v_sz_727_, v_i_728_, v_b_729_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3___boxed(lean_object* v_as_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_sz_boxed_749_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_750_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__3(v_as_738_, v_sz_boxed_749_, v_i_boxed_750_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v_as_738_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(lean_object* v_as_752_, size_t v_sz_753_, size_t v_i_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___redArg(v_as_752_, v_sz_753_, v_i_754_, v_b_755_, v___y_760_, v___y_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4___boxed(lean_object* v_as_764_, lean_object* v_sz_765_, lean_object* v_i_766_, lean_object* v_b_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v_sz_boxed_775_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_776_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Mutual_addPreDefAttributes_spec__4(v_as_764_, v_sz_boxed_775_, v_i_boxed_776_, v_b_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v_as_764_);
return v_res_777_;
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
