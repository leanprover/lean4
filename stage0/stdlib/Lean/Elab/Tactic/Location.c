// Lean compiler output
// Module: Lean.Elab.Tactic.Location
// Imports: public import Lean.Elab.Tactic.ElabTerm
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
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_wildcard_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_wildcard_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_targets_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_targets_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "locationType"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(28, 84, 76, 241, 57, 201, 89, 77)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_expandLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l_Lean_Elab_Tactic_expandLocation___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_expandLocation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* l_Lean_Elab_Tactic_expandLocation___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__1_value;
static const lean_array_object l_Lean_Elab_Tactic_expandLocation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_expandLocation___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_expandLocation___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Tactic_Location_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_hypotheses_8_; uint8_t v_type_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_hypotheses_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_hypotheses_8_);
v_type_9_ = lean_ctor_get_uint8(v_t_6_, sizeof(void*)*1);
lean_dec_ref_known(v_t_6_, 1);
v___x_10_ = lean_box(v_type_9_);
v___x_11_ = lean_apply_2(v_k_7_, v_hypotheses_8_, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Tactic_Location_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_wildcard_elim___redArg(lean_object* v_t_24_, lean_object* v_wildcard_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_24_, v_wildcard_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_wildcard_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_wildcard_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_28_, v_wildcard_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_targets_elim___redArg(lean_object* v_t_32_, lean_object* v_targets_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_32_, v_targets_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_targets_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_targets_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_36_, v_targets_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(lean_object* v_as_49_, size_t v_i_50_, size_t v_stop_51_, lean_object* v_b_52_){
_start:
{
lean_object* v___y_54_; uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_eq(v_i_50_, v_stop_51_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; uint8_t v___x_63_; 
v___x_59_ = lean_array_uget_borrowed(v_as_49_, v_i_50_);
lean_inc(v___x_59_);
v___x_60_ = l_Lean_Syntax_getKind(v___x_59_);
v___x_61_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4));
v___x_62_ = lean_name_eq(v___x_60_, v___x_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_bool_not(v___x_62_);
if (v___x_63_ == 0)
{
v___y_54_ = v_b_52_;
goto v___jp_53_;
}
else
{
lean_object* v___x_64_; 
lean_inc(v___x_59_);
v___x_64_ = lean_array_push(v_b_52_, v___x_59_);
v___y_54_ = v___x_64_;
goto v___jp_53_;
}
}
else
{
return v_b_52_;
}
v___jp_53_:
{
size_t v___x_55_; size_t v___x_56_; 
v___x_55_ = ((size_t)1ULL);
v___x_56_ = lean_usize_add(v_i_50_, v___x_55_);
v_i_50_ = v___x_56_;
v_b_52_ = v___y_54_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v_b_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; lean_object* v_res_71_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_as_65_, v_i_boxed_69_, v_stop_boxed_70_, v_b_68_);
lean_dec_ref(v_as_65_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object* v_stx_80_){
_start:
{
lean_object* v___x_81_; lean_object* v_arg_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v_arg_82_ = l_Lean_Syntax_getArg(v_stx_80_, v___x_81_);
lean_inc(v_arg_82_);
v___x_83_ = l_Lean_Syntax_getKind(v_arg_82_);
v___x_84_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__1));
v___x_85_ = lean_name_eq(v___x_83_, v___x_84_);
lean_dec(v___x_83_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_locationHyps_88_; lean_object* v___x_89_; lean_object* v___y_91_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_Lean_Syntax_getArg(v_arg_82_, v___x_86_);
lean_dec(v_arg_82_);
v_locationHyps_88_ = l_Lean_Syntax_getArgs(v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = lean_array_get_size(v_locationHyps_88_);
v___x_96_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__2));
v___x_97_ = lean_nat_dec_lt(v___x_86_, v___x_89_);
if (v___x_97_ == 0)
{
lean_dec_ref(v_locationHyps_88_);
v___y_91_ = v___x_96_;
goto v___jp_90_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = lean_nat_dec_le(v___x_89_, v___x_89_);
if (v___x_98_ == 0)
{
if (v___x_97_ == 0)
{
lean_dec_ref(v_locationHyps_88_);
v___y_91_ = v___x_96_;
goto v___jp_90_;
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_89_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_88_, v___x_99_, v___x_100_, v___x_96_);
lean_dec_ref(v_locationHyps_88_);
v___y_91_ = v___x_101_;
goto v___jp_90_;
}
}
else
{
size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((size_t)0ULL);
v___x_103_ = lean_usize_of_nat(v___x_89_);
v___x_104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_88_, v___x_102_, v___x_103_, v___x_96_);
lean_dec_ref(v_locationHyps_88_);
v___y_91_ = v___x_104_;
goto v___jp_90_;
}
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v_numTurnstiles_93_; uint8_t v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_array_get_size(v___y_91_);
v_numTurnstiles_93_ = lean_nat_sub(v___x_89_, v___x_92_);
v___x_94_ = lean_nat_dec_lt(v___x_86_, v_numTurnstiles_93_);
lean_dec(v_numTurnstiles_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_95_, 0, v___y_91_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
return v___x_95_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec(v_arg_82_);
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation___boxed(lean_object* v_stx_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Elab_Tactic_expandLocation(v_stx_106_);
lean_dec(v_stx_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object* v_stx_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = l_Lean_Syntax_isNone(v_stx_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_Lean_Syntax_getArg(v_stx_108_, v___x_110_);
v___x_112_ = l_Lean_Elab_Tactic_expandLocation(v___x_111_);
lean_dec(v___x_111_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__2));
v___x_114_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_109_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation___boxed(lean_object* v_stx_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Elab_Tactic_expandOptLocation(v_stx_115_);
lean_dec(v_stx_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(lean_object* v_x_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
v___x_127_ = lean_apply_9(v_x_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, lean_box(0));
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(v_x_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(lean_object* v_mvarId_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___f_150_; lean_object* v___x_151_; 
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v___f_150_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_150_, 0, v_x_140_);
lean_closure_set(v___f_150_, 1, v___y_141_);
lean_closure_set(v___f_150_, 2, v___y_142_);
lean_closure_set(v___f_150_, 3, v___y_143_);
lean_closure_set(v___f_150_, 4, v___y_144_);
v___x_151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_139_, v___f_150_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
return v___x_151_;
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___boxed(lean_object* v_mvarId_160_, lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_160_, v_x_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(lean_object* v_00_u03b1_172_, lean_object* v_mvarId_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_173_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___boxed(lean_object* v_00_u03b1_185_, lean_object* v_mvarId_186_, lean_object* v_x_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(v_00_u03b1_185_, v_mvarId_186_, v_x_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(lean_object* v___x_198_, lean_object* v_ctx_x3f_199_, size_t v_sz_200_, size_t v_i_201_, lean_object* v_bs_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_lt(v_i_201_, v_sz_200_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec_ref(v_ctx_x3f_199_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_bs_202_);
return v___x_213_;
}
else
{
lean_object* v_assignment_214_; lean_object* v___x_215_; 
v_assignment_214_ = lean_ctor_get(v___x_198_, 0);
lean_inc_ref(v_ctx_x3f_199_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
v___x_215_ = lean_apply_9(v_ctx_x3f_199_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, lean_box(0));
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v_v_217_; lean_object* v___x_218_; lean_object* v_bs_x27_219_; lean_object* v_a_221_; lean_object* v_tree_226_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v_v_217_ = lean_array_uget(v_bs_202_, v_i_201_);
v___x_218_ = lean_unsigned_to_nat(0u);
v_bs_x27_219_ = lean_array_uset(v_bs_202_, v_i_201_, v___x_218_);
v_tree_226_ = l_Lean_Elab_InfoTree_substitute(v_v_217_, v_assignment_214_);
if (lean_obj_tag(v_a_216_) == 0)
{
v_a_221_ = v_tree_226_;
goto v___jp_220_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; 
v_val_227_ = lean_ctor_get(v_a_216_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v_a_216_, 1);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_val_227_);
lean_ctor_set(v___x_228_, 1, v_tree_226_);
v_a_221_ = v___x_228_;
goto v___jp_220_;
}
v___jp_220_:
{
size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; 
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_201_, v___x_222_);
v___x_224_ = lean_array_uset(v_bs_x27_219_, v_i_201_, v_a_221_);
v_i_201_ = v___x_223_;
v_bs_202_ = v___x_224_;
goto _start;
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec_ref(v_bs_202_);
lean_dec_ref(v_ctx_x3f_199_);
v_a_229_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_215_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_215_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v___x_237_, lean_object* v_ctx_x3f_238_, lean_object* v_sz_239_, lean_object* v_i_240_, lean_object* v_bs_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
size_t v_sz_boxed_251_; size_t v_i_boxed_252_; lean_object* v_res_253_; 
v_sz_boxed_251_ = lean_unbox_usize(v_sz_239_);
lean_dec(v_sz_239_);
v_i_boxed_252_ = lean_unbox_usize(v_i_240_);
lean_dec(v_i_240_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_237_, v_ctx_x3f_238_, v_sz_boxed_251_, v_i_boxed_252_, v_bs_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec_ref(v___x_237_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(lean_object* v___x_254_, lean_object* v_ctx_x3f_255_, lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v_cs_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_292_; 
v_cs_266_ = lean_ctor_get(v_x_256_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_292_ == 0)
{
v___x_268_ = v_x_256_;
v_isShared_269_ = v_isSharedCheck_292_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_cs_266_);
lean_dec(v_x_256_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_292_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
size_t v_sz_270_; size_t v___x_271_; lean_object* v___x_272_; 
v_sz_270_ = lean_array_size(v_cs_266_);
v___x_271_ = ((size_t)0ULL);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_254_, v_ctx_x3f_255_, v_sz_270_, v___x_271_, v_cs_266_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_283_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_283_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_a_273_);
v___x_278_ = v___x_268_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_278_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_del_object(v___x_268_);
v_a_284_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_272_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_272_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
else
{
lean_object* v_vs_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_319_; 
v_vs_293_ = lean_ctor_get(v_x_256_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_319_ == 0)
{
v___x_295_ = v_x_256_;
v_isShared_296_ = v_isSharedCheck_319_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_vs_293_);
lean_dec(v_x_256_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_319_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
size_t v_sz_297_; size_t v___x_298_; lean_object* v___x_299_; 
v_sz_297_ = lean_array_size(v_vs_293_);
v___x_298_ = ((size_t)0ULL);
v___x_299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_254_, v_ctx_x3f_255_, v_sz_297_, v___x_298_, v_vs_293_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v_a_300_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_del_object(v___x_295_);
v_a_311_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_299_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v___x_320_, lean_object* v_ctx_x3f_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_bs_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v_ctx_x3f_321_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_bs_324_);
return v___x_335_;
}
else
{
lean_object* v_v_336_; lean_object* v___x_337_; 
v_v_336_ = lean_array_uget_borrowed(v_bs_324_, v_i_323_);
lean_inc(v_v_336_);
lean_inc_ref(v_ctx_x3f_321_);
v___x_337_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_320_, v_ctx_x3f_321_, v_v_336_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v_bs_x27_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = lean_unsigned_to_nat(0u);
v_bs_x27_340_ = lean_array_uset(v_bs_324_, v_i_323_, v___x_339_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_323_, v___x_341_);
v___x_343_ = lean_array_uset(v_bs_x27_340_, v_i_323_, v_a_338_);
v_i_323_ = v___x_342_;
v_bs_324_ = v___x_343_;
goto _start;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v_bs_324_);
lean_dec_ref(v_ctx_x3f_321_);
v_a_345_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_337_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_337_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v___x_353_, lean_object* v_ctx_x3f_354_, lean_object* v_sz_355_, lean_object* v_i_356_, lean_object* v_bs_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
size_t v_sz_boxed_367_; size_t v_i_boxed_368_; lean_object* v_res_369_; 
v_sz_boxed_367_ = lean_unbox_usize(v_sz_355_);
lean_dec(v_sz_355_);
v_i_boxed_368_ = lean_unbox_usize(v_i_356_);
lean_dec(v_i_356_);
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_353_, v_ctx_x3f_354_, v_sz_boxed_367_, v_i_boxed_368_, v_bs_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec_ref(v___x_353_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v___x_370_, lean_object* v_ctx_x3f_371_, lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_370_, v_ctx_x3f_371_, v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec_ref(v___x_370_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(lean_object* v___x_383_, lean_object* v_ctx_x3f_384_, lean_object* v_t_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_root_395_; lean_object* v_tail_396_; lean_object* v_size_397_; size_t v_shift_398_; lean_object* v_tailOff_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_435_; 
v_root_395_ = lean_ctor_get(v_t_385_, 0);
v_tail_396_ = lean_ctor_get(v_t_385_, 1);
v_size_397_ = lean_ctor_get(v_t_385_, 2);
v_shift_398_ = lean_ctor_get_usize(v_t_385_, 4);
v_tailOff_399_ = lean_ctor_get(v_t_385_, 3);
v_isSharedCheck_435_ = !lean_is_exclusive(v_t_385_);
if (v_isSharedCheck_435_ == 0)
{
v___x_401_ = v_t_385_;
v_isShared_402_ = v_isSharedCheck_435_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_tailOff_399_);
lean_inc(v_size_397_);
lean_inc(v_tail_396_);
lean_inc(v_root_395_);
lean_dec(v_t_385_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_435_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; 
lean_inc_ref(v_ctx_x3f_384_);
v___x_403_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_383_, v_ctx_x3f_384_, v_root_395_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v_sz_405_ = lean_array_size(v_tail_396_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_383_, v_ctx_x3f_384_, v_sz_405_, v___x_406_, v_tail_396_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_418_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_418_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v_a_408_);
lean_ctor_set(v___x_401_, 0, v_a_404_);
v___x_413_ = v___x_401_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_404_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_size_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_tailOff_399_);
lean_ctor_set_usize(v_reuseFailAlloc_417_, 4, v_shift_398_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_a_404_);
lean_del_object(v___x_401_);
lean_dec(v_tailOff_399_);
lean_dec(v_size_397_);
v_a_419_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_407_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_407_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_del_object(v___x_401_);
lean_dec(v_tailOff_399_);
lean_dec(v_size_397_);
lean_dec_ref(v_tail_396_);
lean_dec_ref(v_ctx_x3f_384_);
v_a_427_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_403_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_403_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5___boxed(lean_object* v___x_436_, lean_object* v_ctx_x3f_437_, lean_object* v_t_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_436_, v_ctx_x3f_437_, v_t_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v___x_436_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(lean_object* v___y_449_, lean_object* v_ctx_x3f_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v_a_458_, lean_object* v_a_x3f_459_){
_start:
{
lean_object* v___x_461_; lean_object* v_infoState_462_; lean_object* v_trees_463_; lean_object* v___x_464_; 
v___x_461_ = lean_st_ref_get(v___y_449_);
v_infoState_462_ = lean_ctor_get(v___x_461_, 7);
lean_inc_ref(v_infoState_462_);
lean_dec(v___x_461_);
v_trees_463_ = lean_ctor_get(v_infoState_462_, 2);
lean_inc_ref(v_trees_463_);
v___x_464_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_462_, v_ctx_x3f_450_, v_trees_463_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_449_);
lean_dec_ref(v_infoState_462_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_503_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_503_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_503_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_503_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v_infoState_470_; lean_object* v_env_471_; lean_object* v_nextMacroScope_472_; lean_object* v_ngen_473_; lean_object* v_auxDeclNGen_474_; lean_object* v_traceState_475_; lean_object* v_cache_476_; lean_object* v_messages_477_; lean_object* v_snapshotTasks_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_502_; 
v___x_469_ = lean_st_ref_take(v___y_449_);
v_infoState_470_ = lean_ctor_get(v___x_469_, 7);
v_env_471_ = lean_ctor_get(v___x_469_, 0);
v_nextMacroScope_472_ = lean_ctor_get(v___x_469_, 1);
v_ngen_473_ = lean_ctor_get(v___x_469_, 2);
v_auxDeclNGen_474_ = lean_ctor_get(v___x_469_, 3);
v_traceState_475_ = lean_ctor_get(v___x_469_, 4);
v_cache_476_ = lean_ctor_get(v___x_469_, 5);
v_messages_477_ = lean_ctor_get(v___x_469_, 6);
v_snapshotTasks_478_ = lean_ctor_get(v___x_469_, 8);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_502_ == 0)
{
v___x_480_ = v___x_469_;
v_isShared_481_ = v_isSharedCheck_502_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snapshotTasks_478_);
lean_inc(v_infoState_470_);
lean_inc(v_messages_477_);
lean_inc(v_cache_476_);
lean_inc(v_traceState_475_);
lean_inc(v_auxDeclNGen_474_);
lean_inc(v_ngen_473_);
lean_inc(v_nextMacroScope_472_);
lean_inc(v_env_471_);
lean_dec(v___x_469_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_502_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v_enabled_482_; lean_object* v_assignment_483_; lean_object* v_lazyAssignment_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_500_; 
v_enabled_482_ = lean_ctor_get_uint8(v_infoState_470_, sizeof(void*)*3);
v_assignment_483_ = lean_ctor_get(v_infoState_470_, 0);
v_lazyAssignment_484_ = lean_ctor_get(v_infoState_470_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_infoState_470_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v_infoState_470_, 2);
lean_dec(v_unused_501_);
v___x_486_ = v_infoState_470_;
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_lazyAssignment_484_);
lean_inc(v_assignment_483_);
lean_dec(v_infoState_470_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = l_Lean_PersistentArray_append___redArg(v_a_458_, v_a_465_);
lean_dec(v_a_465_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 2, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_assignment_483_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_lazyAssignment_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v___x_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*3, v_enabled_482_);
v___x_490_ = v_reuseFailAlloc_499_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 7, v___x_490_);
v___x_492_ = v___x_480_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_env_471_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextMacroScope_472_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_ngen_473_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_auxDeclNGen_474_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_traceState_475_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_cache_476_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_messages_477_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_snapshotTasks_478_);
v___x_492_ = v_reuseFailAlloc_498_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = lean_st_ref_set(v___y_449_, v___x_492_);
v___x_494_ = lean_box(0);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_494_);
v___x_496_ = v___x_467_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v_a_458_);
v_a_504_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_464_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_464_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_512_, lean_object* v_ctx_x3f_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v_a_521_, lean_object* v_a_x3f_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_512_, v_ctx_x3f_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v_a_521_, v_a_x3f_522_);
lean_dec(v_a_x3f_522_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_512_);
return v_res_524_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_unsigned_to_nat(32u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_528_ = ((size_t)5ULL);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_unsigned_to_nat(32u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_533_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_529_);
lean_ctor_set(v___x_533_, 3, v___x_529_);
lean_ctor_set_usize(v___x_533_, 4, v___x_528_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v_infoState_537_; lean_object* v_trees_538_; lean_object* v___x_539_; lean_object* v_infoState_540_; lean_object* v_env_541_; lean_object* v_nextMacroScope_542_; lean_object* v_ngen_543_; lean_object* v_auxDeclNGen_544_; lean_object* v_traceState_545_; lean_object* v_cache_546_; lean_object* v_messages_547_; lean_object* v_snapshotTasks_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_569_; 
v___x_536_ = lean_st_ref_get(v___y_534_);
v_infoState_537_ = lean_ctor_get(v___x_536_, 7);
lean_inc_ref(v_infoState_537_);
lean_dec(v___x_536_);
v_trees_538_ = lean_ctor_get(v_infoState_537_, 2);
lean_inc_ref(v_trees_538_);
lean_dec_ref(v_infoState_537_);
v___x_539_ = lean_st_ref_take(v___y_534_);
v_infoState_540_ = lean_ctor_get(v___x_539_, 7);
v_env_541_ = lean_ctor_get(v___x_539_, 0);
v_nextMacroScope_542_ = lean_ctor_get(v___x_539_, 1);
v_ngen_543_ = lean_ctor_get(v___x_539_, 2);
v_auxDeclNGen_544_ = lean_ctor_get(v___x_539_, 3);
v_traceState_545_ = lean_ctor_get(v___x_539_, 4);
v_cache_546_ = lean_ctor_get(v___x_539_, 5);
v_messages_547_ = lean_ctor_get(v___x_539_, 6);
v_snapshotTasks_548_ = lean_ctor_get(v___x_539_, 8);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_569_ == 0)
{
v___x_550_ = v___x_539_;
v_isShared_551_ = v_isSharedCheck_569_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snapshotTasks_548_);
lean_inc(v_infoState_540_);
lean_inc(v_messages_547_);
lean_inc(v_cache_546_);
lean_inc(v_traceState_545_);
lean_inc(v_auxDeclNGen_544_);
lean_inc(v_ngen_543_);
lean_inc(v_nextMacroScope_542_);
lean_inc(v_env_541_);
lean_dec(v___x_539_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_569_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
uint8_t v_enabled_552_; lean_object* v_assignment_553_; lean_object* v_lazyAssignment_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_567_; 
v_enabled_552_ = lean_ctor_get_uint8(v_infoState_540_, sizeof(void*)*3);
v_assignment_553_ = lean_ctor_get(v_infoState_540_, 0);
v_lazyAssignment_554_ = lean_ctor_get(v_infoState_540_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_infoState_540_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_infoState_540_, 2);
lean_dec(v_unused_568_);
v___x_556_ = v_infoState_540_;
v_isShared_557_ = v_isSharedCheck_567_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_lazyAssignment_554_);
lean_inc(v_assignment_553_);
lean_dec(v_infoState_540_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_567_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 2, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_assignment_553_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_lazyAssignment_554_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v___x_558_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3, v_enabled_552_);
v___x_560_ = v_reuseFailAlloc_566_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 7, v___x_560_);
v___x_562_ = v___x_550_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_env_541_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_nextMacroScope_542_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_ngen_543_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_auxDeclNGen_544_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_traceState_545_);
lean_ctor_set(v_reuseFailAlloc_565_, 5, v_cache_546_);
lean_ctor_set(v_reuseFailAlloc_565_, 6, v_messages_547_);
lean_ctor_set(v_reuseFailAlloc_565_, 7, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_565_, 8, v_snapshotTasks_548_);
v___x_562_ = v_reuseFailAlloc_565_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_st_ref_set(v___y_534_, v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v_trees_538_);
return v___x_564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_570_);
lean_dec(v___y_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(lean_object* v_x_573_, lean_object* v_ctx_x3f_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v_infoState_585_; uint8_t v_enabled_586_; uint8_t v___x_587_; 
v___x_584_ = lean_st_ref_get(v___y_582_);
v_infoState_585_ = lean_ctor_get(v___x_584_, 7);
lean_inc_ref(v_infoState_585_);
lean_dec(v___x_584_);
v_enabled_586_ = lean_ctor_get_uint8(v_infoState_585_, sizeof(void*)*3);
lean_dec_ref(v_infoState_585_);
v___x_587_ = lean_bool_not(v_enabled_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v_a_589_; lean_object* v_r_590_; 
v___x_588_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_582_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
v_r_590_ = lean_apply_9(v_x_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, lean_box(0));
if (lean_obj_tag(v_r_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_615_; 
v_a_591_ = lean_ctor_get(v_r_590_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_r_590_);
if (v_isSharedCheck_615_ == 0)
{
v___x_593_ = v_r_590_;
v_isShared_594_ = v_isSharedCheck_615_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v_r_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_615_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
lean_inc(v_a_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 1);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_614_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_582_, v_ctx_x3f_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v_a_589_, v___x_596_);
lean_dec_ref(v___x_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_605_);
v___x_599_ = v___x_597_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___x_597_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_a_591_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_591_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_591_);
v_a_606_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_597_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_597_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_616_ = lean_ctor_get(v_r_590_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v_r_590_, 1);
v___x_617_ = lean_box(0);
v___x_618_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_582_, v_ctx_x3f_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v_a_589_, v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_618_, 0);
lean_dec(v_unused_626_);
v___x_620_ = v___x_618_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_618_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 1);
lean_ctor_set(v___x_620_, 0, v_a_616_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_616_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_616_);
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_ctx_x3f_574_);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
v___x_635_ = lean_apply_9(v_x_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, lean_box(0));
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___boxed(lean_object* v_x_636_, lean_object* v_ctx_x3f_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_636_, v_ctx_x3f_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_env_653_; lean_object* v___x_654_; lean_object* v_mctx_655_; lean_object* v_options_656_; lean_object* v_currNamespace_657_; lean_object* v_openDecls_658_; lean_object* v___x_659_; lean_object* v_ngen_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_652_ = lean_st_ref_get(v___y_650_);
v_env_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc_ref(v_env_653_);
lean_dec(v___x_652_);
v___x_654_ = lean_st_ref_get(v___y_648_);
v_mctx_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_mctx_655_);
lean_dec(v___x_654_);
v_options_656_ = lean_ctor_get(v___y_649_, 2);
v_currNamespace_657_ = lean_ctor_get(v___y_649_, 6);
v_openDecls_658_ = lean_ctor_get(v___y_649_, 7);
v___x_659_ = lean_st_ref_get(v___y_650_);
v_ngen_660_ = lean_ctor_get(v___x_659_, 2);
lean_inc_ref(v_ngen_660_);
lean_dec(v___x_659_);
v___x_661_ = lean_box(0);
v___x_662_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_658_);
lean_inc(v_currNamespace_657_);
lean_inc_ref(v_options_656_);
v___x_663_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_663_, 0, v_env_653_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
lean_ctor_set(v___x_663_, 3, v_mctx_655_);
lean_ctor_set(v___x_663_, 4, v_options_656_);
lean_ctor_set(v___x_663_, 5, v_currNamespace_657_);
lean_ctor_set(v___x_663_, 6, v_openDecls_658_);
lean_ctor_set(v___x_663_, 7, v_ngen_660_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_704_; 
v___x_679_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_675_, v___y_676_, v___y_677_);
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_704_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_704_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_704_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_fileMap_684_; lean_object* v_env_685_; lean_object* v_mctx_686_; lean_object* v_options_687_; lean_object* v_currNamespace_688_; lean_object* v_openDecls_689_; lean_object* v_ngen_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_701_; 
v_fileMap_684_ = lean_ctor_get(v___y_676_, 1);
v_env_685_ = lean_ctor_get(v_a_680_, 0);
v_mctx_686_ = lean_ctor_get(v_a_680_, 3);
v_options_687_ = lean_ctor_get(v_a_680_, 4);
v_currNamespace_688_ = lean_ctor_get(v_a_680_, 5);
v_openDecls_689_ = lean_ctor_get(v_a_680_, 6);
v_ngen_690_ = lean_ctor_get(v_a_680_, 7);
v_isSharedCheck_701_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; lean_object* v_unused_703_; 
v_unused_702_ = lean_ctor_get(v_a_680_, 2);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_a_680_, 1);
lean_dec(v_unused_703_);
v___x_692_ = v_a_680_;
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_ngen_690_);
lean_inc(v_openDecls_689_);
lean_inc(v_currNamespace_688_);
lean_inc(v_options_687_);
lean_inc(v_mctx_686_);
lean_inc(v_env_685_);
lean_dec(v_a_680_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_box(0);
lean_inc_ref(v_fileMap_684_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 2, v_fileMap_684_);
lean_ctor_set(v___x_692_, 1, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_env_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_fileMap_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_mctx_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_options_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_currNamespace_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_openDecls_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_ngen_690_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_696_);
v___x_698_ = v___x_682_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0___boxed(lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
v___x_724_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_a_725_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed(lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; 
v___f_756_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0));
v___x_757_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_746_, v___f_756_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(lean_object* v_00_u03b1_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed(lean_object* v_00_u03b1_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(v_00_u03b1_781_, v_x_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(lean_object* v_atLocal_793_, lean_object* v_as_794_, size_t v_sz_795_, size_t v_i_796_, uint8_t v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
uint8_t v_a_808_; uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_lt(v_i_796_, v_sz_795_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec_ref(v_atLocal_793_);
v___x_813_ = lean_box(v_b_797_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_815_ = lean_array_uget_borrowed(v_as_794_, v_i_796_);
lean_inc(v_a_815_);
v___x_816_ = l_Lean_FVarId_getDecl___redArg(v_a_815_, v___y_802_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; uint8_t v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = l_Lean_LocalDecl_isImplementationDetail(v_a_817_);
lean_dec(v_a_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_inc_ref(v_atLocal_793_);
lean_inc(v_a_815_);
v___x_819_ = lean_apply_1(v_atLocal_793_, v_a_815_);
v___x_820_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_820_, 0, lean_box(0));
lean_closure_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_821_, 0, lean_box(0));
lean_closure_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_821_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_822_) == 0)
{
if (v_b_797_ == 0)
{
lean_object* v_a_823_; uint8_t v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_unbox(v_a_823_);
lean_dec(v_a_823_);
v_a_808_ = v___x_824_;
goto v___jp_807_;
}
else
{
lean_dec_ref_known(v___x_822_, 1);
v_a_808_ = v_b_797_;
goto v___jp_807_;
}
}
else
{
lean_dec_ref(v_atLocal_793_);
return v___x_822_;
}
}
else
{
v_a_808_ = v_b_797_;
goto v___jp_807_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_atLocal_793_);
v_a_825_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_816_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_816_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
v___jp_807_:
{
size_t v___x_809_; size_t v___x_810_; 
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_i_796_, v___x_809_);
v_i_796_ = v___x_810_;
v_b_797_ = v_a_808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1___boxed(lean_object* v_atLocal_833_, lean_object* v_as_834_, lean_object* v_sz_835_, lean_object* v_i_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; uint8_t v_b_boxed_849_; lean_object* v_res_850_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_835_);
lean_dec(v_sz_835_);
v_i_boxed_848_ = lean_unbox_usize(v_i_836_);
lean_dec(v_i_836_);
v_b_boxed_849_ = lean_unbox(v_b_837_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_833_, v_as_834_, v_sz_boxed_847_, v_i_boxed_848_, v_b_boxed_849_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v_as_834_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0(lean_object* v_atLocal_851_, uint8_t v_a_852_, lean_object* v_failed_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_lctx_863_; lean_object* v___x_864_; lean_object* v___x_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; 
v_lctx_863_ = lean_ctor_get(v___y_858_, 2);
v___x_864_ = l_Lean_LocalContext_getFVarIds(v_lctx_863_);
v___x_865_ = l_Array_reverse___redArg(v___x_864_);
v_sz_866_ = lean_array_size(v___x_865_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_851_, v___x_865_, v_sz_866_, v___x_867_, v_a_852_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec_ref(v___x_865_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_889_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_889_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_889_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_889_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_del_object(v___x_871_);
v___x_874_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_855_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = lean_apply_10(v_failed_853_, v_a_875_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, lean_box(0));
return v___x_876_;
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_failed_853_);
v_a_877_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_874_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_failed_853_);
v___x_885_ = lean_box(0);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_885_);
v___x_887_ = v___x_871_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_failed_853_);
v_a_890_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_868_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_868_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0___boxed(lean_object* v_atLocal_898_, lean_object* v_a_899_, lean_object* v_failed_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v_a_17061__boxed_910_; lean_object* v_res_911_; 
v_a_17061__boxed_910_ = lean_unbox(v_a_899_);
v_res_911_ = l_Lean_Elab_Tactic_withLocation___lam__0(v_atLocal_898_, v_a_17061__boxed_910_, v_failed_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(lean_object* v___x_912_, lean_object* v_atLocal_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Elab_Tactic_getFVarId(v___x_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_925_ = lean_apply_10(v_atLocal_913_, v_a_924_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_925_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_atLocal_913_);
v_a_926_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_923_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_923_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed(lean_object* v___x_934_, lean_object* v_atLocal_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_934_, v_atLocal_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(lean_object* v_atLocal_946_, lean_object* v_as_947_, size_t v_i_948_, size_t v_stop_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = lean_usize_dec_eq(v_i_948_, v_stop_949_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___f_962_; lean_object* v___x_963_; 
v___x_961_ = lean_array_uget_borrowed(v_as_947_, v_i_948_);
lean_inc_ref(v_atLocal_946_);
lean_inc(v___x_961_);
v___f_962_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed), 11, 2);
lean_closure_set(v___f_962_, 0, v___x_961_);
lean_closure_set(v___f_962_, 1, v_atLocal_946_);
v___x_963_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_962_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; size_t v___x_965_; size_t v___x_966_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_948_, v___x_965_);
v_i_948_ = v___x_966_;
v_b_950_ = v_a_964_;
goto _start;
}
else
{
lean_dec_ref(v_atLocal_946_);
return v___x_963_;
}
}
else
{
lean_object* v___x_968_; 
lean_dec_ref(v_atLocal_946_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v_b_950_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(lean_object* v_atLocal_969_, lean_object* v_as_970_, lean_object* v_i_971_, lean_object* v_stop_972_, lean_object* v_b_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
size_t v_i_boxed_983_; size_t v_stop_boxed_984_; lean_object* v_res_985_; 
v_i_boxed_983_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_stop_boxed_984_ = lean_unbox_usize(v_stop_972_);
lean_dec(v_stop_972_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_969_, v_as_970_, v_i_boxed_983_, v_stop_boxed_984_, v_b_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_as_970_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation(lean_object* v_loc_986_, lean_object* v_atLocal_987_, lean_object* v_atTarget_988_, lean_object* v_failed_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
if (lean_obj_tag(v_loc_986_) == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_999_, 0, lean_box(0));
lean_closure_set(v___x_999_, 1, v_atTarget_988_);
v___x_1000_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_1000_, 0, lean_box(0));
lean_closure_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_1000_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_991_, v_a_993_, v_a_995_, v_a_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_991_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; 
lean_dec(v_a_1004_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withLocation___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1007_, 0, v_atLocal_987_);
lean_closure_set(v___f_1007_, 1, v_a_1002_);
lean_closure_set(v___f_1007_, 2, v_failed_989_);
v___x_1008_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_1006_, v___f_1007_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1008_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1002_);
lean_dec_ref(v_failed_989_);
lean_dec_ref(v_atLocal_987_);
v_a_1009_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1011_ = v___x_1005_;
v_isShared_1012_ = v_isSharedCheck_1030_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1005_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1030_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
uint8_t v___y_1014_; uint8_t v___x_1028_; 
v___x_1028_ = l_Lean_Exception_isInterrupt(v_a_1009_);
if (v___x_1028_ == 0)
{
uint8_t v___x_1029_; 
lean_inc(v_a_1009_);
v___x_1029_ = l_Lean_Exception_isRuntime(v_a_1009_);
v___y_1014_ = v___x_1029_;
goto v___jp_1013_;
}
else
{
v___y_1014_ = v___x_1028_;
goto v___jp_1013_;
}
v___jp_1013_:
{
if (v___y_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_del_object(v___x_1011_);
lean_dec(v_a_1009_);
v___x_1015_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1004_, v___y_1014_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v___x_1015_, 0);
lean_dec(v_unused_1024_);
v___x_1017_ = v___x_1015_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_1015_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = lean_box(0);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1026_; 
lean_dec(v_a_1004_);
if (v_isShared_1012_ == 0)
{
v___x_1026_ = v___x_1011_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1009_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_a_1002_);
lean_dec_ref(v_failed_989_);
lean_dec_ref(v_atLocal_987_);
v_a_1031_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1003_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1003_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_failed_989_);
lean_dec_ref(v_atLocal_987_);
v_a_1039_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1001_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1001_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_hypotheses_1047_; uint8_t v_type_1048_; lean_object* v___y_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
lean_dec_ref(v_failed_989_);
v_hypotheses_1047_ = lean_ctor_get(v_loc_986_, 0);
v_type_1048_ = lean_ctor_get_uint8(v_loc_986_, sizeof(void*)*1);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_array_get_size(v_hypotheses_1047_);
v___x_1057_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_dec_ref(v_atLocal_987_);
goto v___jp_1049_;
}
else
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
if (v___x_1059_ == 0)
{
if (v___x_1057_ == 0)
{
lean_dec_ref(v_atLocal_987_);
goto v___jp_1049_;
}
else
{
size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1056_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_987_, v_hypotheses_1047_, v___x_1060_, v___x_1061_, v___x_1058_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
v___y_1054_ = v___x_1062_;
goto v___jp_1053_;
}
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = lean_usize_of_nat(v___x_1056_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_987_, v_hypotheses_1047_, v___x_1063_, v___x_1064_, v___x_1058_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
v___y_1054_ = v___x_1065_;
goto v___jp_1053_;
}
}
v___jp_1049_:
{
if (v_type_1048_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_atTarget_988_);
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Elab_Tactic_withMainContext___redArg(v_atTarget_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1052_;
}
}
v___jp_1053_:
{
if (lean_obj_tag(v___y_1054_) == 0)
{
lean_dec_ref_known(v___y_1054_, 1);
goto v___jp_1049_;
}
else
{
lean_dec_ref(v_atTarget_988_);
return v___y_1054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___boxed(lean_object* v_loc_1066_, lean_object* v_atLocal_1067_, lean_object* v_atTarget_1068_, lean_object* v_failed_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Elab_Tactic_withLocation(v_loc_1066_, v_atLocal_1067_, v_atTarget_1068_, v_failed_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_loc_1066_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(lean_object* v_00_u03b1_1120_, lean_object* v_x_1121_, lean_object* v_ctx_x3f_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1121_, v_ctx_x3f_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1133_, lean_object* v_x_1134_, lean_object* v_ctx_x3f_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_1133_, v_x_1134_, v_ctx_x3f_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1145_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Location(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Location(builtin);
}
#ifdef __cplusplus
}
#endif
