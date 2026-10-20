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
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_Location_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_hypotheses_7_; uint8_t v_type_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_hypotheses_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_hypotheses_7_);
v_type_8_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5_, 1);
v___x_9_ = lean_box(v_type_8_);
v___x_10_ = lean_apply_2(v_k_6_, v_hypotheses_7_, v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Tactic_Location_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_wildcard_elim___redArg(lean_object* v_t_23_, lean_object* v_wildcard_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_23_, v_wildcard_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_wildcard_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_wildcard_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_27_, v_wildcard_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_targets_elim___redArg(lean_object* v_t_31_, lean_object* v_targets_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_31_, v_targets_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Location_targets_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_targets_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_35_, v_targets_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(lean_object* v_as_48_, size_t v_i_49_, size_t v_stop_50_, lean_object* v_b_51_){
_start:
{
lean_object* v___y_53_; uint8_t v___x_57_; 
v___x_57_ = lean_usize_dec_eq(v_i_49_, v_stop_50_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_58_ = lean_array_uget_borrowed(v_as_48_, v_i_49_);
lean_inc(v___x_58_);
v___x_59_ = l_Lean_Syntax_getKind(v___x_58_);
v___x_60_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4));
v___x_61_ = lean_name_eq(v___x_59_, v___x_60_);
lean_dec(v___x_59_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_inc(v___x_58_);
v___x_62_ = lean_array_push(v_b_51_, v___x_58_);
v___y_53_ = v___x_62_;
goto v___jp_52_;
}
else
{
v___y_53_ = v_b_51_;
goto v___jp_52_;
}
}
else
{
return v_b_51_;
}
v___jp_52_:
{
size_t v___x_54_; size_t v___x_55_; 
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_49_, v___x_54_);
v_i_49_ = v___x_55_;
v_b_51_ = v___y_53_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; lean_object* v_res_69_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_as_63_, v_i_boxed_67_, v_stop_boxed_68_, v_b_66_);
lean_dec_ref(v_as_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object* v_stx_78_){
_start:
{
lean_object* v___x_79_; lean_object* v_arg_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_79_ = lean_unsigned_to_nat(1u);
v_arg_80_ = l_Lean_Syntax_getArg(v_stx_78_, v___x_79_);
lean_inc(v_arg_80_);
v___x_81_ = l_Lean_Syntax_getKind(v_arg_80_);
v___x_82_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__1));
v___x_83_ = lean_name_eq(v___x_81_, v___x_82_);
lean_dec(v___x_81_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_locationHyps_86_; lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_Syntax_getArg(v_arg_80_, v___x_84_);
lean_dec(v_arg_80_);
v_locationHyps_86_ = l_Lean_Syntax_getArgs(v___x_85_);
lean_dec(v___x_85_);
v___x_87_ = lean_array_get_size(v_locationHyps_86_);
v___x_94_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__2));
v___x_95_ = lean_nat_dec_lt(v___x_84_, v___x_87_);
if (v___x_95_ == 0)
{
lean_dec_ref(v_locationHyps_86_);
v___y_89_ = v___x_94_;
goto v___jp_88_;
}
else
{
size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((size_t)0ULL);
v___x_97_ = lean_usize_of_nat(v___x_87_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_86_, v___x_96_, v___x_97_, v___x_94_);
lean_dec_ref(v_locationHyps_86_);
v___y_89_ = v___x_98_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v_numTurnstiles_91_; uint8_t v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_array_get_size(v___y_89_);
v_numTurnstiles_91_ = lean_nat_sub(v___x_87_, v___x_90_);
v___x_92_ = lean_nat_dec_lt(v___x_84_, v_numTurnstiles_91_);
lean_dec(v_numTurnstiles_91_);
v___x_93_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_93_, 0, v___y_89_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
return v___x_93_;
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v_arg_80_);
v___x_99_ = lean_box(0);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation___boxed(lean_object* v_stx_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Elab_Tactic_expandLocation(v_stx_100_);
lean_dec(v_stx_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object* v_stx_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Lean_Syntax_isNone(v_stx_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_stx_102_, v___x_104_);
v___x_106_ = l_Lean_Elab_Tactic_expandLocation(v___x_105_);
lean_dec(v___x_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__2));
v___x_108_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_103_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation___boxed(lean_object* v_stx_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_Tactic_expandOptLocation(v_stx_109_);
lean_dec(v_stx_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(lean_object* v_x_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; 
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
v___x_121_ = lean_apply_9(v_x_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, lean_box(0));
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(lean_object* v_x_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(v_x_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(lean_object* v_mvarId_133_, lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; 
lean_inc(v___y_138_);
lean_inc_ref(v___y_137_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_144_, 0, v_x_134_);
lean_closure_set(v___f_144_, 1, v___y_135_);
lean_closure_set(v___f_144_, 2, v___y_136_);
lean_closure_set(v___f_144_, 3, v___y_137_);
lean_closure_set(v___f_144_, 4, v___y_138_);
v___x_145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_133_, v___f_144_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_145_) == 0)
{
return v___x_145_;
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___boxed(lean_object* v_mvarId_154_, lean_object* v_x_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_154_, v_x_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(lean_object* v_00_u03b1_166_, lean_object* v_mvarId_167_, lean_object* v_x_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_167_, v_x_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___boxed(lean_object* v_00_u03b1_179_, lean_object* v_mvarId_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(v_00_u03b1_179_, v_mvarId_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(lean_object* v___x_192_, lean_object* v_ctx_x3f_193_, size_t v_sz_194_, size_t v_i_195_, lean_object* v_bs_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_195_, v_sz_194_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec_ref(v_ctx_x3f_193_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v_bs_196_);
return v___x_207_;
}
else
{
lean_object* v_assignment_208_; lean_object* v_v_209_; lean_object* v___x_210_; lean_object* v_bs_x27_211_; lean_object* v_a_213_; lean_object* v_tree_218_; lean_object* v___x_219_; 
v_assignment_208_ = lean_ctor_get(v___x_192_, 0);
v_v_209_ = lean_array_uget(v_bs_196_, v_i_195_);
v___x_210_ = lean_unsigned_to_nat(0u);
v_bs_x27_211_ = lean_array_uset(v_bs_196_, v_i_195_, v___x_210_);
v_tree_218_ = l_Lean_Elab_InfoTree_substitute(v_v_209_, v_assignment_208_);
lean_inc_ref(v_ctx_x3f_193_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
lean_inc(v___y_200_);
lean_inc_ref(v___y_199_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
v___x_219_ = lean_apply_9(v_ctx_x3f_193_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, lean_box(0));
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_219_, 1);
if (lean_obj_tag(v_a_220_) == 0)
{
v_a_213_ = v_tree_218_;
goto v___jp_212_;
}
else
{
lean_object* v_val_221_; lean_object* v___x_222_; 
v_val_221_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v_a_220_, 1);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_val_221_);
lean_ctor_set(v___x_222_, 1, v_tree_218_);
v_a_213_ = v___x_222_;
goto v___jp_212_;
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec_ref(v_tree_218_);
lean_dec_ref(v_bs_x27_211_);
lean_dec_ref(v_ctx_x3f_193_);
v_a_223_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_219_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_219_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
v___jp_212_:
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = ((size_t)1ULL);
v___x_215_ = lean_usize_add(v_i_195_, v___x_214_);
v___x_216_ = lean_array_uset(v_bs_x27_211_, v_i_195_, v_a_213_);
v_i_195_ = v___x_215_;
v_bs_196_ = v___x_216_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v___x_231_, lean_object* v_ctx_x3f_232_, lean_object* v_sz_233_, lean_object* v_i_234_, lean_object* v_bs_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_233_);
lean_dec(v_sz_233_);
v_i_boxed_246_ = lean_unbox_usize(v_i_234_);
lean_dec(v_i_234_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_231_, v_ctx_x3f_232_, v_sz_boxed_245_, v_i_boxed_246_, v_bs_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec_ref(v___x_231_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(lean_object* v___x_248_, lean_object* v_ctx_x3f_249_, lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v_cs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_286_; 
v_cs_260_ = lean_ctor_get(v_x_250_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_286_ == 0)
{
v___x_262_ = v_x_250_;
v_isShared_263_ = v_isSharedCheck_286_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_cs_260_);
lean_dec(v_x_250_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_286_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
size_t v_sz_264_; size_t v___x_265_; lean_object* v___x_266_; 
v_sz_264_ = lean_array_size(v_cs_260_);
v___x_265_ = ((size_t)0ULL);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_248_, v_ctx_x3f_249_, v_sz_264_, v___x_265_, v_cs_260_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_a_267_);
v___x_272_ = v___x_262_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_del_object(v___x_262_);
v_a_278_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_266_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_266_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
else
{
lean_object* v_vs_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_313_; 
v_vs_287_ = lean_ctor_get(v_x_250_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_313_ == 0)
{
v___x_289_ = v_x_250_;
v_isShared_290_ = v_isSharedCheck_313_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_vs_287_);
lean_dec(v_x_250_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_313_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
size_t v_sz_291_; size_t v___x_292_; lean_object* v___x_293_; 
v_sz_291_ = lean_array_size(v_vs_287_);
v___x_292_ = ((size_t)0ULL);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_248_, v_ctx_x3f_249_, v_sz_291_, v___x_292_, v_vs_287_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_304_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_a_294_);
v___x_299_ = v___x_289_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_303_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_del_object(v___x_289_);
v_a_305_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_293_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_293_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v___x_314_, lean_object* v_ctx_x3f_315_, size_t v_sz_316_, size_t v_i_317_, lean_object* v_bs_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec_ref(v_ctx_x3f_315_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_bs_318_);
return v___x_329_;
}
else
{
lean_object* v_v_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; lean_object* v___x_333_; 
v_v_330_ = lean_array_uget(v_bs_318_, v_i_317_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_318_, v_i_317_, v___x_331_);
lean_inc_ref(v_ctx_x3f_315_);
v___x_333_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_314_, v_ctx_x3f_315_, v_v_330_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_317_, v___x_335_);
v___x_337_ = lean_array_uset(v_bs_x27_332_, v_i_317_, v_a_334_);
v_i_317_ = v___x_336_;
v_bs_318_ = v___x_337_;
goto _start;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v_bs_x27_332_);
lean_dec_ref(v_ctx_x3f_315_);
v_a_339_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_333_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_333_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v___x_347_, lean_object* v_ctx_x3f_348_, lean_object* v_sz_349_, lean_object* v_i_350_, lean_object* v_bs_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
size_t v_sz_boxed_361_; size_t v_i_boxed_362_; lean_object* v_res_363_; 
v_sz_boxed_361_ = lean_unbox_usize(v_sz_349_);
lean_dec(v_sz_349_);
v_i_boxed_362_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_347_, v_ctx_x3f_348_, v_sz_boxed_361_, v_i_boxed_362_, v_bs_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v___x_347_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v___x_364_, lean_object* v_ctx_x3f_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_364_, v_ctx_x3f_365_, v_x_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec_ref(v___x_364_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(lean_object* v___x_377_, lean_object* v_ctx_x3f_378_, lean_object* v_t_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_root_389_; lean_object* v_tail_390_; lean_object* v_size_391_; size_t v_shift_392_; lean_object* v_tailOff_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_429_; 
v_root_389_ = lean_ctor_get(v_t_379_, 0);
v_tail_390_ = lean_ctor_get(v_t_379_, 1);
v_size_391_ = lean_ctor_get(v_t_379_, 2);
v_shift_392_ = lean_ctor_get_usize(v_t_379_, 4);
v_tailOff_393_ = lean_ctor_get(v_t_379_, 3);
v_isSharedCheck_429_ = !lean_is_exclusive(v_t_379_);
if (v_isSharedCheck_429_ == 0)
{
v___x_395_ = v_t_379_;
v_isShared_396_ = v_isSharedCheck_429_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_tailOff_393_);
lean_inc(v_size_391_);
lean_inc(v_tail_390_);
lean_inc(v_root_389_);
lean_dec(v_t_379_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_429_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; 
lean_inc_ref(v_ctx_x3f_378_);
v___x_397_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_377_, v_ctx_x3f_378_, v_root_389_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v_sz_399_ = lean_array_size(v_tail_390_);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_377_, v_ctx_x3f_378_, v_sz_399_, v___x_400_, v_tail_390_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_412_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_412_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v_a_402_);
lean_ctor_set(v___x_395_, 0, v_a_398_);
v___x_407_ = v___x_395_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_398_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_a_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_size_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_tailOff_393_);
lean_ctor_set_usize(v_reuseFailAlloc_411_, 4, v_shift_392_);
v___x_407_ = v_reuseFailAlloc_411_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_a_398_);
lean_del_object(v___x_395_);
lean_dec(v_tailOff_393_);
lean_dec(v_size_391_);
v_a_413_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_401_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_401_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_del_object(v___x_395_);
lean_dec(v_tailOff_393_);
lean_dec(v_size_391_);
lean_dec_ref(v_tail_390_);
lean_dec_ref(v_ctx_x3f_378_);
v_a_421_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_397_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_397_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5___boxed(lean_object* v___x_430_, lean_object* v_ctx_x3f_431_, lean_object* v_t_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_430_, v_ctx_x3f_431_, v_t_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v___x_430_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(lean_object* v___y_443_, lean_object* v_ctx_x3f_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v_a_452_, lean_object* v_a_x3f_453_){
_start:
{
lean_object* v___x_455_; lean_object* v_infoState_456_; lean_object* v_trees_457_; lean_object* v___x_458_; 
v___x_455_ = lean_st_ref_get(v___y_443_);
v_infoState_456_ = lean_ctor_get(v___x_455_, 8);
lean_inc_ref(v_infoState_456_);
lean_dec(v___x_455_);
v_trees_457_ = lean_ctor_get(v_infoState_456_, 2);
lean_inc_ref(v_trees_457_);
v___x_458_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_456_, v_ctx_x3f_444_, v_trees_457_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_443_);
lean_dec_ref(v_infoState_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_498_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_498_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_498_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_498_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v_infoState_464_; lean_object* v_env_465_; lean_object* v_nextMacroScope_466_; lean_object* v_ngen_467_; lean_object* v_auxDeclNGen_468_; lean_object* v_traceState_469_; lean_object* v_cache_470_; lean_object* v_recordedDeps_471_; lean_object* v_messages_472_; lean_object* v_snapshotTasks_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_497_; 
v___x_463_ = lean_st_ref_take(v___y_443_);
v_infoState_464_ = lean_ctor_get(v___x_463_, 8);
v_env_465_ = lean_ctor_get(v___x_463_, 0);
v_nextMacroScope_466_ = lean_ctor_get(v___x_463_, 1);
v_ngen_467_ = lean_ctor_get(v___x_463_, 2);
v_auxDeclNGen_468_ = lean_ctor_get(v___x_463_, 3);
v_traceState_469_ = lean_ctor_get(v___x_463_, 4);
v_cache_470_ = lean_ctor_get(v___x_463_, 5);
v_recordedDeps_471_ = lean_ctor_get(v___x_463_, 6);
v_messages_472_ = lean_ctor_get(v___x_463_, 7);
v_snapshotTasks_473_ = lean_ctor_get(v___x_463_, 9);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_497_ == 0)
{
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_497_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snapshotTasks_473_);
lean_inc(v_infoState_464_);
lean_inc(v_messages_472_);
lean_inc(v_recordedDeps_471_);
lean_inc(v_cache_470_);
lean_inc(v_traceState_469_);
lean_inc(v_auxDeclNGen_468_);
lean_inc(v_ngen_467_);
lean_inc(v_nextMacroScope_466_);
lean_inc(v_env_465_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_497_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v_enabled_477_; lean_object* v_assignment_478_; lean_object* v_lazyAssignment_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_495_; 
v_enabled_477_ = lean_ctor_get_uint8(v_infoState_464_, sizeof(void*)*3);
v_assignment_478_ = lean_ctor_get(v_infoState_464_, 0);
v_lazyAssignment_479_ = lean_ctor_get(v_infoState_464_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_infoState_464_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_infoState_464_, 2);
lean_dec(v_unused_496_);
v___x_481_ = v_infoState_464_;
v_isShared_482_ = v_isSharedCheck_495_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_lazyAssignment_479_);
lean_inc(v_assignment_478_);
lean_dec(v_infoState_464_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_495_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = lean_box(0);
v___x_484_ = l_Lean_PersistentArray_append___redArg(v_a_452_, v_a_459_);
lean_dec(v_a_459_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 2, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_assignment_478_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_lazyAssignment_479_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v___x_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*3, v_enabled_477_);
v___x_486_ = v_reuseFailAlloc_494_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 8, v___x_486_);
v___x_488_ = v___x_475_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_env_465_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_nextMacroScope_466_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_ngen_467_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_auxDeclNGen_468_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_traceState_469_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_cache_470_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_recordedDeps_471_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_messages_472_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_493_, 9, v_snapshotTasks_473_);
v___x_488_ = v_reuseFailAlloc_493_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_st_ref_put(v___y_443_, v___x_488_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_483_);
v___x_491_ = v___x_461_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_483_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v_a_452_);
v_a_499_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_458_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_458_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_507_, lean_object* v_ctx_x3f_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v_a_516_, lean_object* v_a_x3f_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_507_, v_ctx_x3f_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v_a_516_, v_a_x3f_517_);
lean_dec(v_a_x3f_517_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_507_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_unsigned_to_nat(32u);
v___x_521_ = lean_mk_empty_array_with_capacity(v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = ((size_t)5ULL);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_unsigned_to_nat(32u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_528_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
lean_ctor_set(v___x_528_, 2, v___x_524_);
lean_ctor_set(v___x_528_, 3, v___x_524_);
lean_ctor_set_usize(v___x_528_, 4, v___x_523_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; lean_object* v_infoState_532_; lean_object* v_trees_533_; lean_object* v___x_534_; lean_object* v_infoState_535_; lean_object* v_env_536_; lean_object* v_nextMacroScope_537_; lean_object* v_ngen_538_; lean_object* v_auxDeclNGen_539_; lean_object* v_traceState_540_; lean_object* v_cache_541_; lean_object* v_recordedDeps_542_; lean_object* v_messages_543_; lean_object* v_snapshotTasks_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_565_; 
v___x_531_ = lean_st_ref_get(v___y_529_);
v_infoState_532_ = lean_ctor_get(v___x_531_, 8);
lean_inc_ref(v_infoState_532_);
lean_dec(v___x_531_);
v_trees_533_ = lean_ctor_get(v_infoState_532_, 2);
lean_inc_ref(v_trees_533_);
lean_dec_ref(v_infoState_532_);
v___x_534_ = lean_st_ref_take(v___y_529_);
v_infoState_535_ = lean_ctor_get(v___x_534_, 8);
v_env_536_ = lean_ctor_get(v___x_534_, 0);
v_nextMacroScope_537_ = lean_ctor_get(v___x_534_, 1);
v_ngen_538_ = lean_ctor_get(v___x_534_, 2);
v_auxDeclNGen_539_ = lean_ctor_get(v___x_534_, 3);
v_traceState_540_ = lean_ctor_get(v___x_534_, 4);
v_cache_541_ = lean_ctor_get(v___x_534_, 5);
v_recordedDeps_542_ = lean_ctor_get(v___x_534_, 6);
v_messages_543_ = lean_ctor_get(v___x_534_, 7);
v_snapshotTasks_544_ = lean_ctor_get(v___x_534_, 9);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_565_ == 0)
{
v___x_546_ = v___x_534_;
v_isShared_547_ = v_isSharedCheck_565_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snapshotTasks_544_);
lean_inc(v_infoState_535_);
lean_inc(v_messages_543_);
lean_inc(v_recordedDeps_542_);
lean_inc(v_cache_541_);
lean_inc(v_traceState_540_);
lean_inc(v_auxDeclNGen_539_);
lean_inc(v_ngen_538_);
lean_inc(v_nextMacroScope_537_);
lean_inc(v_env_536_);
lean_dec(v___x_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_565_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v_enabled_548_; lean_object* v_assignment_549_; lean_object* v_lazyAssignment_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_563_; 
v_enabled_548_ = lean_ctor_get_uint8(v_infoState_535_, sizeof(void*)*3);
v_assignment_549_ = lean_ctor_get(v_infoState_535_, 0);
v_lazyAssignment_550_ = lean_ctor_get(v_infoState_535_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_infoState_535_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_infoState_535_, 2);
lean_dec(v_unused_564_);
v___x_552_ = v_infoState_535_;
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_lazyAssignment_550_);
lean_inc(v_assignment_549_);
lean_dec(v_infoState_535_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 2, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_assignment_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_lazyAssignment_550_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v___x_554_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3, v_enabled_548_);
v___x_556_ = v_reuseFailAlloc_562_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 8, v___x_556_);
v___x_558_ = v___x_546_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_env_536_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_537_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_538_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_539_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_traceState_540_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_cache_541_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_recordedDeps_542_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_messages_543_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_561_, 9, v_snapshotTasks_544_);
v___x_558_ = v_reuseFailAlloc_561_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_st_ref_put(v___y_529_, v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_trees_533_);
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_566_);
lean_dec(v___y_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(lean_object* v_x_569_, lean_object* v_ctx_x3f_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; lean_object* v_infoState_581_; uint8_t v_enabled_582_; 
v___x_580_ = lean_st_ref_get(v___y_578_);
v_infoState_581_ = lean_ctor_get(v___x_580_, 8);
lean_inc_ref(v_infoState_581_);
lean_dec(v___x_580_);
v_enabled_582_ = lean_ctor_get_uint8(v_infoState_581_, sizeof(void*)*3);
lean_dec_ref(v_infoState_581_);
if (v_enabled_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_ctx_x3f_570_);
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
v___x_583_ = lean_apply_9(v_x_569_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, lean_box(0));
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v_a_585_; lean_object* v_r_586_; 
v___x_584_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_578_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref(v___x_584_);
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
v_r_586_ = lean_apply_9(v_x_569_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, lean_box(0));
if (lean_obj_tag(v_r_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_611_; 
v_a_587_ = lean_ctor_get(v_r_586_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_r_586_);
if (v_isSharedCheck_611_ == 0)
{
v___x_589_ = v_r_586_;
v_isShared_590_ = v_isSharedCheck_611_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v_r_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_611_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
lean_inc(v_a_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 1);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_610_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_578_, v_ctx_x3f_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v_a_585_, v___x_592_);
lean_dec_ref(v___x_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_601_);
v___x_595_ = v___x_593_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_dec(v___x_593_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_a_587_);
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_587_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_a_587_);
v_a_602_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_593_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_593_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_a_612_ = lean_ctor_get(v_r_586_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v_r_586_, 1);
v___x_613_ = lean_box(0);
v___x_614_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_578_, v_ctx_x3f_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v_a_585_, v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_614_, 0);
lean_dec(v_unused_622_);
v___x_616_ = v___x_614_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_dec(v___x_614_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 1);
lean_ctor_set(v___x_616_, 0, v_a_612_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_612_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_612_);
v_a_623_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_614_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_614_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___boxed(lean_object* v_x_631_, lean_object* v_ctx_x3f_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_631_, v_ctx_x3f_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; lean_object* v_toCold_650_; lean_object* v_mctx_651_; lean_object* v_currNamespace_652_; lean_object* v_openDecls_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_ngen_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_647_ = lean_st_ref_get(v___y_645_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_st_ref_get(v___y_643_);
v_toCold_650_ = lean_ctor_get(v___y_644_, 0);
v_mctx_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_mctx_651_);
lean_dec(v___x_649_);
v_currNamespace_652_ = lean_ctor_get(v_toCold_650_, 4);
v_openDecls_653_ = lean_ctor_get(v_toCold_650_, 5);
v___x_654_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_644_);
v___x_655_ = lean_st_ref_get(v___y_645_);
v_ngen_656_ = lean_ctor_get(v___x_655_, 2);
lean_inc_ref(v_ngen_656_);
lean_dec(v___x_655_);
v___x_657_ = lean_box(0);
v___x_658_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_653_);
lean_inc(v_currNamespace_652_);
v___x_659_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_659_, 0, v_env_648_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_658_);
lean_ctor_set(v___x_659_, 3, v_mctx_651_);
lean_ctor_set(v___x_659_, 4, v___x_654_);
lean_ctor_set(v___x_659_, 5, v_currNamespace_652_);
lean_ctor_set(v___x_659_, 6, v_openDecls_653_);
lean_ctor_set(v___x_659_, 7, v_ngen_656_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; lean_object* v_toCold_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_701_; 
v___x_675_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_671_, v___y_672_, v___y_673_);
v_toCold_676_ = lean_ctor_get(v___y_672_, 0);
v_a_677_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_701_ == 0)
{
v___x_679_ = v___x_675_;
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_fileMap_681_; lean_object* v_env_682_; lean_object* v_mctx_683_; lean_object* v_options_684_; lean_object* v_currNamespace_685_; lean_object* v_openDecls_686_; lean_object* v_ngen_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_698_; 
v_fileMap_681_ = lean_ctor_get(v_toCold_676_, 1);
v_env_682_ = lean_ctor_get(v_a_677_, 0);
v_mctx_683_ = lean_ctor_get(v_a_677_, 3);
v_options_684_ = lean_ctor_get(v_a_677_, 4);
v_currNamespace_685_ = lean_ctor_get(v_a_677_, 5);
v_openDecls_686_ = lean_ctor_get(v_a_677_, 6);
v_ngen_687_ = lean_ctor_get(v_a_677_, 7);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_677_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_699_ = lean_ctor_get(v_a_677_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_a_677_, 1);
lean_dec(v_unused_700_);
v___x_689_ = v_a_677_;
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_ngen_687_);
lean_inc(v_openDecls_686_);
lean_inc(v_currNamespace_685_);
lean_inc(v_options_684_);
lean_inc(v_mctx_683_);
lean_inc(v_env_682_);
lean_dec(v_a_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_box(0);
lean_inc_ref(v_fileMap_681_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 2, v_fileMap_681_);
lean_ctor_set(v___x_689_, 1, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_env_682_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_fileMap_681_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_mctx_683_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_options_684_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v_currNamespace_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 6, v_openDecls_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 7, v_ngen_687_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_693_);
v___x_695_ = v___x_679_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0___boxed(lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_731_; 
v___x_721_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_731_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_a_722_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed(lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; 
v___f_753_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0));
v___x_754_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_743_, v___f_753_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(lean_object* v_00_u03b1_766_, lean_object* v_x_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed(lean_object* v_00_u03b1_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(v_00_u03b1_778_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(lean_object* v_atLocal_790_, lean_object* v_as_791_, size_t v_sz_792_, size_t v_i_793_, uint8_t v_b_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v_a_805_; uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_lt(v_i_793_, v_sz_792_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v_atLocal_790_);
v___x_810_ = lean_box(v_b_794_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_array_uget_borrowed(v_as_791_, v_i_793_);
lean_inc(v_a_812_);
v___x_813_ = l_Lean_FVarId_getDecl___redArg(v_a_812_, v___y_799_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; uint8_t v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = l_Lean_LocalDecl_isImplementationDetail(v_a_814_);
lean_dec(v_a_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_inc_ref(v_atLocal_790_);
lean_inc(v_a_812_);
v___x_816_ = lean_apply_1(v_atLocal_790_, v_a_812_);
v___x_817_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_817_, 0, lean_box(0));
lean_closure_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_818_, 0, lean_box(0));
lean_closure_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_818_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_819_) == 0)
{
if (v_b_794_ == 0)
{
lean_object* v_a_820_; uint8_t v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = lean_unbox(v_a_820_);
lean_dec(v_a_820_);
v_a_805_ = v___x_821_;
goto v___jp_804_;
}
else
{
lean_dec_ref_known(v___x_819_, 1);
v_a_805_ = v___x_809_;
goto v___jp_804_;
}
}
else
{
lean_dec_ref(v_atLocal_790_);
return v___x_819_;
}
}
else
{
v_a_805_ = v_b_794_;
goto v___jp_804_;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v_atLocal_790_);
v_a_822_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_813_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_813_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
v___jp_804_:
{
size_t v___x_806_; size_t v___x_807_; 
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_793_, v___x_806_);
v_i_793_ = v___x_807_;
v_b_794_ = v_a_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1___boxed(lean_object* v_atLocal_830_, lean_object* v_as_831_, lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
size_t v_sz_boxed_844_; size_t v_i_boxed_845_; uint8_t v_b_boxed_846_; lean_object* v_res_847_; 
v_sz_boxed_844_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_845_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_b_boxed_846_ = lean_unbox(v_b_834_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_830_, v_as_831_, v_sz_boxed_844_, v_i_boxed_845_, v_b_boxed_846_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v_as_831_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0(lean_object* v_atLocal_848_, uint8_t v_a_849_, lean_object* v_failed_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_lctx_860_; lean_object* v___x_861_; lean_object* v___x_862_; size_t v_sz_863_; size_t v___x_864_; lean_object* v___x_865_; 
v_lctx_860_ = lean_ctor_get(v___y_855_, 2);
v___x_861_ = l_Lean_LocalContext_getFVarIds(v_lctx_860_);
v___x_862_ = l_Array_reverse___redArg(v___x_861_);
v_sz_863_ = lean_array_size(v___x_862_);
v___x_864_ = ((size_t)0ULL);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_848_, v___x_862_, v_sz_863_, v___x_864_, v_a_849_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec_ref(v___x_862_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_886_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_886_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_886_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_886_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
uint8_t v___x_870_; 
v___x_870_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_del_object(v___x_868_);
v___x_871_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_852_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = lean_apply_10(v_failed_850_, v_a_872_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_873_;
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_failed_850_);
v_a_874_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_871_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_871_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_failed_850_);
v___x_882_ = lean_box(0);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_882_);
v___x_884_ = v___x_868_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_failed_850_);
v_a_887_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_865_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_865_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0___boxed(lean_object* v_atLocal_895_, lean_object* v_a_896_, lean_object* v_failed_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_a_16798__boxed_907_; lean_object* v_res_908_; 
v_a_16798__boxed_907_ = lean_unbox(v_a_896_);
v_res_908_ = l_Lean_Elab_Tactic_withLocation___lam__0(v_atLocal_895_, v_a_16798__boxed_907_, v_failed_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(lean_object* v___x_909_, lean_object* v_atLocal_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Elab_Tactic_getFVarId(v___x_909_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_apply_10(v_atLocal_910_, v_a_921_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_922_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec_ref(v_atLocal_910_);
v_a_923_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_920_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_920_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed(lean_object* v___x_931_, lean_object* v_atLocal_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_931_, v_atLocal_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(lean_object* v_atLocal_943_, lean_object* v_as_944_, size_t v_i_945_, size_t v_stop_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_eq(v_i_945_, v_stop_946_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___f_959_; lean_object* v___x_960_; 
v___x_958_ = lean_array_uget_borrowed(v_as_944_, v_i_945_);
lean_inc_ref(v_atLocal_943_);
lean_inc(v___x_958_);
v___f_959_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed), 11, 2);
lean_closure_set(v___f_959_, 0, v___x_958_);
lean_closure_set(v___f_959_, 1, v_atLocal_943_);
v___x_960_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_959_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; size_t v___x_962_; size_t v___x_963_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_945_, v___x_962_);
v_i_945_ = v___x_963_;
v_b_947_ = v_a_961_;
goto _start;
}
else
{
lean_dec_ref(v_atLocal_943_);
return v___x_960_;
}
}
else
{
lean_object* v___x_965_; 
lean_dec_ref(v_atLocal_943_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v_b_947_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(lean_object* v_atLocal_966_, lean_object* v_as_967_, lean_object* v_i_968_, lean_object* v_stop_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
size_t v_i_boxed_980_; size_t v_stop_boxed_981_; lean_object* v_res_982_; 
v_i_boxed_980_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_stop_boxed_981_ = lean_unbox_usize(v_stop_969_);
lean_dec(v_stop_969_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_966_, v_as_967_, v_i_boxed_980_, v_stop_boxed_981_, v_b_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v_as_967_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation(lean_object* v_loc_983_, lean_object* v_atLocal_984_, lean_object* v_atTarget_985_, lean_object* v_failed_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
if (lean_obj_tag(v_loc_983_) == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_996_, 0, lean_box(0));
lean_closure_set(v___x_996_, 1, v_atTarget_985_);
v___x_997_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_997_, 0, lean_box(0));
lean_closure_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_997_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withLocation___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1000_, 0, v_atLocal_984_);
lean_closure_set(v___f_1000_, 1, v_a_999_);
lean_closure_set(v___f_1000_, 2, v_failed_986_);
v___x_1001_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_988_, v_a_990_, v_a_992_, v_a_994_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_988_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
lean_dec(v_a_1002_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_1004_, v___f_1000_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v___f_1000_);
v_a_1006_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1008_ = v___x_1003_;
v_isShared_1009_ = v_isSharedCheck_1028_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1003_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1028_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Lean_Exception_isInterrupt(v_a_1006_);
if (v___x_1010_ == 0)
{
uint8_t v___x_1011_; 
lean_inc(v_a_1006_);
v___x_1011_ = l_Lean_Exception_isRuntime(v_a_1006_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_del_object(v___x_1008_);
lean_dec(v_a_1006_);
v___x_1012_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1002_, v___x_1011_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1021_);
v___x_1014_ = v___x_1012_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_dec(v___x_1012_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(0);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1023_; 
lean_dec(v_a_1002_);
if (v_isShared_1009_ == 0)
{
v___x_1023_ = v___x_1008_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1006_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_object* v___x_1026_; 
lean_dec(v_a_1002_);
if (v_isShared_1009_ == 0)
{
v___x_1026_ = v___x_1008_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1006_);
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
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___f_1000_);
v_a_1029_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1001_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1001_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_failed_986_);
lean_dec_ref(v_atLocal_984_);
v_a_1037_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_998_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_998_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_hypotheses_1045_; uint8_t v_type_1046_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
lean_dec_ref(v_failed_986_);
v_hypotheses_1045_ = lean_ctor_get(v_loc_983_, 0);
v_type_1046_ = lean_ctor_get_uint8(v_loc_983_, sizeof(void*)*1);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_array_get_size(v_hypotheses_1045_);
v___x_1053_ = lean_nat_dec_lt(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v_atLocal_984_);
goto v___jp_1047_;
}
else
{
lean_object* v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = lean_usize_of_nat(v___x_1052_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_984_, v_hypotheses_1045_, v___x_1055_, v___x_1056_, v___x_1054_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref_known(v___x_1057_, 1);
goto v___jp_1047_;
}
else
{
lean_dec_ref(v_atTarget_985_);
return v___x_1057_;
}
}
v___jp_1047_:
{
if (v_type_1046_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v_atTarget_985_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Elab_Tactic_withMainContext___redArg(v_atTarget_985_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___boxed(lean_object* v_loc_1058_, lean_object* v_atLocal_1059_, lean_object* v_atTarget_1060_, lean_object* v_failed_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Elab_Tactic_withLocation(v_loc_1058_, v_atLocal_1059_, v_atTarget_1060_, v_failed_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_loc_1058_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(lean_object* v_00_u03b1_1112_, lean_object* v_x_1113_, lean_object* v_ctx_x3f_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1113_, v_ctx_x3f_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_x_1126_, lean_object* v_ctx_x3f_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_1125_, v_x_1126_, v_ctx_x3f_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1137_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
