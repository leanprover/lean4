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
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(uint8_t v___x_48_, lean_object* v_as_49_, size_t v_i_50_, size_t v_stop_51_, lean_object* v_b_52_){
_start:
{
lean_object* v___y_54_; uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_eq(v_i_50_, v_stop_51_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_59_ = lean_array_uget_borrowed(v_as_49_, v_i_50_);
lean_inc(v___x_59_);
v___x_60_ = l_Lean_Syntax_getKind(v___x_59_);
v___x_61_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4));
v___x_62_ = lean_name_eq(v___x_60_, v___x_61_);
lean_dec(v___x_60_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_inc(v___x_59_);
v___x_63_ = lean_array_push(v_b_52_, v___x_59_);
v___y_54_ = v___x_63_;
goto v___jp_53_;
}
else
{
if (v___x_48_ == 0)
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_48_ = stack[0].m_num;
lean_object* v_as_49_ = stack[1].m_obj;
size_t v_i_50_ = stack[2].m_num;
size_t v_stop_51_ = stack[3].m_num;
lean_object* v_b_52_ = stack[4].m_obj;
lean_object* v_res_65_;
v_res_65_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v___x_48_, v_as_49_, v_i_50_, v_stop_51_, v_b_52_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___boxed(lean_object* v___x_66_, lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_, lean_object* v_b_70_){
_start:
{
uint8_t v___x_263__boxed_71_; size_t v_i_boxed_72_; size_t v_stop_boxed_73_; lean_object* v_res_74_; 
v___x_263__boxed_71_ = lean_unbox(v___x_66_);
v_i_boxed_72_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_73_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_res_74_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v___x_263__boxed_71_, v_as_67_, v_i_boxed_72_, v_stop_boxed_73_, v_b_70_);
lean_dec_ref(v_as_67_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object* v_stx_83_){
_start:
{
lean_object* v___x_84_; lean_object* v_arg_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v_arg_85_ = l_Lean_Syntax_getArg(v_stx_83_, v___x_84_);
lean_inc(v_arg_85_);
v___x_86_ = l_Lean_Syntax_getKind(v_arg_85_);
v___x_87_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__1));
v___x_88_ = lean_name_eq(v___x_86_, v___x_87_);
lean_dec(v___x_86_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_locationHyps_91_; lean_object* v___x_92_; lean_object* v___y_94_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Lean_Syntax_getArg(v_arg_85_, v___x_89_);
lean_dec(v_arg_85_);
v_locationHyps_91_ = l_Lean_Syntax_getArgs(v___x_90_);
lean_dec(v___x_90_);
v___x_92_ = lean_array_get_size(v_locationHyps_91_);
v___x_99_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__2));
v___x_100_ = lean_nat_dec_lt(v___x_89_, v___x_92_);
if (v___x_100_ == 0)
{
lean_dec_ref(v_locationHyps_91_);
v___y_94_ = v___x_99_;
goto v___jp_93_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_le(v___x_92_, v___x_92_);
if (v___x_101_ == 0)
{
if (v___x_100_ == 0)
{
lean_dec_ref(v_locationHyps_91_);
v___y_94_ = v___x_99_;
goto v___jp_93_;
}
else
{
size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((size_t)0ULL);
v___x_103_ = lean_usize_of_nat(v___x_92_);
v___x_104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v___x_88_, v_locationHyps_91_, v___x_102_, v___x_103_, v___x_99_);
lean_dec_ref(v_locationHyps_91_);
v___y_94_ = v___x_104_;
goto v___jp_93_;
}
}
else
{
size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_92_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v___x_88_, v_locationHyps_91_, v___x_105_, v___x_106_, v___x_99_);
lean_dec_ref(v_locationHyps_91_);
v___y_94_ = v___x_107_;
goto v___jp_93_;
}
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v_numTurnstiles_96_; uint8_t v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_array_get_size(v___y_94_);
v_numTurnstiles_96_ = lean_nat_sub(v___x_92_, v___x_95_);
v___x_97_ = lean_nat_dec_lt(v___x_89_, v_numTurnstiles_96_);
lean_dec(v_numTurnstiles_96_);
v___x_98_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_98_, 0, v___y_94_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
return v___x_98_;
}
}
else
{
lean_object* v___x_108_; 
lean_dec(v_arg_85_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandLocation___boxed(lean_object* v_stx_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_Tactic_expandLocation(v_stx_109_);
lean_dec(v_stx_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object* v_stx_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = l_Lean_Syntax_isNone(v_stx_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = l_Lean_Syntax_getArg(v_stx_111_, v___x_113_);
v___x_115_ = l_Lean_Elab_Tactic_expandLocation(v___x_114_);
lean_dec(v___x_114_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Tactic_expandLocation___closed__2));
v___x_117_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_112_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_expandOptLocation___boxed(lean_object* v_stx_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Elab_Tactic_expandOptLocation(v_stx_118_);
lean_dec(v_stx_118_);
return v_res_119_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(lean_object* v_x_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
lean_inc(v___y_124_);
lean_inc_ref(v___y_123_);
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
v___x_130_ = lean_apply_9(v_x_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_120_ = stack[0].m_obj;
lean_object* v___y_121_ = stack[1].m_obj;
lean_object* v___y_122_ = stack[2].m_obj;
lean_object* v___y_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v___y_127_ = stack[7].m_obj;
lean_object* v___y_128_ = stack[8].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(v_x_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_142_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(lean_object* v_mvarId_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___f_154_; lean_object* v___x_155_; 
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
v___f_154_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_154_, 0, v_x_144_);
lean_closure_set(v___f_154_, 1, v___y_145_);
lean_closure_set(v___f_154_, 2, v___y_146_);
lean_closure_set(v___f_154_, 3, v___y_147_);
lean_closure_set(v___f_154_, 4, v___y_148_);
v___x_155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_143_, v___f_154_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
if (lean_obj_tag(v___x_155_) == 0)
{
return v___x_155_;
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_143_ = stack[0].m_obj;
lean_object* v_x_144_ = stack[1].m_obj;
lean_object* v___y_145_ = stack[2].m_obj;
lean_object* v___y_146_ = stack[3].m_obj;
lean_object* v___y_147_ = stack[4].m_obj;
lean_object* v___y_148_ = stack[5].m_obj;
lean_object* v___y_149_ = stack[6].m_obj;
lean_object* v___y_150_ = stack[7].m_obj;
lean_object* v___y_151_ = stack[8].m_obj;
lean_object* v___y_152_ = stack[9].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_143_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___boxed(lean_object* v_mvarId_165_, lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_165_, v_x_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_176_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(lean_object* v_00_u03b1_177_, lean_object* v_mvarId_178_, lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_178_, v_x_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
return v___x_189_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_178_ = stack[1].m_obj;
lean_object* v_x_179_ = stack[2].m_obj;
lean_object* v___y_180_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[4].m_obj;
lean_object* v___y_182_ = stack[5].m_obj;
lean_object* v___y_183_ = stack[6].m_obj;
lean_object* v___y_184_ = stack[7].m_obj;
lean_object* v___y_185_ = stack[8].m_obj;
lean_object* v___y_186_ = stack[9].m_obj;
lean_object* v___y_187_ = stack[10].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(lean_box(0), v_mvarId_178_, v_x_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___boxed(lean_object* v_00_u03b1_191_, lean_object* v_mvarId_192_, lean_object* v_x_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(v_00_u03b1_191_, v_mvarId_192_, v_x_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_203_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(lean_object* v___x_204_, lean_object* v_ctx_x3f_205_, size_t v_sz_206_, size_t v_i_207_, lean_object* v_bs_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_lt(v_i_207_, v_sz_206_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec_ref(v_ctx_x3f_205_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v_bs_208_);
return v___x_219_;
}
else
{
lean_object* v_assignment_220_; lean_object* v_v_221_; lean_object* v___x_222_; lean_object* v_bs_x27_223_; lean_object* v_a_225_; lean_object* v_tree_230_; lean_object* v___x_231_; 
v_assignment_220_ = lean_ctor_get(v___x_204_, 0);
v_v_221_ = lean_array_uget(v_bs_208_, v_i_207_);
v___x_222_ = lean_unsigned_to_nat(0u);
v_bs_x27_223_ = lean_array_uset(v_bs_208_, v_i_207_, v___x_222_);
v_tree_230_ = l_Lean_Elab_InfoTree_substitute(v_v_221_, v_assignment_220_);
lean_inc_ref(v_ctx_x3f_205_);
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
v___x_231_ = lean_apply_9(v_ctx_x3f_205_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, lean_box(0));
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
if (lean_obj_tag(v_a_232_) == 0)
{
v_a_225_ = v_tree_230_;
goto v___jp_224_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_234_; 
v_val_233_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v_a_232_, 1);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_val_233_);
lean_ctor_set(v___x_234_, 1, v_tree_230_);
v_a_225_ = v___x_234_;
goto v___jp_224_;
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_tree_230_);
lean_dec_ref(v_bs_x27_223_);
lean_dec_ref(v_ctx_x3f_205_);
v_a_235_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_231_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_231_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
v___jp_224_:
{
size_t v___x_226_; size_t v___x_227_; lean_object* v___x_228_; 
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_add(v_i_207_, v___x_226_);
v___x_228_ = lean_array_uset(v_bs_x27_223_, v_i_207_, v_a_225_);
v_i_207_ = v___x_227_;
v_bs_208_ = v___x_228_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_204_ = stack[0].m_obj;
lean_object* v_ctx_x3f_205_ = stack[1].m_obj;
size_t v_sz_206_ = stack[2].m_num;
size_t v_i_207_ = stack[3].m_num;
lean_object* v_bs_208_ = stack[4].m_obj;
lean_object* v___y_209_ = stack[5].m_obj;
lean_object* v___y_210_ = stack[6].m_obj;
lean_object* v___y_211_ = stack[7].m_obj;
lean_object* v___y_212_ = stack[8].m_obj;
lean_object* v___y_213_ = stack[9].m_obj;
lean_object* v___y_214_ = stack[10].m_obj;
lean_object* v___y_215_ = stack[11].m_obj;
lean_object* v___y_216_ = stack[12].m_obj;
lean_object* v_res_243_;
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_204_, v_ctx_x3f_205_, v_sz_206_, v_i_207_, v_bs_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v___x_244_, lean_object* v_ctx_x3f_245_, lean_object* v_sz_246_, lean_object* v_i_247_, lean_object* v_bs_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
size_t v_sz_boxed_258_; size_t v_i_boxed_259_; lean_object* v_res_260_; 
v_sz_boxed_258_ = lean_unbox_usize(v_sz_246_);
lean_dec(v_sz_246_);
v_i_boxed_259_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_244_, v_ctx_x3f_245_, v_sz_boxed_258_, v_i_boxed_259_, v_bs_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec_ref(v___x_244_);
return v_res_260_;
}
}
lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(lean_object* v___x_261_, lean_object* v_ctx_x3f_262_, lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_cs_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_299_; 
v_cs_273_ = lean_ctor_get(v_x_263_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_299_ == 0)
{
v___x_275_ = v_x_263_;
v_isShared_276_ = v_isSharedCheck_299_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_cs_273_);
lean_dec(v_x_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_299_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
size_t v_sz_277_; size_t v___x_278_; lean_object* v___x_279_; 
v_sz_277_ = lean_array_size(v_cs_273_);
v___x_278_ = ((size_t)0ULL);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_261_, v_ctx_x3f_262_, v_sz_277_, v___x_278_, v_cs_273_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_290_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_290_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_290_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_290_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_a_280_);
v___x_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_285_);
v___x_287_ = v___x_282_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_del_object(v___x_275_);
v_a_291_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_279_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_279_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_object* v_vs_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_326_; 
v_vs_300_ = lean_ctor_get(v_x_263_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_326_ == 0)
{
v___x_302_ = v_x_263_;
v_isShared_303_ = v_isSharedCheck_326_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_vs_300_);
lean_dec(v_x_263_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_326_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
size_t v_sz_304_; size_t v___x_305_; lean_object* v___x_306_; 
v_sz_304_ = lean_array_size(v_vs_300_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_261_, v_ctx_x3f_262_, v_sz_304_, v___x_305_, v_vs_300_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_317_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_a_307_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_del_object(v___x_302_);
v_a_318_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_306_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_261_ = stack[0].m_obj;
lean_object* v_ctx_x3f_262_ = stack[1].m_obj;
lean_object* v_x_263_ = stack[2].m_obj;
lean_object* v___y_264_ = stack[3].m_obj;
lean_object* v___y_265_ = stack[4].m_obj;
lean_object* v___y_266_ = stack[5].m_obj;
lean_object* v___y_267_ = stack[6].m_obj;
lean_object* v___y_268_ = stack[7].m_obj;
lean_object* v___y_269_ = stack[8].m_obj;
lean_object* v___y_270_ = stack[9].m_obj;
lean_object* v___y_271_ = stack[10].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_261_, v_ctx_x3f_262_, v_x_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
stack->m_obj
 = v_res_327_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v___x_328_, lean_object* v_ctx_x3f_329_, size_t v_sz_330_, size_t v_i_331_, lean_object* v_bs_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_331_, v_sz_330_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_ctx_x3f_329_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v_bs_332_);
return v___x_343_;
}
else
{
lean_object* v_v_344_; lean_object* v___x_345_; lean_object* v_bs_x27_346_; lean_object* v___x_347_; 
v_v_344_ = lean_array_uget(v_bs_332_, v_i_331_);
v___x_345_ = lean_unsigned_to_nat(0u);
v_bs_x27_346_ = lean_array_uset(v_bs_332_, v_i_331_, v___x_345_);
lean_inc_ref(v_ctx_x3f_329_);
v___x_347_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_328_, v_ctx_x3f_329_, v_v_344_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v___x_351_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_add(v_i_331_, v___x_349_);
v___x_351_ = lean_array_uset(v_bs_x27_346_, v_i_331_, v_a_348_);
v_i_331_ = v___x_350_;
v_bs_332_ = v___x_351_;
goto _start;
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_bs_x27_346_);
lean_dec_ref(v_ctx_x3f_329_);
v_a_353_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_347_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_347_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_328_ = stack[0].m_obj;
lean_object* v_ctx_x3f_329_ = stack[1].m_obj;
size_t v_sz_330_ = stack[2].m_num;
size_t v_i_331_ = stack[3].m_num;
lean_object* v_bs_332_ = stack[4].m_obj;
lean_object* v___y_333_ = stack[5].m_obj;
lean_object* v___y_334_ = stack[6].m_obj;
lean_object* v___y_335_ = stack[7].m_obj;
lean_object* v___y_336_ = stack[8].m_obj;
lean_object* v___y_337_ = stack[9].m_obj;
lean_object* v___y_338_ = stack[10].m_obj;
lean_object* v___y_339_ = stack[11].m_obj;
lean_object* v___y_340_ = stack[12].m_obj;
lean_object* v_res_361_;
v_res_361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_328_, v_ctx_x3f_329_, v_sz_330_, v_i_331_, v_bs_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v___x_362_, lean_object* v_ctx_x3f_363_, lean_object* v_sz_364_, lean_object* v_i_365_, lean_object* v_bs_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
size_t v_sz_boxed_376_; size_t v_i_boxed_377_; lean_object* v_res_378_; 
v_sz_boxed_376_ = lean_unbox_usize(v_sz_364_);
lean_dec(v_sz_364_);
v_i_boxed_377_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_362_, v_ctx_x3f_363_, v_sz_boxed_376_, v_i_boxed_377_, v_bs_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec_ref(v___x_362_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v___x_379_, lean_object* v_ctx_x3f_380_, lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_379_, v_ctx_x3f_380_, v_x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v___x_379_);
return v_res_391_;
}
}
lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(lean_object* v___x_392_, lean_object* v_ctx_x3f_393_, lean_object* v_t_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_root_404_; lean_object* v_tail_405_; lean_object* v_size_406_; size_t v_shift_407_; lean_object* v_tailOff_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_444_; 
v_root_404_ = lean_ctor_get(v_t_394_, 0);
v_tail_405_ = lean_ctor_get(v_t_394_, 1);
v_size_406_ = lean_ctor_get(v_t_394_, 2);
v_shift_407_ = lean_ctor_get_usize(v_t_394_, 4);
v_tailOff_408_ = lean_ctor_get(v_t_394_, 3);
v_isSharedCheck_444_ = !lean_is_exclusive(v_t_394_);
if (v_isSharedCheck_444_ == 0)
{
v___x_410_ = v_t_394_;
v_isShared_411_ = v_isSharedCheck_444_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_tailOff_408_);
lean_inc(v_size_406_);
lean_inc(v_tail_405_);
lean_inc(v_root_404_);
lean_dec(v_t_394_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_444_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; 
lean_inc_ref(v_ctx_x3f_393_);
v___x_412_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_392_, v_ctx_x3f_393_, v_root_404_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_sz_414_ = lean_array_size(v_tail_405_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_392_, v_ctx_x3f_393_, v_sz_414_, v___x_415_, v_tail_405_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_427_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_427_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_a_417_);
lean_ctor_set(v___x_410_, 0, v_a_413_);
v___x_422_ = v___x_410_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_a_417_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_size_406_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_tailOff_408_);
lean_ctor_set_usize(v_reuseFailAlloc_426_, 4, v_shift_407_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
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
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_a_413_);
lean_del_object(v___x_410_);
lean_dec(v_tailOff_408_);
lean_dec(v_size_406_);
v_a_428_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_416_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_416_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_del_object(v___x_410_);
lean_dec(v_tailOff_408_);
lean_dec(v_size_406_);
lean_dec_ref(v_tail_405_);
lean_dec_ref(v_ctx_x3f_393_);
v_a_436_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_412_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_412_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_392_ = stack[0].m_obj;
lean_object* v_ctx_x3f_393_ = stack[1].m_obj;
lean_object* v_t_394_ = stack[2].m_obj;
lean_object* v___y_395_ = stack[3].m_obj;
lean_object* v___y_396_ = stack[4].m_obj;
lean_object* v___y_397_ = stack[5].m_obj;
lean_object* v___y_398_ = stack[6].m_obj;
lean_object* v___y_399_ = stack[7].m_obj;
lean_object* v___y_400_ = stack[8].m_obj;
lean_object* v___y_401_ = stack[9].m_obj;
lean_object* v___y_402_ = stack[10].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_392_, v_ctx_x3f_393_, v_t_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5___boxed(lean_object* v___x_446_, lean_object* v_ctx_x3f_447_, lean_object* v_t_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_446_, v_ctx_x3f_447_, v_t_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec_ref(v___x_446_);
return v_res_458_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(lean_object* v___y_459_, lean_object* v_ctx_x3f_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v_a_468_, lean_object* v_a_x3f_469_){
_start:
{
lean_object* v___x_471_; lean_object* v_infoState_472_; lean_object* v_trees_473_; lean_object* v___x_474_; 
v___x_471_ = lean_st_ref_get(v___y_459_);
v_infoState_472_ = lean_ctor_get(v___x_471_, 8);
lean_inc_ref(v_infoState_472_);
lean_dec(v___x_471_);
v_trees_473_ = lean_ctor_get(v_infoState_472_, 2);
lean_inc_ref(v_trees_473_);
v___x_474_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_472_, v_ctx_x3f_460_, v_trees_473_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_459_);
lean_dec_ref(v_infoState_472_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_514_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_514_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_514_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_514_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v_infoState_480_; lean_object* v_env_481_; lean_object* v_nextMacroScope_482_; lean_object* v_ngen_483_; lean_object* v_auxDeclNGen_484_; lean_object* v_traceState_485_; lean_object* v_cache_486_; lean_object* v_recordedDeps_487_; lean_object* v_messages_488_; lean_object* v_snapshotTasks_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v___x_479_ = lean_st_ref_take(v___y_459_);
v_infoState_480_ = lean_ctor_get(v___x_479_, 8);
v_env_481_ = lean_ctor_get(v___x_479_, 0);
v_nextMacroScope_482_ = lean_ctor_get(v___x_479_, 1);
v_ngen_483_ = lean_ctor_get(v___x_479_, 2);
v_auxDeclNGen_484_ = lean_ctor_get(v___x_479_, 3);
v_traceState_485_ = lean_ctor_get(v___x_479_, 4);
v_cache_486_ = lean_ctor_get(v___x_479_, 5);
v_recordedDeps_487_ = lean_ctor_get(v___x_479_, 6);
v_messages_488_ = lean_ctor_get(v___x_479_, 7);
v_snapshotTasks_489_ = lean_ctor_get(v___x_479_, 9);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v___x_479_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snapshotTasks_489_);
lean_inc(v_infoState_480_);
lean_inc(v_messages_488_);
lean_inc(v_recordedDeps_487_);
lean_inc(v_cache_486_);
lean_inc(v_traceState_485_);
lean_inc(v_auxDeclNGen_484_);
lean_inc(v_ngen_483_);
lean_inc(v_nextMacroScope_482_);
lean_inc(v_env_481_);
lean_dec(v___x_479_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint8_t v_enabled_493_; lean_object* v_assignment_494_; lean_object* v_lazyAssignment_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_511_; 
v_enabled_493_ = lean_ctor_get_uint8(v_infoState_480_, sizeof(void*)*3);
v_assignment_494_ = lean_ctor_get(v_infoState_480_, 0);
v_lazyAssignment_495_ = lean_ctor_get(v_infoState_480_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_infoState_480_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_infoState_480_, 2);
lean_dec(v_unused_512_);
v___x_497_ = v_infoState_480_;
v_isShared_498_ = v_isSharedCheck_511_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_lazyAssignment_495_);
lean_inc(v_assignment_494_);
lean_dec(v_infoState_480_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_511_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = lean_box(0);
v___x_500_ = l_Lean_PersistentArray_append___redArg(v_a_468_, v_a_475_);
lean_dec(v_a_475_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 2, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_assignment_494_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_lazyAssignment_495_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*3, v_enabled_493_);
v___x_502_ = v_reuseFailAlloc_510_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 8, v___x_502_);
v___x_504_ = v___x_491_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_env_481_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_nextMacroScope_482_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_ngen_483_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_auxDeclNGen_484_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_traceState_485_);
lean_ctor_set(v_reuseFailAlloc_509_, 5, v_cache_486_);
lean_ctor_set(v_reuseFailAlloc_509_, 6, v_recordedDeps_487_);
lean_ctor_set(v_reuseFailAlloc_509_, 7, v_messages_488_);
lean_ctor_set(v_reuseFailAlloc_509_, 8, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 9, v_snapshotTasks_489_);
v___x_504_ = v_reuseFailAlloc_509_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_st_ref_put(v___y_459_, v___x_504_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_499_);
v___x_507_ = v___x_477_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_499_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_a_468_);
v_a_515_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_474_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_474_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_459_ = stack[0].m_obj;
lean_object* v_ctx_x3f_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v___y_462_ = stack[3].m_obj;
lean_object* v___y_463_ = stack[4].m_obj;
lean_object* v___y_464_ = stack[5].m_obj;
lean_object* v___y_465_ = stack[6].m_obj;
lean_object* v___y_466_ = stack[7].m_obj;
lean_object* v___y_467_ = stack[8].m_obj;
lean_object* v_a_468_ = stack[9].m_obj;
lean_object* v_a_x3f_469_ = stack[10].m_obj;
lean_object* v_res_523_;
v_res_523_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_459_, v_ctx_x3f_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v_a_468_, v_a_x3f_469_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_524_, lean_object* v_ctx_x3f_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v_a_533_, lean_object* v_a_x3f_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_524_, v_ctx_x3f_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v_a_533_, v_a_x3f_534_);
lean_dec(v_a_x3f_534_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_524_);
return v_res_536_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_unsigned_to_nat(32u);
v___x_538_ = lean_mk_empty_array_with_capacity(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_540_ = ((size_t)5ULL);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_unsigned_to_nat(32u);
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
v___x_544_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_545_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_543_);
lean_ctor_set(v___x_545_, 2, v___x_541_);
lean_ctor_set(v___x_545_, 3, v___x_541_);
lean_ctor_set_usize(v___x_545_, 4, v___x_540_);
return v___x_545_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; lean_object* v_infoState_549_; lean_object* v_trees_550_; lean_object* v___x_551_; lean_object* v_infoState_552_; lean_object* v_env_553_; lean_object* v_nextMacroScope_554_; lean_object* v_ngen_555_; lean_object* v_auxDeclNGen_556_; lean_object* v_traceState_557_; lean_object* v_cache_558_; lean_object* v_recordedDeps_559_; lean_object* v_messages_560_; lean_object* v_snapshotTasks_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_582_; 
v___x_548_ = lean_st_ref_get(v___y_546_);
v_infoState_549_ = lean_ctor_get(v___x_548_, 8);
lean_inc_ref(v_infoState_549_);
lean_dec(v___x_548_);
v_trees_550_ = lean_ctor_get(v_infoState_549_, 2);
lean_inc_ref(v_trees_550_);
lean_dec_ref(v_infoState_549_);
v___x_551_ = lean_st_ref_take(v___y_546_);
v_infoState_552_ = lean_ctor_get(v___x_551_, 8);
v_env_553_ = lean_ctor_get(v___x_551_, 0);
v_nextMacroScope_554_ = lean_ctor_get(v___x_551_, 1);
v_ngen_555_ = lean_ctor_get(v___x_551_, 2);
v_auxDeclNGen_556_ = lean_ctor_get(v___x_551_, 3);
v_traceState_557_ = lean_ctor_get(v___x_551_, 4);
v_cache_558_ = lean_ctor_get(v___x_551_, 5);
v_recordedDeps_559_ = lean_ctor_get(v___x_551_, 6);
v_messages_560_ = lean_ctor_get(v___x_551_, 7);
v_snapshotTasks_561_ = lean_ctor_get(v___x_551_, 9);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_582_ == 0)
{
v___x_563_ = v___x_551_;
v_isShared_564_ = v_isSharedCheck_582_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snapshotTasks_561_);
lean_inc(v_infoState_552_);
lean_inc(v_messages_560_);
lean_inc(v_recordedDeps_559_);
lean_inc(v_cache_558_);
lean_inc(v_traceState_557_);
lean_inc(v_auxDeclNGen_556_);
lean_inc(v_ngen_555_);
lean_inc(v_nextMacroScope_554_);
lean_inc(v_env_553_);
lean_dec(v___x_551_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_582_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v_enabled_565_; lean_object* v_assignment_566_; lean_object* v_lazyAssignment_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_580_; 
v_enabled_565_ = lean_ctor_get_uint8(v_infoState_552_, sizeof(void*)*3);
v_assignment_566_ = lean_ctor_get(v_infoState_552_, 0);
v_lazyAssignment_567_ = lean_ctor_get(v_infoState_552_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_infoState_552_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_infoState_552_, 2);
lean_dec(v_unused_581_);
v___x_569_ = v_infoState_552_;
v_isShared_570_ = v_isSharedCheck_580_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_lazyAssignment_567_);
lean_inc(v_assignment_566_);
lean_dec(v_infoState_552_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_580_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_assignment_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_lazyAssignment_567_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v___x_571_);
lean_ctor_set_uint8(v_reuseFailAlloc_579_, sizeof(void*)*3, v_enabled_565_);
v___x_573_ = v_reuseFailAlloc_579_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_575_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 8, v___x_573_);
v___x_575_ = v___x_563_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_env_553_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_nextMacroScope_554_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_ngen_555_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_auxDeclNGen_556_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_traceState_557_);
lean_ctor_set(v_reuseFailAlloc_578_, 5, v_cache_558_);
lean_ctor_set(v_reuseFailAlloc_578_, 6, v_recordedDeps_559_);
lean_ctor_set(v_reuseFailAlloc_578_, 7, v_messages_560_);
lean_ctor_set(v_reuseFailAlloc_578_, 8, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_578_, 9, v_snapshotTasks_561_);
v___x_575_ = v_reuseFailAlloc_578_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_st_ref_put(v___y_546_, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_trees_550_);
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_546_ = stack[0].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_546_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_584_);
lean_dec(v___y_584_);
return v_res_586_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(lean_object* v_x_587_, lean_object* v_ctx_x3f_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_infoState_599_; uint8_t v_enabled_600_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_infoState_599_ = lean_ctor_get(v___x_598_, 8);
lean_inc_ref(v_infoState_599_);
lean_dec(v___x_598_);
v_enabled_600_ = lean_ctor_get_uint8(v_infoState_599_, sizeof(void*)*3);
lean_dec_ref(v_infoState_599_);
if (v_enabled_600_ == 0)
{
lean_object* v___x_601_; 
lean_dec_ref(v_ctx_x3f_588_);
lean_inc(v___y_596_);
lean_inc_ref(v___y_595_);
lean_inc(v___y_594_);
lean_inc_ref(v___y_593_);
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
v___x_601_ = lean_apply_9(v_x_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, lean_box(0));
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v_r_604_; 
v___x_602_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_596_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
lean_inc(v___y_596_);
lean_inc_ref(v___y_595_);
lean_inc(v___y_594_);
lean_inc_ref(v___y_593_);
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
v_r_604_ = lean_apply_9(v_x_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, lean_box(0));
if (lean_obj_tag(v_r_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_629_; 
v_a_605_ = lean_ctor_get(v_r_604_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_r_604_);
if (v_isSharedCheck_629_ == 0)
{
v___x_607_ = v_r_604_;
v_isShared_608_ = v_isSharedCheck_629_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v_r_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_629_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
lean_inc(v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_628_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_596_, v_ctx_x3f_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v_a_603_, v___x_610_);
lean_dec_ref(v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_611_, 0);
lean_dec(v_unused_619_);
v___x_613_ = v___x_611_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_dec(v___x_611_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_a_605_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_605_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_a_605_);
v_a_620_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_a_630_ = lean_ctor_get(v_r_604_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v_r_604_, 1);
v___x_631_ = lean_box(0);
v___x_632_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_596_, v_ctx_x3f_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v_a_603_, v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_632_, 0);
lean_dec(v_unused_640_);
v___x_634_ = v___x_632_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___x_632_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 1);
lean_ctor_set(v___x_634_, 0, v_a_630_);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_630_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_a_630_);
v_a_641_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_632_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_632_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_587_ = stack[0].m_obj;
lean_object* v_ctx_x3f_588_ = stack[1].m_obj;
lean_object* v___y_589_ = stack[2].m_obj;
lean_object* v___y_590_ = stack[3].m_obj;
lean_object* v___y_591_ = stack[4].m_obj;
lean_object* v___y_592_ = stack[5].m_obj;
lean_object* v___y_593_ = stack[6].m_obj;
lean_object* v___y_594_ = stack[7].m_obj;
lean_object* v___y_595_ = stack[8].m_obj;
lean_object* v___y_596_ = stack[9].m_obj;
lean_object* v_res_649_;
v_res_649_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_587_, v_ctx_x3f_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___boxed(lean_object* v_x_650_, lean_object* v_ctx_x3f_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_650_, v_ctx_x3f_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_661_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; lean_object* v_env_667_; lean_object* v___x_668_; lean_object* v_toCold_669_; lean_object* v_mctx_670_; lean_object* v_currNamespace_671_; lean_object* v_openDecls_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_ngen_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_666_ = lean_st_ref_get(v___y_664_);
v_env_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc_ref(v_env_667_);
lean_dec(v___x_666_);
v___x_668_ = lean_st_ref_get(v___y_662_);
v_toCold_669_ = lean_ctor_get(v___y_663_, 0);
v_mctx_670_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_mctx_670_);
lean_dec(v___x_668_);
v_currNamespace_671_ = lean_ctor_get(v_toCold_669_, 4);
v_openDecls_672_ = lean_ctor_get(v_toCold_669_, 5);
v___x_673_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_663_);
v___x_674_ = lean_st_ref_get(v___y_664_);
v_ngen_675_ = lean_ctor_get(v___x_674_, 2);
lean_inc_ref(v_ngen_675_);
lean_dec(v___x_674_);
v___x_676_ = lean_box(0);
v___x_677_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_672_);
lean_inc(v_currNamespace_671_);
v___x_678_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_678_, 0, v_env_667_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_677_);
lean_ctor_set(v___x_678_, 3, v_mctx_670_);
lean_ctor_set(v___x_678_, 4, v___x_673_);
lean_ctor_set(v___x_678_, 5, v_currNamespace_671_);
lean_ctor_set(v___x_678_, 6, v_openDecls_672_);
lean_ctor_set(v___x_678_, 7, v_ngen_675_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_662_ = stack[0].m_obj;
lean_object* v___y_663_ = stack[1].m_obj;
lean_object* v___y_664_ = stack[2].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_662_, v___y_663_, v___y_664_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
return v_res_685_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_toCold_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_721_; 
v___x_695_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_691_, v___y_692_, v___y_693_);
v_toCold_696_ = lean_ctor_get(v___y_692_, 0);
v_a_697_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_721_ == 0)
{
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_fileMap_701_; lean_object* v_env_702_; lean_object* v_mctx_703_; lean_object* v_options_704_; lean_object* v_currNamespace_705_; lean_object* v_openDecls_706_; lean_object* v_ngen_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_718_; 
v_fileMap_701_ = lean_ctor_get(v_toCold_696_, 1);
v_env_702_ = lean_ctor_get(v_a_697_, 0);
v_mctx_703_ = lean_ctor_get(v_a_697_, 3);
v_options_704_ = lean_ctor_get(v_a_697_, 4);
v_currNamespace_705_ = lean_ctor_get(v_a_697_, 5);
v_openDecls_706_ = lean_ctor_get(v_a_697_, 6);
v_ngen_707_ = lean_ctor_get(v_a_697_, 7);
v_isSharedCheck_718_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_719_ = lean_ctor_get(v_a_697_, 2);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_a_697_, 1);
lean_dec(v_unused_720_);
v___x_709_ = v_a_697_;
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_ngen_707_);
lean_inc(v_openDecls_706_);
lean_inc(v_currNamespace_705_);
lean_inc(v_options_704_);
lean_inc(v_mctx_703_);
lean_inc(v_env_702_);
lean_dec(v_a_697_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_box(0);
lean_inc_ref(v_fileMap_701_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 2, v_fileMap_701_);
lean_ctor_set(v___x_709_, 1, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_env_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_fileMap_701_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_mctx_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_options_704_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_currNamespace_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_openDecls_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_ngen_707_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_713_);
v___x_715_ = v___x_699_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_686_ = stack[0].m_obj;
lean_object* v___y_687_ = stack[1].m_obj;
lean_object* v___y_688_ = stack[2].m_obj;
lean_object* v___y_689_ = stack[3].m_obj;
lean_object* v___y_690_ = stack[4].m_obj;
lean_object* v___y_691_ = stack[5].m_obj;
lean_object* v___y_692_ = stack[6].m_obj;
lean_object* v___y_693_ = stack[7].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0___boxed(lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_732_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_752_; 
v___x_742_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_752_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_a_743_);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_748_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_733_ = stack[0].m_obj;
lean_object* v___y_734_ = stack[1].m_obj;
lean_object* v___y_735_ = stack[2].m_obj;
lean_object* v___y_736_ = stack[3].m_obj;
lean_object* v___y_737_ = stack[4].m_obj;
lean_object* v___y_738_ = stack[5].m_obj;
lean_object* v___y_739_ = stack[6].m_obj;
lean_object* v___y_740_ = stack[7].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed(lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_763_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(lean_object* v_x_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___f_775_; lean_object* v___x_776_; 
v___f_775_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0));
v___x_776_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_765_, v___f_775_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_776_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_765_ = stack[0].m_obj;
lean_object* v___y_766_ = stack[1].m_obj;
lean_object* v___y_767_ = stack[2].m_obj;
lean_object* v___y_768_ = stack[3].m_obj;
lean_object* v___y_769_ = stack[4].m_obj;
lean_object* v___y_770_ = stack[5].m_obj;
lean_object* v___y_771_ = stack[6].m_obj;
lean_object* v___y_772_ = stack[7].m_obj;
lean_object* v___y_773_ = stack[8].m_obj;
lean_object* v_res_777_;
v_res_777_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
stack->m_obj
 = v_res_777_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_788_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(lean_object* v_00_u03b1_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_800_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_790_ = stack[1].m_obj;
lean_object* v___y_791_ = stack[2].m_obj;
lean_object* v___y_792_ = stack[3].m_obj;
lean_object* v___y_793_ = stack[4].m_obj;
lean_object* v___y_794_ = stack[5].m_obj;
lean_object* v___y_795_ = stack[6].m_obj;
lean_object* v___y_796_ = stack[7].m_obj;
lean_object* v___y_797_ = stack[8].m_obj;
lean_object* v___y_798_ = stack[9].m_obj;
lean_object* v_res_801_;
v_res_801_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(lean_box(0), v_x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
stack->m_obj
 = v_res_801_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed(lean_object* v_00_u03b1_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(v_00_u03b1_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_813_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(lean_object* v_atLocal_814_, lean_object* v_as_815_, size_t v_sz_816_, size_t v_i_817_, uint8_t v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v_a_829_; uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_817_, v_sz_816_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_atLocal_814_);
v___x_834_ = lean_box(v_b_818_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_array_uget_borrowed(v_as_815_, v_i_817_);
lean_inc(v_a_836_);
v___x_837_ = l_Lean_FVarId_getDecl___redArg(v_a_836_, v___y_823_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_LocalDecl_isImplementationDetail(v_a_838_);
lean_dec(v_a_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_inc_ref(v_atLocal_814_);
lean_inc(v_a_836_);
v___x_840_ = lean_apply_1(v_atLocal_814_, v_a_836_);
v___x_841_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_841_, 0, lean_box(0));
lean_closure_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_842_, 0, lean_box(0));
lean_closure_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_842_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_843_) == 0)
{
if (v_b_818_ == 0)
{
lean_object* v_a_844_; uint8_t v___x_845_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = lean_unbox(v_a_844_);
lean_dec(v_a_844_);
v_a_829_ = v___x_845_;
goto v___jp_828_;
}
else
{
lean_dec_ref_known(v___x_843_, 1);
v_a_829_ = v___x_833_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_atLocal_814_);
return v___x_843_;
}
}
else
{
v_a_829_ = v_b_818_;
goto v___jp_828_;
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v_atLocal_814_);
v_a_846_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_837_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_837_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
v___jp_828_:
{
size_t v___x_830_; size_t v___x_831_; 
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_817_, v___x_830_);
v_i_817_ = v___x_831_;
v_b_818_ = v_a_829_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_atLocal_814_ = stack[0].m_obj;
lean_object* v_as_815_ = stack[1].m_obj;
size_t v_sz_816_ = stack[2].m_num;
size_t v_i_817_ = stack[3].m_num;
uint8_t v_b_818_ = stack[4].m_num;
lean_object* v___y_819_ = stack[5].m_obj;
lean_object* v___y_820_ = stack[6].m_obj;
lean_object* v___y_821_ = stack[7].m_obj;
lean_object* v___y_822_ = stack[8].m_obj;
lean_object* v___y_823_ = stack[9].m_obj;
lean_object* v___y_824_ = stack[10].m_obj;
lean_object* v___y_825_ = stack[11].m_obj;
lean_object* v___y_826_ = stack[12].m_obj;
lean_object* v_res_854_;
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_814_, v_as_815_, v_sz_816_, v_i_817_, v_b_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1___boxed(lean_object* v_atLocal_855_, lean_object* v_as_856_, lean_object* v_sz_857_, lean_object* v_i_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
size_t v_sz_boxed_869_; size_t v_i_boxed_870_; uint8_t v_b_boxed_871_; lean_object* v_res_872_; 
v_sz_boxed_869_ = lean_unbox_usize(v_sz_857_);
lean_dec(v_sz_857_);
v_i_boxed_870_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_b_boxed_871_ = lean_unbox(v_b_859_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_855_, v_as_856_, v_sz_boxed_869_, v_i_boxed_870_, v_b_boxed_871_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec_ref(v_as_856_);
return v_res_872_;
}
}
lean_object* l_Lean_Elab_Tactic_withLocation___lam__0(lean_object* v_atLocal_873_, uint8_t v_a_874_, lean_object* v_failed_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_lctx_885_; lean_object* v___x_886_; lean_object* v___x_887_; size_t v_sz_888_; size_t v___x_889_; lean_object* v___x_890_; 
v_lctx_885_ = lean_ctor_get(v___y_880_, 2);
v___x_886_ = l_Lean_LocalContext_getFVarIds(v_lctx_885_);
v___x_887_ = l_Array_reverse___redArg(v___x_886_);
v_sz_888_ = lean_array_size(v___x_887_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_873_, v___x_887_, v_sz_888_, v___x_889_, v_a_874_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec_ref(v___x_887_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_911_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_911_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_911_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_911_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; 
v___x_895_ = lean_unbox(v_a_891_);
lean_dec(v_a_891_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_del_object(v___x_893_);
v___x_896_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_877_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = lean_apply_10(v_failed_875_, v_a_897_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
return v___x_898_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_failed_875_);
v_a_899_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_896_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_896_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_failed_875_);
v___x_907_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_907_);
v___x_909_ = v___x_893_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_failed_875_);
v_a_912_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_890_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_890_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_withLocation___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_atLocal_873_ = stack[0].m_obj;
uint8_t v_a_874_ = stack[1].m_num;
lean_object* v_failed_875_ = stack[2].m_obj;
lean_object* v___y_876_ = stack[3].m_obj;
lean_object* v___y_877_ = stack[4].m_obj;
lean_object* v___y_878_ = stack[5].m_obj;
lean_object* v___y_879_ = stack[6].m_obj;
lean_object* v___y_880_ = stack[7].m_obj;
lean_object* v___y_881_ = stack[8].m_obj;
lean_object* v___y_882_ = stack[9].m_obj;
lean_object* v___y_883_ = stack[10].m_obj;
lean_object* v_res_920_;
v_res_920_ = l_Lean_Elab_Tactic_withLocation___lam__0(v_atLocal_873_, v_a_874_, v_failed_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0___boxed(lean_object* v_atLocal_921_, lean_object* v_a_922_, lean_object* v_failed_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v_a_17400__boxed_933_; lean_object* v_res_934_; 
v_a_17400__boxed_933_ = lean_unbox(v_a_922_);
v_res_934_ = l_Lean_Elab_Tactic_withLocation___lam__0(v_atLocal_921_, v_a_17400__boxed_933_, v_failed_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v_res_934_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(lean_object* v___x_935_, lean_object* v_atLocal_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Elab_Tactic_getFVarId(v___x_935_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = lean_apply_10(v_atLocal_936_, v_a_947_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, lean_box(0));
return v___x_948_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_atLocal_936_);
v_a_949_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_946_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_935_ = stack[0].m_obj;
lean_object* v_atLocal_936_ = stack[1].m_obj;
lean_object* v___y_937_ = stack[2].m_obj;
lean_object* v___y_938_ = stack[3].m_obj;
lean_object* v___y_939_ = stack[4].m_obj;
lean_object* v___y_940_ = stack[5].m_obj;
lean_object* v___y_941_ = stack[6].m_obj;
lean_object* v___y_942_ = stack[7].m_obj;
lean_object* v___y_943_ = stack[8].m_obj;
lean_object* v___y_944_ = stack[9].m_obj;
lean_object* v_res_957_;
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_935_, v_atLocal_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed(lean_object* v___x_958_, lean_object* v_atLocal_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_958_, v_atLocal_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v_res_969_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(lean_object* v_atLocal_970_, lean_object* v_as_971_, size_t v_i_972_, size_t v_stop_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_eq(v_i_972_, v_stop_973_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___f_986_; lean_object* v___x_987_; 
v___x_985_ = lean_array_uget_borrowed(v_as_971_, v_i_972_);
lean_inc_ref(v_atLocal_970_);
lean_inc(v___x_985_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed), 11, 2);
lean_closure_set(v___f_986_, 0, v___x_985_);
lean_closure_set(v___f_986_, 1, v_atLocal_970_);
v___x_987_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_986_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; size_t v___x_989_; size_t v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_972_, v___x_989_);
v_i_972_ = v___x_990_;
v_b_974_ = v_a_988_;
goto _start;
}
else
{
lean_dec_ref(v_atLocal_970_);
return v___x_987_;
}
}
else
{
lean_object* v___x_992_; 
lean_dec_ref(v_atLocal_970_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_974_);
return v___x_992_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_atLocal_970_ = stack[0].m_obj;
lean_object* v_as_971_ = stack[1].m_obj;
size_t v_i_972_ = stack[2].m_num;
size_t v_stop_973_ = stack[3].m_num;
lean_object* v_b_974_ = stack[4].m_obj;
lean_object* v___y_975_ = stack[5].m_obj;
lean_object* v___y_976_ = stack[6].m_obj;
lean_object* v___y_977_ = stack[7].m_obj;
lean_object* v___y_978_ = stack[8].m_obj;
lean_object* v___y_979_ = stack[9].m_obj;
lean_object* v___y_980_ = stack[10].m_obj;
lean_object* v___y_981_ = stack[11].m_obj;
lean_object* v___y_982_ = stack[12].m_obj;
lean_object* v_res_993_;
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_970_, v_as_971_, v_i_972_, v_stop_973_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
stack->m_obj
 = v_res_993_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(lean_object* v_atLocal_994_, lean_object* v_as_995_, lean_object* v_i_996_, lean_object* v_stop_997_, lean_object* v_b_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
size_t v_i_boxed_1008_; size_t v_stop_boxed_1009_; lean_object* v_res_1010_; 
v_i_boxed_1008_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_stop_boxed_1009_ = lean_unbox_usize(v_stop_997_);
lean_dec(v_stop_997_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_994_, v_as_995_, v_i_boxed_1008_, v_stop_boxed_1009_, v_b_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec_ref(v_as_995_);
return v_res_1010_;
}
}
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object* v_loc_1011_, lean_object* v_atLocal_1012_, lean_object* v_atTarget_1013_, lean_object* v_failed_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
if (lean_obj_tag(v_loc_1011_) == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_1024_, 0, lean_box(0));
lean_closure_set(v___x_1024_, 1, v_atTarget_1013_);
v___x_1025_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_1025_, 0, lean_box(0));
lean_closure_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_1025_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withLocation___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1028_, 0, v_atLocal_1012_);
lean_closure_set(v___f_1028_, 1, v_a_1027_);
lean_closure_set(v___f_1028_, 2, v_failed_1014_);
v___x_1029_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1016_, v_a_1018_, v_a_1020_, v_a_1022_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1016_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
lean_dec(v_a_1030_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_1032_, v___f_1028_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1033_;
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___f_1028_);
v_a_1034_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1036_ = v___x_1031_;
v_isShared_1037_ = v_isSharedCheck_1055_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1031_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1055_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___y_1039_; uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Exception_isInterrupt(v_a_1034_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
lean_inc(v_a_1034_);
v___x_1054_ = l_Lean_Exception_isRuntime(v_a_1034_);
v___y_1039_ = v___x_1054_;
goto v___jp_1038_;
}
else
{
v___y_1039_ = v___x_1053_;
goto v___jp_1038_;
}
v___jp_1038_:
{
if (v___y_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_del_object(v___x_1036_);
lean_dec(v_a_1034_);
v___x_1040_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1030_, v___y_1039_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1040_, 0);
lean_dec(v_unused_1049_);
v___x_1042_ = v___x_1040_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v___x_1040_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_box(0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
return v___x_1040_;
}
}
else
{
lean_object* v___x_1051_; 
lean_dec(v_a_1030_);
if (v_isShared_1037_ == 0)
{
v___x_1051_ = v___x_1036_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1034_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v___f_1028_);
v_a_1056_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1029_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1029_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_failed_1014_);
lean_dec_ref(v_atLocal_1012_);
v_a_1064_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1026_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1026_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_hypotheses_1072_; uint8_t v_type_1073_; lean_object* v___y_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
lean_dec_ref(v_failed_1014_);
v_hypotheses_1072_ = lean_ctor_get(v_loc_1011_, 0);
v_type_1073_ = lean_ctor_get_uint8(v_loc_1011_, sizeof(void*)*1);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_array_get_size(v_hypotheses_1072_);
v___x_1082_ = lean_nat_dec_lt(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v_atLocal_1012_);
goto v___jp_1074_;
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_nat_dec_le(v___x_1081_, v___x_1081_);
if (v___x_1084_ == 0)
{
if (v___x_1082_ == 0)
{
lean_dec_ref(v_atLocal_1012_);
goto v___jp_1074_;
}
else
{
size_t v___x_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = lean_usize_of_nat(v___x_1081_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_1012_, v_hypotheses_1072_, v___x_1085_, v___x_1086_, v___x_1083_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1079_ = v___x_1087_;
goto v___jp_1078_;
}
}
else
{
size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1081_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_1012_, v_hypotheses_1072_, v___x_1088_, v___x_1089_, v___x_1083_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1079_ = v___x_1090_;
goto v___jp_1078_;
}
}
v___jp_1074_:
{
if (v_type_1073_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_atTarget_1013_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Elab_Tactic_withMainContext___redArg(v_atTarget_1013_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1077_;
}
}
v___jp_1078_:
{
if (lean_obj_tag(v___y_1079_) == 0)
{
lean_dec_ref_known(v___y_1079_, 1);
goto v___jp_1074_;
}
else
{
lean_dec_ref(v_atTarget_1013_);
return v___y_1079_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_withLocation_0interp(lean_interpreter_value* stack)
{
lean_object* v_loc_1011_ = stack[0].m_obj;
lean_object* v_atLocal_1012_ = stack[1].m_obj;
lean_object* v_atTarget_1013_ = stack[2].m_obj;
lean_object* v_failed_1014_ = stack[3].m_obj;
lean_object* v_a_1015_ = stack[4].m_obj;
lean_object* v_a_1016_ = stack[5].m_obj;
lean_object* v_a_1017_ = stack[6].m_obj;
lean_object* v_a_1018_ = stack[7].m_obj;
lean_object* v_a_1019_ = stack[8].m_obj;
lean_object* v_a_1020_ = stack[9].m_obj;
lean_object* v_a_1021_ = stack[10].m_obj;
lean_object* v_a_1022_ = stack[11].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Lean_Elab_Tactic_withLocation(v_loc_1011_, v_atLocal_1012_, v_atTarget_1013_, v_failed_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___boxed(lean_object* v_loc_1092_, lean_object* v_atLocal_1093_, lean_object* v_atTarget_1094_, lean_object* v_failed_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Elab_Tactic_withLocation(v_loc_1092_, v_atLocal_1093_, v_atTarget_1094_, v_failed_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_loc_1092_);
return v_res_1105_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1106_ = stack[0].m_obj;
lean_object* v___y_1107_ = stack[1].m_obj;
lean_object* v___y_1108_ = stack[2].m_obj;
lean_object* v___y_1109_ = stack[3].m_obj;
lean_object* v___y_1110_ = stack[4].m_obj;
lean_object* v___y_1111_ = stack[5].m_obj;
lean_object* v___y_1112_ = stack[6].m_obj;
lean_object* v___y_1113_ = stack[7].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1126_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1127_ = stack[0].m_obj;
lean_object* v___y_1128_ = stack[1].m_obj;
lean_object* v___y_1129_ = stack[2].m_obj;
lean_object* v___y_1130_ = stack[3].m_obj;
lean_object* v___y_1131_ = stack[4].m_obj;
lean_object* v___y_1132_ = stack[5].m_obj;
lean_object* v___y_1133_ = stack[6].m_obj;
lean_object* v___y_1134_ = stack[7].m_obj;
lean_object* v_res_1137_;
v_res_1137_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
stack->m_obj
 = v_res_1137_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1147_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(lean_object* v_00_u03b1_1148_, lean_object* v_x_1149_, lean_object* v_ctx_x3f_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1149_, v_ctx_x3f_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1149_ = stack[1].m_obj;
lean_object* v_ctx_x3f_1150_ = stack[2].m_obj;
lean_object* v___y_1151_ = stack[3].m_obj;
lean_object* v___y_1152_ = stack[4].m_obj;
lean_object* v___y_1153_ = stack[5].m_obj;
lean_object* v___y_1154_ = stack[6].m_obj;
lean_object* v___y_1155_ = stack[7].m_obj;
lean_object* v___y_1156_ = stack[8].m_obj;
lean_object* v___y_1157_ = stack[9].m_obj;
lean_object* v___y_1158_ = stack[10].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(lean_box(0), v_x_1149_, v_ctx_x3f_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_x_1163_, lean_object* v_ctx_x3f_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_1162_, v_x_1163_, v_ctx_x3f_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1174_;
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
