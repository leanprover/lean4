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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(uint8_t v___x_49_, lean_object* v_as_50_, size_t v_i_51_, size_t v_stop_52_, lean_object* v_b_53_){
_start:
{
lean_object* v___y_55_; uint8_t v___x_59_; 
v___x_59_ = lean_usize_dec_eq(v_i_51_, v_stop_52_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_60_ = lean_array_uget_borrowed(v_as_50_, v_i_51_);
lean_inc(v___x_60_);
v___x_61_ = l_Lean_Syntax_getKind(v___x_60_);
v___x_62_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4));
v___x_63_ = lean_name_eq(v___x_61_, v___x_62_);
lean_dec(v___x_61_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_inc(v___x_60_);
v___x_64_ = lean_array_push(v_b_53_, v___x_60_);
v___y_55_ = v___x_64_;
goto v___jp_54_;
}
else
{
if (v___x_49_ == 0)
{
v___y_55_ = v_b_53_;
goto v___jp_54_;
}
else
{
lean_object* v___x_65_; 
lean_inc(v___x_60_);
v___x_65_ = lean_array_push(v_b_53_, v___x_60_);
v___y_55_ = v___x_65_;
goto v___jp_54_;
}
}
}
else
{
return v_b_53_;
}
v___jp_54_:
{
size_t v___x_56_; size_t v___x_57_; 
v___x_56_ = ((size_t)1ULL);
v___x_57_ = lean_usize_add(v_i_51_, v___x_56_);
v_i_51_ = v___x_57_;
v_b_53_ = v___y_55_;
goto _start;
}
}
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(lean_object* v_x_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(lean_object* v_x_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(v_x_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(lean_object* v_mvarId_142_, lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; 
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
v___f_153_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_153_, 0, v_x_143_);
lean_closure_set(v___f_153_, 1, v___y_144_);
lean_closure_set(v___f_153_, 2, v___y_145_);
lean_closure_set(v___f_153_, 3, v___y_146_);
lean_closure_set(v___f_153_, 4, v___y_147_);
v___x_154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_142_, v___f_153_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
if (lean_obj_tag(v___x_154_) == 0)
{
return v___x_154_;
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___boxed(lean_object* v_mvarId_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_163_, v_x_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(lean_object* v_00_u03b1_175_, lean_object* v_mvarId_176_, lean_object* v_x_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_mvarId_176_, v_x_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___boxed(lean_object* v_00_u03b1_188_, lean_object* v_mvarId_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(v_00_u03b1_188_, v_mvarId_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(lean_object* v___x_201_, lean_object* v_ctx_x3f_202_, size_t v_sz_203_, size_t v_i_204_, lean_object* v_bs_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = lean_usize_dec_lt(v_i_204_, v_sz_203_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_ctx_x3f_202_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v_bs_205_);
return v___x_216_;
}
else
{
lean_object* v_assignment_217_; lean_object* v_v_218_; lean_object* v___x_219_; lean_object* v_bs_x27_220_; lean_object* v_a_222_; lean_object* v_tree_227_; lean_object* v___x_228_; 
v_assignment_217_ = lean_ctor_get(v___x_201_, 0);
v_v_218_ = lean_array_uget(v_bs_205_, v_i_204_);
v___x_219_ = lean_unsigned_to_nat(0u);
v_bs_x27_220_ = lean_array_uset(v_bs_205_, v_i_204_, v___x_219_);
v_tree_227_ = l_Lean_Elab_InfoTree_substitute(v_v_218_, v_assignment_217_);
lean_inc_ref(v_ctx_x3f_202_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
v___x_228_ = lean_apply_9(v_ctx_x3f_202_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, lean_box(0));
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
if (lean_obj_tag(v_a_229_) == 0)
{
v_a_222_ = v_tree_227_;
goto v___jp_221_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
v_val_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v_a_229_, 1);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_val_230_);
lean_ctor_set(v___x_231_, 1, v_tree_227_);
v_a_222_ = v___x_231_;
goto v___jp_221_;
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v_tree_227_);
lean_dec_ref(v_bs_x27_220_);
lean_dec_ref(v_ctx_x3f_202_);
v_a_232_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_228_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_228_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
v___jp_221_:
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_add(v_i_204_, v___x_223_);
v___x_225_ = lean_array_uset(v_bs_x27_220_, v_i_204_, v_a_222_);
v_i_204_ = v___x_224_;
v_bs_205_ = v___x_225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v___x_240_, lean_object* v_ctx_x3f_241_, lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_bs_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
size_t v_sz_boxed_254_; size_t v_i_boxed_255_; lean_object* v_res_256_; 
v_sz_boxed_254_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_255_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_240_, v_ctx_x3f_241_, v_sz_boxed_254_, v_i_boxed_255_, v_bs_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec_ref(v___x_240_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(lean_object* v___x_257_, lean_object* v_ctx_x3f_258_, lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_cs_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_295_; 
v_cs_269_ = lean_ctor_get(v_x_259_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_295_ == 0)
{
v___x_271_ = v_x_259_;
v_isShared_272_ = v_isSharedCheck_295_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_cs_269_);
lean_dec(v_x_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_295_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
size_t v_sz_273_; size_t v___x_274_; lean_object* v___x_275_; 
v_sz_273_ = lean_array_size(v_cs_269_);
v___x_274_ = ((size_t)0ULL);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_257_, v_ctx_x3f_258_, v_sz_273_, v___x_274_, v_cs_269_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v_a_276_);
v___x_281_ = v___x_271_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_285_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_283_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_281_);
v___x_283_ = v___x_278_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
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
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_del_object(v___x_271_);
v_a_287_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_275_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_275_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_vs_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_322_; 
v_vs_296_ = lean_ctor_get(v_x_259_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_322_ == 0)
{
v___x_298_ = v_x_259_;
v_isShared_299_ = v_isSharedCheck_322_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_vs_296_);
lean_dec(v_x_259_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_322_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
size_t v_sz_300_; size_t v___x_301_; lean_object* v___x_302_; 
v_sz_300_ = lean_array_size(v_vs_296_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_257_, v_ctx_x3f_258_, v_sz_300_, v___x_301_, v_vs_296_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_313_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_a_303_);
v___x_308_ = v___x_298_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
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
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_del_object(v___x_298_);
v_a_314_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_302_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_302_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v___x_323_, lean_object* v_ctx_x3f_324_, size_t v_sz_325_, size_t v_i_326_, lean_object* v_bs_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec_ref(v_ctx_x3f_324_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_bs_327_);
return v___x_338_;
}
else
{
lean_object* v_v_339_; lean_object* v___x_340_; lean_object* v_bs_x27_341_; lean_object* v___x_342_; 
v_v_339_ = lean_array_uget(v_bs_327_, v_i_326_);
v___x_340_ = lean_unsigned_to_nat(0u);
v_bs_x27_341_ = lean_array_uset(v_bs_327_, v_i_326_, v___x_340_);
lean_inc_ref(v_ctx_x3f_324_);
v___x_342_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_323_, v_ctx_x3f_324_, v_v_339_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_add(v_i_326_, v___x_344_);
v___x_346_ = lean_array_uset(v_bs_x27_341_, v_i_326_, v_a_343_);
v_i_326_ = v___x_345_;
v_bs_327_ = v___x_346_;
goto _start;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_bs_x27_341_);
lean_dec_ref(v_ctx_x3f_324_);
v_a_348_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_342_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_342_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v___x_356_, lean_object* v_ctx_x3f_357_, lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_bs_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_371_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_356_, v_ctx_x3f_357_, v_sz_boxed_370_, v_i_boxed_371_, v_bs_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v___x_356_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v___x_373_, lean_object* v_ctx_x3f_374_, lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_373_, v_ctx_x3f_374_, v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec_ref(v___x_373_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(lean_object* v___x_386_, lean_object* v_ctx_x3f_387_, lean_object* v_t_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_root_398_; lean_object* v_tail_399_; lean_object* v_size_400_; size_t v_shift_401_; lean_object* v_tailOff_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_438_; 
v_root_398_ = lean_ctor_get(v_t_388_, 0);
v_tail_399_ = lean_ctor_get(v_t_388_, 1);
v_size_400_ = lean_ctor_get(v_t_388_, 2);
v_shift_401_ = lean_ctor_get_usize(v_t_388_, 4);
v_tailOff_402_ = lean_ctor_get(v_t_388_, 3);
v_isSharedCheck_438_ = !lean_is_exclusive(v_t_388_);
if (v_isSharedCheck_438_ == 0)
{
v___x_404_ = v_t_388_;
v_isShared_405_ = v_isSharedCheck_438_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_tailOff_402_);
lean_inc(v_size_400_);
lean_inc(v_tail_399_);
lean_inc(v_root_398_);
lean_dec(v_t_388_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_438_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; 
lean_inc_ref(v_ctx_x3f_387_);
v___x_406_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_386_, v_ctx_x3f_387_, v_root_398_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; size_t v_sz_408_; size_t v___x_409_; lean_object* v___x_410_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v_sz_408_ = lean_array_size(v_tail_399_);
v___x_409_ = ((size_t)0ULL);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_386_, v_ctx_x3f_387_, v_sz_408_, v___x_409_, v_tail_399_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_421_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_a_411_);
lean_ctor_set(v___x_404_, 0, v_a_407_);
v___x_416_ = v___x_404_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_407_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_a_411_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_size_400_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_tailOff_402_);
lean_ctor_set_usize(v_reuseFailAlloc_420_, 4, v_shift_401_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_416_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
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
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_407_);
lean_del_object(v___x_404_);
lean_dec(v_tailOff_402_);
lean_dec(v_size_400_);
v_a_422_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_410_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_410_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_del_object(v___x_404_);
lean_dec(v_tailOff_402_);
lean_dec(v_size_400_);
lean_dec_ref(v_tail_399_);
lean_dec_ref(v_ctx_x3f_387_);
v_a_430_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_406_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_406_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5___boxed(lean_object* v___x_439_, lean_object* v_ctx_x3f_440_, lean_object* v_t_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_439_, v_ctx_x3f_440_, v_t_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec_ref(v___x_439_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(lean_object* v___y_452_, lean_object* v_ctx_x3f_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v_a_461_, lean_object* v_a_x3f_462_){
_start:
{
lean_object* v___x_464_; lean_object* v_infoState_465_; lean_object* v_trees_466_; lean_object* v___x_467_; 
v___x_464_ = lean_st_ref_get(v___y_452_);
v_infoState_465_ = lean_ctor_get(v___x_464_, 8);
lean_inc_ref(v_infoState_465_);
lean_dec(v___x_464_);
v_trees_466_ = lean_ctor_get(v_infoState_465_, 2);
lean_inc_ref(v_trees_466_);
v___x_467_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_465_, v_ctx_x3f_453_, v_trees_466_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_452_);
lean_dec_ref(v_infoState_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_507_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_507_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_507_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_507_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v_infoState_473_; lean_object* v_env_474_; lean_object* v_nextMacroScope_475_; lean_object* v_ngen_476_; lean_object* v_auxDeclNGen_477_; lean_object* v_traceState_478_; lean_object* v_cache_479_; lean_object* v_recordedDeps_480_; lean_object* v_messages_481_; lean_object* v_snapshotTasks_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_506_; 
v___x_472_ = lean_st_ref_take(v___y_452_);
v_infoState_473_ = lean_ctor_get(v___x_472_, 8);
v_env_474_ = lean_ctor_get(v___x_472_, 0);
v_nextMacroScope_475_ = lean_ctor_get(v___x_472_, 1);
v_ngen_476_ = lean_ctor_get(v___x_472_, 2);
v_auxDeclNGen_477_ = lean_ctor_get(v___x_472_, 3);
v_traceState_478_ = lean_ctor_get(v___x_472_, 4);
v_cache_479_ = lean_ctor_get(v___x_472_, 5);
v_recordedDeps_480_ = lean_ctor_get(v___x_472_, 6);
v_messages_481_ = lean_ctor_get(v___x_472_, 7);
v_snapshotTasks_482_ = lean_ctor_get(v___x_472_, 9);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_506_ == 0)
{
v___x_484_ = v___x_472_;
v_isShared_485_ = v_isSharedCheck_506_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snapshotTasks_482_);
lean_inc(v_infoState_473_);
lean_inc(v_messages_481_);
lean_inc(v_recordedDeps_480_);
lean_inc(v_cache_479_);
lean_inc(v_traceState_478_);
lean_inc(v_auxDeclNGen_477_);
lean_inc(v_ngen_476_);
lean_inc(v_nextMacroScope_475_);
lean_inc(v_env_474_);
lean_dec(v___x_472_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_506_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v_enabled_486_; lean_object* v_assignment_487_; lean_object* v_lazyAssignment_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_504_; 
v_enabled_486_ = lean_ctor_get_uint8(v_infoState_473_, sizeof(void*)*3);
v_assignment_487_ = lean_ctor_get(v_infoState_473_, 0);
v_lazyAssignment_488_ = lean_ctor_get(v_infoState_473_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_infoState_473_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_infoState_473_, 2);
lean_dec(v_unused_505_);
v___x_490_ = v_infoState_473_;
v_isShared_491_ = v_isSharedCheck_504_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_lazyAssignment_488_);
lean_inc(v_assignment_487_);
lean_dec(v_infoState_473_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_504_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = lean_box(0);
v___x_493_ = l_Lean_PersistentArray_append___redArg(v_a_461_, v_a_468_);
lean_dec(v_a_468_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 2, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_assignment_487_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_lazyAssignment_488_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v___x_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_503_, sizeof(void*)*3, v_enabled_486_);
v___x_495_ = v_reuseFailAlloc_503_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 8, v___x_495_);
v___x_497_ = v___x_484_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_env_474_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_nextMacroScope_475_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_ngen_476_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_auxDeclNGen_477_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_traceState_478_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_cache_479_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_recordedDeps_480_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_messages_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_502_, 9, v_snapshotTasks_482_);
v___x_497_ = v_reuseFailAlloc_502_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_st_ref_put(v___y_452_, v___x_497_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_492_);
v___x_500_ = v___x_470_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_492_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_a_461_);
v_a_508_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_467_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_467_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_516_, lean_object* v_ctx_x3f_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v_a_525_, lean_object* v_a_x3f_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_516_, v_ctx_x3f_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v_a_525_, v_a_x3f_526_);
lean_dec(v_a_x3f_526_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_516_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_unsigned_to_nat(32u);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_532_ = ((size_t)5ULL);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_unsigned_to_nat(32u);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_537_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_533_);
lean_ctor_set(v___x_537_, 3, v___x_533_);
lean_ctor_set_usize(v___x_537_, 4, v___x_532_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; lean_object* v_infoState_541_; lean_object* v_trees_542_; lean_object* v___x_543_; lean_object* v_infoState_544_; lean_object* v_env_545_; lean_object* v_nextMacroScope_546_; lean_object* v_ngen_547_; lean_object* v_auxDeclNGen_548_; lean_object* v_traceState_549_; lean_object* v_cache_550_; lean_object* v_recordedDeps_551_; lean_object* v_messages_552_; lean_object* v_snapshotTasks_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_574_; 
v___x_540_ = lean_st_ref_get(v___y_538_);
v_infoState_541_ = lean_ctor_get(v___x_540_, 8);
lean_inc_ref(v_infoState_541_);
lean_dec(v___x_540_);
v_trees_542_ = lean_ctor_get(v_infoState_541_, 2);
lean_inc_ref(v_trees_542_);
lean_dec_ref(v_infoState_541_);
v___x_543_ = lean_st_ref_take(v___y_538_);
v_infoState_544_ = lean_ctor_get(v___x_543_, 8);
v_env_545_ = lean_ctor_get(v___x_543_, 0);
v_nextMacroScope_546_ = lean_ctor_get(v___x_543_, 1);
v_ngen_547_ = lean_ctor_get(v___x_543_, 2);
v_auxDeclNGen_548_ = lean_ctor_get(v___x_543_, 3);
v_traceState_549_ = lean_ctor_get(v___x_543_, 4);
v_cache_550_ = lean_ctor_get(v___x_543_, 5);
v_recordedDeps_551_ = lean_ctor_get(v___x_543_, 6);
v_messages_552_ = lean_ctor_get(v___x_543_, 7);
v_snapshotTasks_553_ = lean_ctor_get(v___x_543_, 9);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_574_ == 0)
{
v___x_555_ = v___x_543_;
v_isShared_556_ = v_isSharedCheck_574_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snapshotTasks_553_);
lean_inc(v_infoState_544_);
lean_inc(v_messages_552_);
lean_inc(v_recordedDeps_551_);
lean_inc(v_cache_550_);
lean_inc(v_traceState_549_);
lean_inc(v_auxDeclNGen_548_);
lean_inc(v_ngen_547_);
lean_inc(v_nextMacroScope_546_);
lean_inc(v_env_545_);
lean_dec(v___x_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_574_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
uint8_t v_enabled_557_; lean_object* v_assignment_558_; lean_object* v_lazyAssignment_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_572_; 
v_enabled_557_ = lean_ctor_get_uint8(v_infoState_544_, sizeof(void*)*3);
v_assignment_558_ = lean_ctor_get(v_infoState_544_, 0);
v_lazyAssignment_559_ = lean_ctor_get(v_infoState_544_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_infoState_544_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v_infoState_544_, 2);
lean_dec(v_unused_573_);
v___x_561_ = v_infoState_544_;
v_isShared_562_ = v_isSharedCheck_572_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_lazyAssignment_559_);
lean_inc(v_assignment_558_);
lean_dec(v_infoState_544_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_572_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 2, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_assignment_558_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_lazyAssignment_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v___x_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*3, v_enabled_557_);
v___x_565_ = v_reuseFailAlloc_571_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 8, v___x_565_);
v___x_567_ = v___x_555_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_env_545_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_nextMacroScope_546_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_ngen_547_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_auxDeclNGen_548_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_traceState_549_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_cache_550_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_recordedDeps_551_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_messages_552_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_570_, 9, v_snapshotTasks_553_);
v___x_567_ = v_reuseFailAlloc_570_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_st_ref_put(v___y_538_, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v_trees_542_);
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_575_);
lean_dec(v___y_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(lean_object* v_x_578_, lean_object* v_ctx_x3f_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v_infoState_590_; uint8_t v_enabled_591_; 
v___x_589_ = lean_st_ref_get(v___y_587_);
v_infoState_590_ = lean_ctor_get(v___x_589_, 8);
lean_inc_ref(v_infoState_590_);
lean_dec(v___x_589_);
v_enabled_591_ = lean_ctor_get_uint8(v_infoState_590_, sizeof(void*)*3);
lean_dec_ref(v_infoState_590_);
if (v_enabled_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec_ref(v_ctx_x3f_579_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v___x_592_ = lean_apply_9(v_x_578_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, lean_box(0));
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v_r_595_; 
v___x_593_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_587_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v___x_593_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v_r_595_ = lean_apply_9(v_x_578_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, lean_box(0));
if (lean_obj_tag(v_r_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_620_; 
v_a_596_ = lean_ctor_get(v_r_595_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_r_595_);
if (v_isSharedCheck_620_ == 0)
{
v___x_598_ = v_r_595_;
v_isShared_599_ = v_isSharedCheck_620_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v_r_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_620_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
lean_inc(v_a_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 1);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_619_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_587_, v_ctx_x3f_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v_a_594_, v___x_601_);
lean_dec_ref(v___x_601_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_602_, 0);
lean_dec(v_unused_610_);
v___x_604_ = v___x_602_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_dec(v___x_602_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_a_596_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_596_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_596_);
v_a_611_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_602_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_621_ = lean_ctor_get(v_r_595_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v_r_595_, 1);
v___x_622_ = lean_box(0);
v___x_623_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_587_, v_ctx_x3f_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v_a_594_, v___x_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_623_, 0);
lean_dec(v_unused_631_);
v___x_625_ = v___x_623_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_dec(v___x_623_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 1);
lean_ctor_set(v___x_625_, 0, v_a_621_);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_621_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_a_621_);
v_a_632_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_623_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_623_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___boxed(lean_object* v_x_640_, lean_object* v_ctx_x3f_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_640_, v_ctx_x3f_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v_env_657_; lean_object* v___x_658_; lean_object* v_toCold_659_; lean_object* v_mctx_660_; lean_object* v_currNamespace_661_; lean_object* v_openDecls_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_ngen_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_656_ = lean_st_ref_get(v___y_654_);
v_env_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_ref(v_env_657_);
lean_dec(v___x_656_);
v___x_658_ = lean_st_ref_get(v___y_652_);
v_toCold_659_ = lean_ctor_get(v___y_653_, 0);
v_mctx_660_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_mctx_660_);
lean_dec(v___x_658_);
v_currNamespace_661_ = lean_ctor_get(v_toCold_659_, 4);
v_openDecls_662_ = lean_ctor_get(v_toCold_659_, 5);
v___x_663_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_653_);
v___x_664_ = lean_st_ref_get(v___y_654_);
v_ngen_665_ = lean_ctor_get(v___x_664_, 2);
lean_inc_ref(v_ngen_665_);
lean_dec(v___x_664_);
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_662_);
lean_inc(v_currNamespace_661_);
v___x_668_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_668_, 0, v_env_657_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
lean_ctor_set(v___x_668_, 2, v___x_667_);
lean_ctor_set(v___x_668_, 3, v_mctx_660_);
lean_ctor_set(v___x_668_, 4, v___x_663_);
lean_ctor_set(v___x_668_, 5, v_currNamespace_661_);
lean_ctor_set(v___x_668_, 6, v_openDecls_662_);
lean_ctor_set(v___x_668_, 7, v_ngen_665_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v_toCold_685_; lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_710_; 
v___x_684_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_680_, v___y_681_, v___y_682_);
v_toCold_685_ = lean_ctor_get(v___y_681_, 0);
v_a_686_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_710_ == 0)
{
v___x_688_ = v___x_684_;
v_isShared_689_ = v_isSharedCheck_710_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_710_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fileMap_690_; lean_object* v_env_691_; lean_object* v_mctx_692_; lean_object* v_options_693_; lean_object* v_currNamespace_694_; lean_object* v_openDecls_695_; lean_object* v_ngen_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_707_; 
v_fileMap_690_ = lean_ctor_get(v_toCold_685_, 1);
v_env_691_ = lean_ctor_get(v_a_686_, 0);
v_mctx_692_ = lean_ctor_get(v_a_686_, 3);
v_options_693_ = lean_ctor_get(v_a_686_, 4);
v_currNamespace_694_ = lean_ctor_get(v_a_686_, 5);
v_openDecls_695_ = lean_ctor_get(v_a_686_, 6);
v_ngen_696_ = lean_ctor_get(v_a_686_, 7);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_686_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_708_ = lean_ctor_get(v_a_686_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_a_686_, 1);
lean_dec(v_unused_709_);
v___x_698_ = v_a_686_;
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_ngen_696_);
lean_inc(v_openDecls_695_);
lean_inc(v_currNamespace_694_);
lean_inc(v_options_693_);
lean_inc(v_mctx_692_);
lean_inc(v_env_691_);
lean_dec(v_a_686_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
lean_inc_ref(v_fileMap_690_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v_fileMap_690_);
lean_ctor_set(v___x_698_, 1, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_env_691_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_fileMap_690_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_mctx_692_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_options_693_);
lean_ctor_set(v_reuseFailAlloc_706_, 5, v_currNamespace_694_);
lean_ctor_set(v_reuseFailAlloc_706_, 6, v_openDecls_695_);
lean_ctor_set(v_reuseFailAlloc_706_, 7, v_ngen_696_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_702_);
v___x_704_ = v___x_688_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0___boxed(lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_740_; 
v___x_730_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_740_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v_a_731_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_736_);
v___x_738_ = v___x_733_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed(lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___f_762_; lean_object* v___x_763_; 
v___f_762_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0));
v___x_763_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_752_, v___f_762_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(lean_object* v_00_u03b1_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(v_x_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed(lean_object* v_00_u03b1_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(v_00_u03b1_787_, v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(lean_object* v_atLocal_799_, lean_object* v_as_800_, size_t v_sz_801_, size_t v_i_802_, uint8_t v_b_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v_a_814_; uint8_t v___x_818_; 
v___x_818_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v_atLocal_799_);
v___x_819_ = lean_box(v_b_803_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_array_uget_borrowed(v_as_800_, v_i_802_);
lean_inc(v_a_821_);
v___x_822_ = l_Lean_FVarId_getDecl___redArg(v_a_821_, v___y_808_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; uint8_t v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = l_Lean_LocalDecl_isImplementationDetail(v_a_823_);
lean_dec(v_a_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_inc_ref(v_atLocal_799_);
lean_inc(v_a_821_);
v___x_825_ = lean_apply_1(v_atLocal_799_, v_a_821_);
v___x_826_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_826_, 0, lean_box(0));
lean_closure_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_827_, 0, lean_box(0));
lean_closure_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_827_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_828_) == 0)
{
if (v_b_803_ == 0)
{
lean_object* v_a_829_; uint8_t v___x_830_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
v___x_830_ = lean_unbox(v_a_829_);
lean_dec(v_a_829_);
v_a_814_ = v___x_830_;
goto v___jp_813_;
}
else
{
lean_dec_ref_known(v___x_828_, 1);
v_a_814_ = v___x_818_;
goto v___jp_813_;
}
}
else
{
lean_dec_ref(v_atLocal_799_);
return v___x_828_;
}
}
else
{
v_a_814_ = v_b_803_;
goto v___jp_813_;
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_atLocal_799_);
v_a_831_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_822_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_822_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
v___jp_813_:
{
size_t v___x_815_; size_t v___x_816_; 
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_802_, v___x_815_);
v_i_802_ = v___x_816_;
v_b_803_ = v_a_814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1___boxed(lean_object* v_atLocal_839_, lean_object* v_as_840_, lean_object* v_sz_841_, lean_object* v_i_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
size_t v_sz_boxed_853_; size_t v_i_boxed_854_; uint8_t v_b_boxed_855_; lean_object* v_res_856_; 
v_sz_boxed_853_ = lean_unbox_usize(v_sz_841_);
lean_dec(v_sz_841_);
v_i_boxed_854_ = lean_unbox_usize(v_i_842_);
lean_dec(v_i_842_);
v_b_boxed_855_ = lean_unbox(v_b_843_);
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_839_, v_as_840_, v_sz_boxed_853_, v_i_boxed_854_, v_b_boxed_855_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_as_840_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0(lean_object* v_atLocal_857_, uint8_t v_a_858_, lean_object* v_failed_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_lctx_869_; lean_object* v___x_870_; lean_object* v___x_871_; size_t v_sz_872_; size_t v___x_873_; lean_object* v___x_874_; 
v_lctx_869_ = lean_ctor_get(v___y_864_, 2);
v___x_870_ = l_Lean_LocalContext_getFVarIds(v_lctx_869_);
v___x_871_ = l_Array_reverse___redArg(v___x_870_);
v_sz_872_ = lean_array_size(v___x_871_);
v___x_873_ = ((size_t)0ULL);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_857_, v___x_871_, v_sz_872_, v___x_873_, v_a_858_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec_ref(v___x_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_895_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_895_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_895_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_895_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___x_879_; 
v___x_879_ = lean_unbox(v_a_875_);
lean_dec(v_a_875_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_del_object(v___x_877_);
v___x_880_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_861_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = lean_apply_10(v_failed_859_, v_a_881_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec_ref(v_failed_859_);
v_a_883_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_880_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_893_; 
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec_ref(v_failed_859_);
v___x_891_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_891_);
v___x_893_ = v___x_877_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec_ref(v_failed_859_);
v_a_896_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_874_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_874_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___lam__0___boxed(lean_object* v_atLocal_904_, lean_object* v_a_905_, lean_object* v_failed_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v_a_16895__boxed_916_; lean_object* v_res_917_; 
v_a_16895__boxed_916_ = lean_unbox(v_a_905_);
v_res_917_ = l_Lean_Elab_Tactic_withLocation___lam__0(v_atLocal_904_, v_a_16895__boxed_916_, v_failed_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(lean_object* v___x_918_, lean_object* v_atLocal_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Elab_Tactic_getFVarId(v___x_918_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = lean_apply_10(v_atLocal_919_, v_a_930_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_931_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v_atLocal_919_);
v_a_932_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_929_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed(lean_object* v___x_940_, lean_object* v_atLocal_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_940_, v_atLocal_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(lean_object* v_atLocal_952_, lean_object* v_as_953_, size_t v_i_954_, size_t v_stop_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_eq(v_i_954_, v_stop_955_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v___x_969_; 
v___x_967_ = lean_array_uget_borrowed(v_as_953_, v_i_954_);
lean_inc_ref(v_atLocal_952_);
lean_inc(v___x_967_);
v___f_968_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed), 11, 2);
lean_closure_set(v___f_968_, 0, v___x_967_);
lean_closure_set(v___f_968_, 1, v_atLocal_952_);
v___x_969_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_968_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; size_t v___x_971_; size_t v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_add(v_i_954_, v___x_971_);
v_i_954_ = v___x_972_;
v_b_956_ = v_a_970_;
goto _start;
}
else
{
lean_dec_ref(v_atLocal_952_);
return v___x_969_;
}
}
else
{
lean_object* v___x_974_; 
lean_dec_ref(v_atLocal_952_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_b_956_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(lean_object* v_atLocal_975_, lean_object* v_as_976_, lean_object* v_i_977_, lean_object* v_stop_978_, lean_object* v_b_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
size_t v_i_boxed_989_; size_t v_stop_boxed_990_; lean_object* v_res_991_; 
v_i_boxed_989_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_stop_boxed_990_ = lean_unbox_usize(v_stop_978_);
lean_dec(v_stop_978_);
v_res_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_975_, v_as_976_, v_i_boxed_989_, v_stop_boxed_990_, v_b_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_as_976_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation(lean_object* v_loc_992_, lean_object* v_atLocal_993_, lean_object* v_atTarget_994_, lean_object* v_failed_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
if (lean_obj_tag(v_loc_992_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_1005_, 0, lean_box(0));
lean_closure_set(v___x_1005_, 1, v_atTarget_994_);
v___x_1006_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed), 11, 2);
lean_closure_set(v___x_1006_, 0, lean_box(0));
lean_closure_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_Elab_Tactic_tryTactic___redArg(v___x_1006_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withLocation___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1009_, 0, v_atLocal_993_);
lean_closure_set(v___f_1009_, 1, v_a_1008_);
lean_closure_set(v___f_1009_, 2, v_failed_995_);
v___x_1010_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_997_, v_a_999_, v_a_1001_, v_a_1003_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_997_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
lean_dec(v_a_1011_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_1013_, v___f_1009_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___f_1009_);
v_a_1015_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1017_ = v___x_1012_;
v_isShared_1018_ = v_isSharedCheck_1036_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1012_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1036_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
uint8_t v___y_1020_; uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Exception_isInterrupt(v_a_1015_);
if (v___x_1034_ == 0)
{
uint8_t v___x_1035_; 
lean_inc(v_a_1015_);
v___x_1035_ = l_Lean_Exception_isRuntime(v_a_1015_);
v___y_1020_ = v___x_1035_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v___x_1034_;
goto v___jp_1019_;
}
v___jp_1019_:
{
if (v___y_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_del_object(v___x_1017_);
lean_dec(v_a_1015_);
v___x_1021_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1011_, v___y_1020_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v___x_1021_, 0);
lean_dec(v_unused_1030_);
v___x_1023_ = v___x_1021_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_dec(v___x_1021_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
return v___x_1021_;
}
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_a_1011_);
if (v_isShared_1018_ == 0)
{
v___x_1032_ = v___x_1017_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1015_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v___f_1009_);
v_a_1037_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1010_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1010_);
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
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_failed_995_);
lean_dec_ref(v_atLocal_993_);
v_a_1045_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1007_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1007_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_hypotheses_1053_; uint8_t v_type_1054_; lean_object* v___y_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
lean_dec_ref(v_failed_995_);
v_hypotheses_1053_ = lean_ctor_get(v_loc_992_, 0);
v_type_1054_ = lean_ctor_get_uint8(v_loc_992_, sizeof(void*)*1);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_array_get_size(v_hypotheses_1053_);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v_atLocal_993_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_nat_dec_le(v___x_1062_, v___x_1062_);
if (v___x_1065_ == 0)
{
if (v___x_1063_ == 0)
{
lean_dec_ref(v_atLocal_993_);
goto v___jp_1055_;
}
else
{
size_t v___x_1066_; size_t v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = ((size_t)0ULL);
v___x_1067_ = lean_usize_of_nat(v___x_1062_);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_993_, v_hypotheses_1053_, v___x_1066_, v___x_1067_, v___x_1064_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
v___y_1060_ = v___x_1068_;
goto v___jp_1059_;
}
}
else
{
size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = lean_usize_of_nat(v___x_1062_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_993_, v_hypotheses_1053_, v___x_1069_, v___x_1070_, v___x_1064_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
v___y_1060_ = v___x_1071_;
goto v___jp_1059_;
}
}
v___jp_1055_:
{
if (v_type_1054_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref(v_atTarget_994_);
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Elab_Tactic_withMainContext___redArg(v_atTarget_994_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1058_;
}
}
v___jp_1059_:
{
if (lean_obj_tag(v___y_1060_) == 0)
{
lean_dec_ref_known(v___y_1060_, 1);
goto v___jp_1055_;
}
else
{
lean_dec_ref(v_atTarget_994_);
return v___y_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withLocation___boxed(lean_object* v_loc_1072_, lean_object* v_atLocal_1073_, lean_object* v_atTarget_1074_, lean_object* v_failed_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_Elab_Tactic_withLocation(v_loc_1072_, v_atLocal_1073_, v_atTarget_1074_, v_failed_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_loc_1072_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(lean_object* v_00_u03b1_1126_, lean_object* v_x_1127_, lean_object* v_ctx_x3f_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1127_, v_ctx_x3f_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_x_1140_, lean_object* v_ctx_x3f_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_1139_, v_x_1140_, v_ctx_x3f_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1151_;
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
