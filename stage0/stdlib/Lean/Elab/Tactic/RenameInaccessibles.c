// Lean compiler output
// Module: Lean.Elab.Tactic.RenameInaccessibles
// Imports: public import Lean.Elab.Term import Lean.Elab.Binders
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_MacroScopesView_equalScope(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_renameInaccessibles___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_renameInaccessibles___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_renameInaccessibles___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_renameInaccessibles___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_renameInaccessibles___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "too many variable names provided"};
static const lean_object* l_Lean_Elab_Tactic_renameInaccessibles___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_renameInaccessibles___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_renameInaccessibles___closed__3;
static const lean_ctor_object l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_9_ = lean_apply_7(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed(lean_object* v_x_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(v_x_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_19_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(lean_object* v_mvarId_20_, lean_object* v_x_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
v___f_29_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_29_, 0, v_x_21_);
lean_closure_set(v___f_29_, 1, v___y_22_);
lean_closure_set(v___f_29_, 2, v___y_23_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_20_, v___f_29_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_20_ = stack[0].m_obj;
lean_object* v_x_21_ = stack[1].m_obj;
lean_object* v___y_22_ = stack[2].m_obj;
lean_object* v___y_23_ = stack[3].m_obj;
lean_object* v___y_24_ = stack[4].m_obj;
lean_object* v___y_25_ = stack[5].m_obj;
lean_object* v___y_26_ = stack[6].m_obj;
lean_object* v___y_27_ = stack[7].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(v_mvarId_20_, v_x_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___boxed(lean_object* v_mvarId_40_, lean_object* v_x_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(v_mvarId_40_, v_x_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_49_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(lean_object* v_00_u03b1_50_, lean_object* v_mvarId_51_, lean_object* v_x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(v_mvarId_51_, v_x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
return v___x_60_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_51_ = stack[1].m_obj;
lean_object* v_x_52_ = stack[2].m_obj;
lean_object* v___y_53_ = stack[3].m_obj;
lean_object* v___y_54_ = stack[4].m_obj;
lean_object* v___y_55_ = stack[5].m_obj;
lean_object* v___y_56_ = stack[6].m_obj;
lean_object* v___y_57_ = stack[7].m_obj;
lean_object* v___y_58_ = stack[8].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(lean_box(0), v_mvarId_51_, v_x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed(lean_object* v_00_u03b1_62_, lean_object* v_mvarId_63_, lean_object* v_x_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(v_00_u03b1_62_, v_mvarId_63_, v_x_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_72_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(lean_object* v_as_73_, size_t v_sz_74_, size_t v_i_75_, lean_object* v_b_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_lt(v_i_75_, v_sz_74_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v_b_76_);
return v___x_85_;
}
else
{
lean_object* v_a_86_; lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_a_86_ = lean_array_uget_borrowed(v_as_73_, v_i_75_);
v_fst_87_ = lean_ctor_get(v_a_86_, 0);
v_snd_88_ = lean_ctor_get(v_a_86_, 1);
v___x_89_ = lean_box(0);
lean_inc(v_fst_87_);
v___x_90_ = l_Lean_mkFVar(v_fst_87_);
lean_inc(v_snd_88_);
v___x_91_ = l_Lean_Elab_Term_addLocalVarInfo(v_snd_88_, v___x_90_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_91_) == 0)
{
size_t v___x_92_; size_t v___x_93_; 
lean_dec_ref_known(v___x_91_, 1);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_add(v_i_75_, v___x_92_);
v_i_75_ = v___x_93_;
v_b_76_ = v___x_89_;
goto _start;
}
else
{
return v___x_91_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_73_ = stack[0].m_obj;
size_t v_sz_74_ = stack[1].m_num;
size_t v_i_75_ = stack[2].m_num;
lean_object* v_b_76_ = stack[3].m_obj;
lean_object* v___y_77_ = stack[4].m_obj;
lean_object* v___y_78_ = stack[5].m_obj;
lean_object* v___y_79_ = stack[6].m_obj;
lean_object* v___y_80_ = stack[7].m_obj;
lean_object* v___y_81_ = stack[8].m_obj;
lean_object* v___y_82_ = stack[9].m_obj;
lean_object* v_res_95_;
v_res_95_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_as_73_, v_sz_74_, v_i_75_, v_b_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0___boxed(lean_object* v_as_96_, lean_object* v_sz_97_, lean_object* v_i_98_, lean_object* v_b_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
size_t v_sz_boxed_107_; size_t v_i_boxed_108_; lean_object* v_res_109_; 
v_sz_boxed_107_ = lean_unbox_usize(v_sz_97_);
lean_dec(v_sz_97_);
v_i_boxed_108_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_res_109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_as_96_, v_sz_boxed_107_, v_i_boxed_108_, v_b_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v_as_96_);
return v_res_109_;
}
}
lean_object* l_Lean_Elab_Tactic_renameInaccessibles___lam__0(lean_object* v_fst_110_, size_t v_sz_111_, size_t v___x_112_, lean_object* v___x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_fst_110_, v_sz_111_, v___x_112_, v___x_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
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
lean_ctor_set(v___x_123_, 0, v___x_113_);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_113_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
return v___x_121_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_renameInaccessibles___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_110_ = stack[0].m_obj;
size_t v_sz_111_ = stack[1].m_num;
size_t v___x_112_ = stack[2].m_num;
lean_object* v___x_113_ = stack[3].m_obj;
lean_object* v___y_114_ = stack[4].m_obj;
lean_object* v___y_115_ = stack[5].m_obj;
lean_object* v___y_116_ = stack[6].m_obj;
lean_object* v___y_117_ = stack[7].m_obj;
lean_object* v___y_118_ = stack[8].m_obj;
lean_object* v___y_119_ = stack[9].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Lean_Elab_Tactic_renameInaccessibles___lam__0(v_fst_110_, v_sz_111_, v___x_112_, v___x_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed(lean_object* v_fst_131_, lean_object* v_sz_132_, lean_object* v___x_133_, lean_object* v___x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
size_t v_sz_boxed_142_; size_t v___x_20576__boxed_143_; lean_object* v_res_144_; 
v_sz_boxed_142_ = lean_unbox_usize(v_sz_132_);
lean_dec(v_sz_132_);
v___x_20576__boxed_143_ = lean_unbox_usize(v___x_133_);
lean_dec(v___x_133_);
v_res_144_ = l_Lean_Elab_Tactic_renameInaccessibles___lam__0(v_fst_131_, v_sz_boxed_142_, v___x_20576__boxed_143_, v___x_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v_fst_131_);
return v_res_144_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_unsigned_to_nat(32u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_148_ = ((size_t)5ULL);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_unsigned_to_nat(32u);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
v___x_152_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_153_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_149_);
lean_ctor_set(v___x_153_, 3, v___x_149_);
lean_ctor_set_usize(v___x_153_, 4, v___x_148_);
return v___x_153_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v_infoState_157_; lean_object* v_trees_158_; lean_object* v___x_159_; lean_object* v_infoState_160_; lean_object* v_env_161_; lean_object* v_nextMacroScope_162_; lean_object* v_ngen_163_; lean_object* v_auxDeclNGen_164_; lean_object* v_traceState_165_; lean_object* v_cache_166_; lean_object* v_recordedDeps_167_; lean_object* v_messages_168_; lean_object* v_snapshotTasks_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_190_; 
v___x_156_ = lean_st_ref_get(v___y_154_);
v_infoState_157_ = lean_ctor_get(v___x_156_, 8);
lean_inc_ref(v_infoState_157_);
lean_dec(v___x_156_);
v_trees_158_ = lean_ctor_get(v_infoState_157_, 2);
lean_inc_ref(v_trees_158_);
lean_dec_ref(v_infoState_157_);
v___x_159_ = lean_st_ref_take(v___y_154_);
v_infoState_160_ = lean_ctor_get(v___x_159_, 8);
v_env_161_ = lean_ctor_get(v___x_159_, 0);
v_nextMacroScope_162_ = lean_ctor_get(v___x_159_, 1);
v_ngen_163_ = lean_ctor_get(v___x_159_, 2);
v_auxDeclNGen_164_ = lean_ctor_get(v___x_159_, 3);
v_traceState_165_ = lean_ctor_get(v___x_159_, 4);
v_cache_166_ = lean_ctor_get(v___x_159_, 5);
v_recordedDeps_167_ = lean_ctor_get(v___x_159_, 6);
v_messages_168_ = lean_ctor_get(v___x_159_, 7);
v_snapshotTasks_169_ = lean_ctor_get(v___x_159_, 9);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_190_ == 0)
{
v___x_171_ = v___x_159_;
v_isShared_172_ = v_isSharedCheck_190_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_snapshotTasks_169_);
lean_inc(v_infoState_160_);
lean_inc(v_messages_168_);
lean_inc(v_recordedDeps_167_);
lean_inc(v_cache_166_);
lean_inc(v_traceState_165_);
lean_inc(v_auxDeclNGen_164_);
lean_inc(v_ngen_163_);
lean_inc(v_nextMacroScope_162_);
lean_inc(v_env_161_);
lean_dec(v___x_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_190_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v_enabled_173_; lean_object* v_assignment_174_; lean_object* v_lazyAssignment_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_188_; 
v_enabled_173_ = lean_ctor_get_uint8(v_infoState_160_, sizeof(void*)*3);
v_assignment_174_ = lean_ctor_get(v_infoState_160_, 0);
v_lazyAssignment_175_ = lean_ctor_get(v_infoState_160_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_infoState_160_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_infoState_160_, 2);
lean_dec(v_unused_189_);
v___x_177_ = v_infoState_160_;
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_lazyAssignment_175_);
lean_inc(v_assignment_174_);
lean_dec(v_infoState_160_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 2, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_assignment_174_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_lazyAssignment_175_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v___x_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, sizeof(void*)*3, v_enabled_173_);
v___x_181_ = v_reuseFailAlloc_187_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 8, v___x_181_);
v___x_183_ = v___x_171_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_env_161_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_nextMacroScope_162_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_ngen_163_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_auxDeclNGen_164_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_traceState_165_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_cache_166_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v_recordedDeps_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v_messages_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_186_, 9, v_snapshotTasks_169_);
v___x_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_st_ref_put(v___y_154_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v_trees_158_);
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_154_ = stack[0].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_154_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_192_);
lean_dec(v___y_192_);
return v_res_194_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(lean_object* v___x_195_, lean_object* v_ctx_x3f_196_, size_t v_sz_197_, size_t v_i_198_, lean_object* v_bs_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_lt(v_i_198_, v_sz_197_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_ctx_x3f_196_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_bs_199_);
return v___x_208_;
}
else
{
lean_object* v_assignment_209_; lean_object* v_v_210_; lean_object* v___x_211_; lean_object* v_bs_x27_212_; lean_object* v_a_214_; lean_object* v_tree_219_; lean_object* v___x_220_; 
v_assignment_209_ = lean_ctor_get(v___x_195_, 0);
v_v_210_ = lean_array_uget(v_bs_199_, v_i_198_);
v___x_211_ = lean_unsigned_to_nat(0u);
v_bs_x27_212_ = lean_array_uset(v_bs_199_, v_i_198_, v___x_211_);
v_tree_219_ = l_Lean_Elab_InfoTree_substitute(v_v_210_, v_assignment_209_);
lean_inc_ref(v_ctx_x3f_196_);
lean_inc(v___y_205_);
lean_inc_ref(v___y_204_);
lean_inc(v___y_203_);
lean_inc_ref(v___y_202_);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
v___x_220_ = lean_apply_7(v_ctx_x3f_196_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
if (lean_obj_tag(v_a_221_) == 0)
{
v_a_214_ = v_tree_219_;
goto v___jp_213_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_223_; 
v_val_222_ = lean_ctor_get(v_a_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v_a_221_, 1);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_val_222_);
lean_ctor_set(v___x_223_, 1, v_tree_219_);
v_a_214_ = v___x_223_;
goto v___jp_213_;
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v_tree_219_);
lean_dec_ref(v_bs_x27_212_);
lean_dec_ref(v_ctx_x3f_196_);
v_a_224_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_220_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_220_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
v___jp_213_:
{
size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_add(v_i_198_, v___x_215_);
v___x_217_ = lean_array_uset(v_bs_x27_212_, v_i_198_, v_a_214_);
v_i_198_ = v___x_216_;
v_bs_199_ = v___x_217_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_195_ = stack[0].m_obj;
lean_object* v_ctx_x3f_196_ = stack[1].m_obj;
size_t v_sz_197_ = stack[2].m_num;
size_t v_i_198_ = stack[3].m_num;
lean_object* v_bs_199_ = stack[4].m_obj;
lean_object* v___y_200_ = stack[5].m_obj;
lean_object* v___y_201_ = stack[6].m_obj;
lean_object* v___y_202_ = stack[7].m_obj;
lean_object* v___y_203_ = stack[8].m_obj;
lean_object* v___y_204_ = stack[9].m_obj;
lean_object* v___y_205_ = stack[10].m_obj;
lean_object* v_res_232_;
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_195_, v_ctx_x3f_196_, v_sz_197_, v_i_198_, v_bs_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12___boxed(lean_object* v___x_233_, lean_object* v_ctx_x3f_234_, lean_object* v_sz_235_, lean_object* v_i_236_, lean_object* v_bs_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_235_);
lean_dec(v_sz_235_);
v_i_boxed_246_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_233_, v_ctx_x3f_234_, v_sz_boxed_245_, v_i_boxed_246_, v_bs_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec_ref(v___x_233_);
return v_res_247_;
}
}
lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(lean_object* v___x_248_, lean_object* v_ctx_x3f_249_, lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v_cs_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_284_; 
v_cs_258_ = lean_ctor_get(v_x_250_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_284_ == 0)
{
v___x_260_ = v_x_250_;
v_isShared_261_ = v_isSharedCheck_284_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_cs_258_);
lean_dec(v_x_250_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_284_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
size_t v_sz_262_; size_t v___x_263_; lean_object* v___x_264_; 
v_sz_262_ = lean_array_size(v_cs_258_);
v___x_263_ = ((size_t)0ULL);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_248_, v_ctx_x3f_249_, v_sz_262_, v___x_263_, v_cs_258_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_275_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_275_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v_a_265_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_272_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_del_object(v___x_260_);
v_a_276_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_264_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_264_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
else
{
lean_object* v_vs_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_311_; 
v_vs_285_ = lean_ctor_get(v_x_250_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_311_ == 0)
{
v___x_287_ = v_x_250_;
v_isShared_288_ = v_isSharedCheck_311_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_vs_285_);
lean_dec(v_x_250_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_311_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_291_; 
v_sz_289_ = lean_array_size(v_vs_285_);
v___x_290_ = ((size_t)0ULL);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_248_, v_ctx_x3f_249_, v_sz_289_, v___x_290_, v_vs_285_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_302_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_302_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_302_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_302_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v_a_292_);
v___x_297_ = v___x_287_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_301_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_297_);
v___x_299_ = v___x_294_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_del_object(v___x_287_);
v_a_303_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_291_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_291_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_248_ = stack[0].m_obj;
lean_object* v_ctx_x3f_249_ = stack[1].m_obj;
lean_object* v_x_250_ = stack[2].m_obj;
lean_object* v___y_251_ = stack[3].m_obj;
lean_object* v___y_252_ = stack[4].m_obj;
lean_object* v___y_253_ = stack[5].m_obj;
lean_object* v___y_254_ = stack[6].m_obj;
lean_object* v___y_255_ = stack[7].m_obj;
lean_object* v___y_256_ = stack[8].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_248_, v_ctx_x3f_249_, v_x_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
stack->m_obj
 = v_res_312_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(lean_object* v___x_313_, lean_object* v_ctx_x3f_314_, size_t v_sz_315_, size_t v_i_316_, lean_object* v_bs_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_316_, v_sz_315_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v_ctx_x3f_314_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_bs_317_);
return v___x_326_;
}
else
{
lean_object* v_v_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; lean_object* v___x_330_; 
v_v_327_ = lean_array_uget(v_bs_317_, v_i_316_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_317_, v_i_316_, v___x_328_);
lean_inc_ref(v_ctx_x3f_314_);
v___x_330_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_313_, v_ctx_x3f_314_, v_v_327_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_316_, v___x_332_);
v___x_334_ = lean_array_uset(v_bs_x27_329_, v_i_316_, v_a_331_);
v_i_316_ = v___x_333_;
v_bs_317_ = v___x_334_;
goto _start;
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_bs_x27_329_);
lean_dec_ref(v_ctx_x3f_314_);
v_a_336_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_330_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_330_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_313_ = stack[0].m_obj;
lean_object* v_ctx_x3f_314_ = stack[1].m_obj;
size_t v_sz_315_ = stack[2].m_num;
size_t v_i_316_ = stack[3].m_num;
lean_object* v_bs_317_ = stack[4].m_obj;
lean_object* v___y_318_ = stack[5].m_obj;
lean_object* v___y_319_ = stack[6].m_obj;
lean_object* v___y_320_ = stack[7].m_obj;
lean_object* v___y_321_ = stack[8].m_obj;
lean_object* v___y_322_ = stack[9].m_obj;
lean_object* v___y_323_ = stack[10].m_obj;
lean_object* v_res_344_;
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_313_, v_ctx_x3f_314_, v_sz_315_, v_i_316_, v_bs_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v___x_345_, lean_object* v_ctx_x3f_346_, lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_bs_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
size_t v_sz_boxed_357_; size_t v_i_boxed_358_; lean_object* v_res_359_; 
v_sz_boxed_357_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_358_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_345_, v_ctx_x3f_346_, v_sz_boxed_357_, v_i_boxed_358_, v_bs_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec_ref(v___x_345_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11___boxed(lean_object* v___x_360_, lean_object* v_ctx_x3f_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_360_, v_ctx_x3f_361_, v_x_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v___x_360_);
return v_res_370_;
}
}
lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(lean_object* v___x_371_, lean_object* v_ctx_x3f_372_, lean_object* v_t_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_root_381_; lean_object* v_tail_382_; lean_object* v_size_383_; size_t v_shift_384_; lean_object* v_tailOff_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_421_; 
v_root_381_ = lean_ctor_get(v_t_373_, 0);
v_tail_382_ = lean_ctor_get(v_t_373_, 1);
v_size_383_ = lean_ctor_get(v_t_373_, 2);
v_shift_384_ = lean_ctor_get_usize(v_t_373_, 4);
v_tailOff_385_ = lean_ctor_get(v_t_373_, 3);
v_isSharedCheck_421_ = !lean_is_exclusive(v_t_373_);
if (v_isSharedCheck_421_ == 0)
{
v___x_387_ = v_t_373_;
v_isShared_388_ = v_isSharedCheck_421_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_tailOff_385_);
lean_inc(v_size_383_);
lean_inc(v_tail_382_);
lean_inc(v_root_381_);
lean_dec(v_t_373_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_421_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; 
lean_inc_ref(v_ctx_x3f_372_);
v___x_389_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_371_, v_ctx_x3f_372_, v_root_381_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; size_t v_sz_391_; size_t v___x_392_; lean_object* v___x_393_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v_sz_391_ = lean_array_size(v_tail_382_);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_371_, v_ctx_x3f_372_, v_sz_391_, v___x_392_, v_tail_382_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_404_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_404_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_a_394_);
lean_ctor_set(v___x_387_, 0, v_a_390_);
v___x_399_ = v___x_387_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_394_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_size_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_tailOff_385_);
lean_ctor_set_usize(v_reuseFailAlloc_403_, 4, v_shift_384_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_390_);
lean_del_object(v___x_387_);
lean_dec(v_tailOff_385_);
lean_dec(v_size_383_);
v_a_405_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_393_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_393_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_del_object(v___x_387_);
lean_dec(v_tailOff_385_);
lean_dec(v_size_383_);
lean_dec_ref(v_tail_382_);
lean_dec_ref(v_ctx_x3f_372_);
v_a_413_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_389_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_389_);
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
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_371_ = stack[0].m_obj;
lean_object* v_ctx_x3f_372_ = stack[1].m_obj;
lean_object* v_t_373_ = stack[2].m_obj;
lean_object* v___y_374_ = stack[3].m_obj;
lean_object* v___y_375_ = stack[4].m_obj;
lean_object* v___y_376_ = stack[5].m_obj;
lean_object* v___y_377_ = stack[6].m_obj;
lean_object* v___y_378_ = stack[7].m_obj;
lean_object* v___y_379_ = stack[8].m_obj;
lean_object* v_res_422_;
v_res_422_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v___x_371_, v_ctx_x3f_372_, v_t_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6___boxed(lean_object* v___x_423_, lean_object* v_ctx_x3f_424_, lean_object* v_t_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v___x_423_, v_ctx_x3f_424_, v_t_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec_ref(v___x_423_);
return v_res_433_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(lean_object* v___y_434_, lean_object* v_ctx_x3f_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v_a_441_, lean_object* v_a_x3f_442_){
_start:
{
lean_object* v___x_444_; lean_object* v_infoState_445_; lean_object* v_trees_446_; lean_object* v___x_447_; 
v___x_444_ = lean_st_ref_get(v___y_434_);
v_infoState_445_ = lean_ctor_get(v___x_444_, 8);
lean_inc_ref(v_infoState_445_);
lean_dec(v___x_444_);
v_trees_446_ = lean_ctor_get(v_infoState_445_, 2);
lean_inc_ref(v_trees_446_);
v___x_447_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v_infoState_445_, v_ctx_x3f_435_, v_trees_446_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_434_);
lean_dec_ref(v_infoState_445_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_487_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_487_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_487_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_487_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v_infoState_453_; lean_object* v_env_454_; lean_object* v_nextMacroScope_455_; lean_object* v_ngen_456_; lean_object* v_auxDeclNGen_457_; lean_object* v_traceState_458_; lean_object* v_cache_459_; lean_object* v_recordedDeps_460_; lean_object* v_messages_461_; lean_object* v_snapshotTasks_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_486_; 
v___x_452_ = lean_st_ref_take(v___y_434_);
v_infoState_453_ = lean_ctor_get(v___x_452_, 8);
v_env_454_ = lean_ctor_get(v___x_452_, 0);
v_nextMacroScope_455_ = lean_ctor_get(v___x_452_, 1);
v_ngen_456_ = lean_ctor_get(v___x_452_, 2);
v_auxDeclNGen_457_ = lean_ctor_get(v___x_452_, 3);
v_traceState_458_ = lean_ctor_get(v___x_452_, 4);
v_cache_459_ = lean_ctor_get(v___x_452_, 5);
v_recordedDeps_460_ = lean_ctor_get(v___x_452_, 6);
v_messages_461_ = lean_ctor_get(v___x_452_, 7);
v_snapshotTasks_462_ = lean_ctor_get(v___x_452_, 9);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_486_ == 0)
{
v___x_464_ = v___x_452_;
v_isShared_465_ = v_isSharedCheck_486_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snapshotTasks_462_);
lean_inc(v_infoState_453_);
lean_inc(v_messages_461_);
lean_inc(v_recordedDeps_460_);
lean_inc(v_cache_459_);
lean_inc(v_traceState_458_);
lean_inc(v_auxDeclNGen_457_);
lean_inc(v_ngen_456_);
lean_inc(v_nextMacroScope_455_);
lean_inc(v_env_454_);
lean_dec(v___x_452_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_486_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v_enabled_466_; lean_object* v_assignment_467_; lean_object* v_lazyAssignment_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_484_; 
v_enabled_466_ = lean_ctor_get_uint8(v_infoState_453_, sizeof(void*)*3);
v_assignment_467_ = lean_ctor_get(v_infoState_453_, 0);
v_lazyAssignment_468_ = lean_ctor_get(v_infoState_453_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_infoState_453_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_infoState_453_, 2);
lean_dec(v_unused_485_);
v___x_470_ = v_infoState_453_;
v_isShared_471_ = v_isSharedCheck_484_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_lazyAssignment_468_);
lean_inc(v_assignment_467_);
lean_dec(v_infoState_453_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_484_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_box(0);
v___x_473_ = l_Lean_PersistentArray_append___redArg(v_a_441_, v_a_448_);
lean_dec(v_a_448_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 2, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_assignment_467_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_lazyAssignment_468_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v___x_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*3, v_enabled_466_);
v___x_475_ = v_reuseFailAlloc_483_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 8, v___x_475_);
v___x_477_ = v___x_464_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_env_454_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_nextMacroScope_455_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_ngen_456_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_auxDeclNGen_457_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_traceState_458_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_cache_459_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_recordedDeps_460_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_messages_461_);
lean_ctor_set(v_reuseFailAlloc_482_, 8, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_482_, 9, v_snapshotTasks_462_);
v___x_477_ = v_reuseFailAlloc_482_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_st_ref_put(v___y_434_, v___x_477_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_472_);
v___x_480_ = v___x_450_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_472_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_a_441_);
v_a_488_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_447_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_447_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_434_ = stack[0].m_obj;
lean_object* v_ctx_x3f_435_ = stack[1].m_obj;
lean_object* v___y_436_ = stack[2].m_obj;
lean_object* v___y_437_ = stack[3].m_obj;
lean_object* v___y_438_ = stack[4].m_obj;
lean_object* v___y_439_ = stack[5].m_obj;
lean_object* v___y_440_ = stack[6].m_obj;
lean_object* v_a_441_ = stack[7].m_obj;
lean_object* v_a_x3f_442_ = stack[8].m_obj;
lean_object* v_res_496_;
v_res_496_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_434_, v_ctx_x3f_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v_a_441_, v_a_x3f_442_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_497_, lean_object* v_ctx_x3f_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v_a_504_, lean_object* v_a_x3f_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_497_, v_ctx_x3f_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v_a_504_, v_a_x3f_505_);
lean_dec(v_a_x3f_505_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_497_);
return v_res_507_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(lean_object* v_x_508_, lean_object* v_ctx_x3f_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_infoState_518_; uint8_t v_enabled_519_; 
v___x_517_ = lean_st_ref_get(v___y_515_);
v_infoState_518_ = lean_ctor_get(v___x_517_, 8);
lean_inc_ref(v_infoState_518_);
lean_dec(v___x_517_);
v_enabled_519_ = lean_ctor_get_uint8(v_infoState_518_, sizeof(void*)*3);
lean_dec_ref(v_infoState_518_);
if (v_enabled_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v_ctx_x3f_509_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
v___x_520_ = lean_apply_7(v_x_508_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, lean_box(0));
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v_r_523_; 
v___x_521_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_515_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
v_r_523_ = lean_apply_7(v_x_508_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, lean_box(0));
if (lean_obj_tag(v_r_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_548_; 
v_a_524_ = lean_ctor_get(v_r_523_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_r_523_);
if (v_isSharedCheck_548_ == 0)
{
v___x_526_ = v_r_523_;
v_isShared_527_ = v_isSharedCheck_548_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v_r_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_548_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
lean_inc(v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 1);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_547_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_515_, v_ctx_x3f_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v_a_522_, v___x_529_);
lean_dec_ref(v___x_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v___x_530_, 0);
lean_dec(v_unused_538_);
v___x_532_ = v___x_530_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_dec(v___x_530_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_a_524_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_524_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_524_);
v_a_539_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_530_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_549_ = lean_ctor_get(v_r_523_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v_r_523_, 1);
v___x_550_ = lean_box(0);
v___x_551_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_515_, v_ctx_x3f_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v_a_522_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_559_);
v___x_553_ = v___x_551_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_dec(v___x_551_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 1);
lean_ctor_set(v___x_553_, 0, v_a_549_);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_549_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_549_);
v_a_560_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_508_ = stack[0].m_obj;
lean_object* v_ctx_x3f_509_ = stack[1].m_obj;
lean_object* v___y_510_ = stack[2].m_obj;
lean_object* v___y_511_ = stack[3].m_obj;
lean_object* v___y_512_ = stack[4].m_obj;
lean_object* v___y_513_ = stack[5].m_obj;
lean_object* v___y_514_ = stack[6].m_obj;
lean_object* v___y_515_ = stack[7].m_obj;
lean_object* v_res_568_;
v_res_568_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_508_, v_ctx_x3f_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___boxed(lean_object* v_x_569_, lean_object* v_ctx_x3f_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_569_, v_ctx_x3f_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_578_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_env_584_; lean_object* v___x_585_; lean_object* v_toCold_586_; lean_object* v_mctx_587_; lean_object* v_currNamespace_588_; lean_object* v_openDecls_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_ngen_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_583_ = lean_st_ref_get(v___y_581_);
v_env_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_env_584_);
lean_dec(v___x_583_);
v___x_585_ = lean_st_ref_get(v___y_579_);
v_toCold_586_ = lean_ctor_get(v___y_580_, 0);
v_mctx_587_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_mctx_587_);
lean_dec(v___x_585_);
v_currNamespace_588_ = lean_ctor_get(v_toCold_586_, 4);
v_openDecls_589_ = lean_ctor_get(v_toCold_586_, 5);
v___x_590_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_580_);
v___x_591_ = lean_st_ref_get(v___y_581_);
v_ngen_592_ = lean_ctor_get(v___x_591_, 2);
lean_inc_ref(v_ngen_592_);
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v___x_594_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_589_);
lean_inc(v_currNamespace_588_);
v___x_595_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_595_, 0, v_env_584_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
lean_ctor_set(v___x_595_, 3, v_mctx_587_);
lean_ctor_set(v___x_595_, 4, v___x_590_);
lean_ctor_set(v___x_595_, 5, v_currNamespace_588_);
lean_ctor_set(v___x_595_, 6, v_openDecls_589_);
lean_ctor_set(v___x_595_, 7, v_ngen_592_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_579_ = stack[0].m_obj;
lean_object* v___y_580_ = stack[1].m_obj;
lean_object* v___y_581_ = stack[2].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_579_, v___y_580_, v___y_581_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
return v_res_602_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; lean_object* v_toCold_611_; lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_636_; 
v___x_610_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_606_, v___y_607_, v___y_608_);
v_toCold_611_ = lean_ctor_get(v___y_607_, 0);
v_a_612_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_636_ == 0)
{
v___x_614_ = v___x_610_;
v_isShared_615_ = v_isSharedCheck_636_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_636_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_fileMap_616_; lean_object* v_env_617_; lean_object* v_mctx_618_; lean_object* v_options_619_; lean_object* v_currNamespace_620_; lean_object* v_openDecls_621_; lean_object* v_ngen_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_633_; 
v_fileMap_616_ = lean_ctor_get(v_toCold_611_, 1);
v_env_617_ = lean_ctor_get(v_a_612_, 0);
v_mctx_618_ = lean_ctor_get(v_a_612_, 3);
v_options_619_ = lean_ctor_get(v_a_612_, 4);
v_currNamespace_620_ = lean_ctor_get(v_a_612_, 5);
v_openDecls_621_ = lean_ctor_get(v_a_612_, 6);
v_ngen_622_ = lean_ctor_get(v_a_612_, 7);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; 
v_unused_634_ = lean_ctor_get(v_a_612_, 2);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_a_612_, 1);
lean_dec(v_unused_635_);
v___x_624_ = v_a_612_;
v_isShared_625_ = v_isSharedCheck_633_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_ngen_622_);
lean_inc(v_openDecls_621_);
lean_inc(v_currNamespace_620_);
lean_inc(v_options_619_);
lean_inc(v_mctx_618_);
lean_inc(v_env_617_);
lean_dec(v_a_612_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_633_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_box(0);
lean_inc_ref(v_fileMap_616_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v_fileMap_616_);
lean_ctor_set(v___x_624_, 1, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_env_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_fileMap_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_mctx_618_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_options_619_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_currNamespace_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_openDecls_621_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_ngen_622_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_628_);
v___x_630_ = v___x_614_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_603_ = stack[0].m_obj;
lean_object* v___y_604_ = stack[1].m_obj;
lean_object* v___y_605_ = stack[2].m_obj;
lean_object* v___y_606_ = stack[3].m_obj;
lean_object* v___y_607_ = stack[4].m_obj;
lean_object* v___y_608_ = stack[5].m_obj;
lean_object* v_res_637_;
v_res_637_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2___boxed(lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_645_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_663_; 
v___x_653_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_a_654_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_646_ = stack[0].m_obj;
lean_object* v___y_647_ = stack[1].m_obj;
lean_object* v___y_648_ = stack[2].m_obj;
lean_object* v___y_649_ = stack[3].m_obj;
lean_object* v___y_650_ = stack[4].m_obj;
lean_object* v___y_651_ = stack[5].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed(lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_672_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; 
v___f_682_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0));
v___x_683_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_674_, v___f_682_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_683_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_674_ = stack[0].m_obj;
lean_object* v___y_675_ = stack[1].m_obj;
lean_object* v___y_676_ = stack[2].m_obj;
lean_object* v___y_677_ = stack[3].m_obj;
lean_object* v___y_678_ = stack[4].m_obj;
lean_object* v___y_679_ = stack[5].m_obj;
lean_object* v___y_680_ = stack[6].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_693_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(lean_object* v_snd_694_, lean_object* v___x_695_, lean_object* v_____r_696_, lean_object* v_lctx_697_, lean_object* v_hs_698_, lean_object* v_info_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_707_ = l_Lean_NameSet_insert(v_snd_694_, v___x_695_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_info_699_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_hs_698_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_lctx_697_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_694_ = stack[0].m_obj;
lean_object* v___x_695_ = stack[1].m_obj;
lean_object* v_____r_696_ = stack[2].m_obj;
lean_object* v_lctx_697_ = stack[3].m_obj;
lean_object* v_hs_698_ = stack[4].m_obj;
lean_object* v_info_699_ = stack[5].m_obj;
lean_object* v___y_700_ = stack[6].m_obj;
lean_object* v___y_701_ = stack[7].m_obj;
lean_object* v___y_702_ = stack[8].m_obj;
lean_object* v___y_703_ = stack[9].m_obj;
lean_object* v___y_704_ = stack[10].m_obj;
lean_object* v___y_705_ = stack[11].m_obj;
lean_object* v_res_713_;
v_res_713_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_694_, v___x_695_, v_____r_696_, v_lctx_697_, v_hs_698_, v_info_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(lean_object* v_snd_714_, lean_object* v___x_715_, lean_object* v_____r_716_, lean_object* v_lctx_717_, lean_object* v_hs_718_, lean_object* v_info_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_714_, v___x_715_, v_____r_716_, v_lctx_717_, v_hs_718_, v_info_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_727_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(lean_object* v_fst_728_, lean_object* v___f_729_, lean_object* v_snd_730_, lean_object* v_____r_731_, lean_object* v_lctx_732_, lean_object* v_info_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_741_ = lean_array_pop(v_fst_728_);
v___x_742_ = lean_array_get_size(v___x_741_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v_snd_730_);
v___x_745_ = lean_box(0);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
v___x_746_ = lean_apply_11(v___f_729_, v___x_745_, v_lctx_732_, v___x_741_, v_info_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, lean_box(0));
return v___x_746_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v___f_729_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_info_733_);
lean_ctor_set(v___x_747_, 1, v_snd_730_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_741_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_lctx_732_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_728_ = stack[0].m_obj;
lean_object* v___f_729_ = stack[1].m_obj;
lean_object* v_snd_730_ = stack[2].m_obj;
lean_object* v_____r_731_ = stack[3].m_obj;
lean_object* v_lctx_732_ = stack[4].m_obj;
lean_object* v_info_733_ = stack[5].m_obj;
lean_object* v___y_734_ = stack[6].m_obj;
lean_object* v___y_735_ = stack[7].m_obj;
lean_object* v___y_736_ = stack[8].m_obj;
lean_object* v___y_737_ = stack[9].m_obj;
lean_object* v___y_738_ = stack[10].m_obj;
lean_object* v___y_739_ = stack[11].m_obj;
lean_object* v_res_752_;
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_728_, v___f_729_, v_snd_730_, v_____r_731_, v_lctx_732_, v_info_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(lean_object* v_fst_753_, lean_object* v___f_754_, lean_object* v_snd_755_, lean_object* v_____r_756_, lean_object* v_lctx_757_, lean_object* v_info_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_753_, v___f_754_, v_snd_755_, v_____r_756_, v_lctx_757_, v_info_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_766_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(lean_object* v_upperBound_775_, lean_object* v___x_776_, lean_object* v_val_777_, lean_object* v_a_778_, lean_object* v_b_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_a_788_; lean_object* v___y_793_; uint8_t v___x_812_; 
v___x_812_ = lean_nat_dec_lt(v_a_778_, v_upperBound_775_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v_a_778_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v_b_779_);
return v___x_813_;
}
else
{
lean_object* v_snd_814_; lean_object* v_snd_815_; lean_object* v_fst_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_889_; 
v_snd_814_ = lean_ctor_get(v_b_779_, 1);
lean_inc(v_snd_814_);
v_snd_815_ = lean_ctor_get(v_snd_814_, 1);
lean_inc(v_snd_815_);
v_fst_816_ = lean_ctor_get(v_b_779_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_b_779_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_b_779_, 1);
lean_dec(v_unused_890_);
v___x_818_ = v_b_779_;
v_isShared_819_ = v_isSharedCheck_889_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_fst_816_);
lean_dec(v_b_779_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_889_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_fst_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_887_; 
v_fst_820_ = lean_ctor_get(v_snd_814_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_snd_814_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_snd_814_, 1);
lean_dec(v_unused_888_);
v___x_822_ = v_snd_814_;
v_isShared_823_ = v_isSharedCheck_887_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_fst_820_);
lean_dec(v_snd_814_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_887_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_fst_824_; lean_object* v_snd_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_886_; 
v_fst_824_ = lean_ctor_get(v_snd_815_, 0);
v_snd_825_ = lean_ctor_get(v_snd_815_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_snd_815_);
if (v_isSharedCheck_886_ == 0)
{
v___x_827_ = v_snd_815_;
v_isShared_828_ = v_isSharedCheck_886_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_snd_825_);
lean_inc(v_fst_824_);
lean_dec(v_snd_815_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_886_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_nat_sub(v___x_776_, v_a_778_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_sub(v___x_829_, v___x_830_);
lean_dec(v___x_829_);
v___x_832_ = l_Lean_LocalContext_getAt_x3f(v_fst_816_, v___x_831_);
lean_dec(v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_834_; 
if (v_isShared_828_ == 0)
{
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_fst_824_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_snd_825_);
v___x_834_ = v_reuseFailAlloc_841_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_836_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_834_);
v___x_836_ = v___x_822_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_836_);
v___x_838_ = v___x_818_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_fst_816_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
v_a_788_ = v___x_838_;
goto v___jp_787_;
}
}
}
}
else
{
lean_object* v_val_842_; uint8_t v___x_843_; 
v_val_842_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v___x_832_, 1);
v___x_843_ = l_Lean_LocalDecl_isImplementationDetail(v_val_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___f_845_; lean_object* v___y_847_; lean_object* v___x_872_; uint8_t v___x_873_; 
lean_del_object(v___x_822_);
lean_del_object(v___x_818_);
v___x_844_ = l_Lean_LocalDecl_userName(v_val_842_);
lean_inc_n(v___x_844_, 2);
lean_inc(v_snd_825_);
v___f_845_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_845_, 0, v_snd_825_);
lean_closure_set(v___f_845_, 1, v___x_844_);
v___x_872_ = l_Lean_extractMacroScopes(v___x_844_);
v___x_873_ = l_Lean_MacroScopesView_equalScope(v___x_872_, v_val_777_);
lean_dec_ref(v___x_872_);
if (v___x_873_ == 0)
{
lean_dec(v___x_844_);
goto v___jp_857_;
}
else
{
if (v___x_843_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_NameSet_contains(v_snd_825_, v___x_844_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v___f_845_);
lean_dec(v_val_842_);
lean_del_object(v___x_827_);
v___x_875_ = lean_box(0);
v___x_876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_825_, v___x_844_, v___x_875_, v_fst_816_, v_fst_820_, v_fst_824_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_793_ = v___x_876_;
goto v___jp_792_;
}
else
{
lean_dec(v___x_844_);
goto v___jp_857_;
}
}
else
{
lean_dec(v___x_844_);
goto v___jp_857_;
}
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_848_ = l_Lean_TSyntax_getId(v___y_847_);
v___x_849_ = l_Lean_LocalDecl_fvarId(v_val_842_);
lean_dec(v_val_842_);
lean_inc(v___x_849_);
v___x_850_ = l_Lean_LocalContext_setUserName(v_fst_816_, v___x_849_, v___x_848_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v___y_847_);
lean_ctor_set(v___x_827_, 0, v___x_849_);
v___x_852_ = v___x_827_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___y_847_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_array_push(v_fst_824_, v___x_852_);
v___x_854_ = lean_box(0);
v___x_855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_820_, v___f_845_, v_snd_825_, v___x_854_, v___x_850_, v___x_853_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_793_ = v___x_855_;
goto v___jp_792_;
}
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_858_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
v___x_859_ = lean_box(0);
v___x_860_ = lean_array_get_size(v_fst_820_);
v___x_861_ = lean_nat_sub(v___x_860_, v___x_830_);
v___x_862_ = lean_array_get_borrowed(v___x_859_, v_fst_820_, v___x_861_);
lean_dec(v___x_861_);
lean_inc(v___x_862_);
v___x_863_ = l_Lean_Syntax_isOfKind(v___x_862_, v___x_858_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v_val_842_);
lean_del_object(v___x_827_);
v___x_864_ = lean_box(0);
v___x_865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_820_, v___f_845_, v_snd_825_, v___x_864_, v_fst_816_, v_fst_824_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_793_ = v___x_865_;
goto v___jp_792_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = l_Lean_Syntax_getArg(v___x_862_, v___x_866_);
if (v___x_843_ == 0)
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_867_);
v___x_869_ = l_Lean_Syntax_isOfKind(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v___x_867_);
lean_dec(v_val_842_);
lean_del_object(v___x_827_);
v___x_870_ = lean_box(0);
v___x_871_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_820_, v___f_845_, v_snd_825_, v___x_870_, v_fst_816_, v_fst_824_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_793_ = v___x_871_;
goto v___jp_792_;
}
else
{
v___y_847_ = v___x_867_;
goto v___jp_846_;
}
}
else
{
v___y_847_ = v___x_867_;
goto v___jp_846_;
}
}
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v_val_842_);
if (v_isShared_828_ == 0)
{
v___x_878_ = v___x_827_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_fst_824_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_825_);
v___x_878_ = v_reuseFailAlloc_885_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_878_);
v___x_880_ = v___x_822_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_880_);
v___x_882_ = v___x_818_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fst_816_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
v_a_788_ = v___x_882_;
goto v___jp_787_;
}
}
}
}
}
}
}
}
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_a_778_, v___x_789_);
lean_dec(v_a_778_);
v_a_778_ = v___x_790_;
v_b_779_ = v_a_788_;
goto _start;
}
v___jp_792_:
{
if (lean_obj_tag(v___y_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_803_; 
v_a_794_ = lean_ctor_get(v___y_793_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___y_793_);
if (v_isSharedCheck_803_ == 0)
{
v___x_796_ = v___y_793_;
v_isShared_797_ = v_isSharedCheck_803_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___y_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_803_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
if (lean_obj_tag(v_a_794_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; 
lean_dec(v_a_778_);
v_a_798_ = lean_ctor_get(v_a_794_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v_a_794_, 1);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v_a_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
lean_object* v_a_802_; 
lean_del_object(v___x_796_);
v_a_802_ = lean_ctor_get(v_a_794_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v_a_794_, 1);
v_a_788_ = v_a_802_;
goto v___jp_787_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_778_);
v_a_804_ = lean_ctor_get(v___y_793_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___y_793_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___y_793_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___y_793_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_775_ = stack[0].m_obj;
lean_object* v___x_776_ = stack[1].m_obj;
lean_object* v_val_777_ = stack[2].m_obj;
lean_object* v_a_778_ = stack[3].m_obj;
lean_object* v_b_779_ = stack[4].m_obj;
lean_object* v___y_780_ = stack[5].m_obj;
lean_object* v___y_781_ = stack[6].m_obj;
lean_object* v___y_782_ = stack[7].m_obj;
lean_object* v___y_783_ = stack[8].m_obj;
lean_object* v___y_784_ = stack[9].m_obj;
lean_object* v___y_785_ = stack[10].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_775_, v___x_776_, v_val_777_, v_a_778_, v_b_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___boxed(lean_object* v_upperBound_892_, lean_object* v___x_893_, lean_object* v_val_894_, lean_object* v_a_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_892_, v___x_893_, v_val_894_, v_a_895_, v_b_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec_ref(v_val_894_);
lean_dec(v___x_893_);
lean_dec(v_upperBound_892_);
return v_res_904_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(uint8_t v_suppressElabErrors_913_, uint8_t v___y_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_915_) == 1)
{
lean_object* v_pre_916_; 
v_pre_916_ = lean_ctor_get(v_x_915_, 0);
switch(lean_obj_tag(v_pre_916_))
{
case 1:
{
lean_object* v_pre_917_; 
v_pre_917_ = lean_ctor_get(v_pre_916_, 0);
switch(lean_obj_tag(v_pre_917_))
{
case 0:
{
lean_object* v_str_918_; lean_object* v_str_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_str_918_ = lean_ctor_get(v_x_915_, 1);
v_str_919_ = lean_ctor_get(v_pre_916_, 1);
v___x_920_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0));
v___x_921_ = lean_string_dec_eq(v_str_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1));
v___x_923_ = lean_string_dec_eq(v_str_919_, v___x_922_);
if (v___x_923_ == 0)
{
return v___x_923_;
}
else
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2));
v___x_925_ = lean_string_dec_eq(v_str_918_, v___x_924_);
if (v___x_925_ == 0)
{
return v___x_925_;
}
else
{
return v_suppressElabErrors_913_;
}
}
}
else
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3));
v___x_927_ = lean_string_dec_eq(v_str_918_, v___x_926_);
if (v___x_927_ == 0)
{
return v___x_927_;
}
else
{
return v_suppressElabErrors_913_;
}
}
}
case 1:
{
lean_object* v_pre_928_; 
v_pre_928_ = lean_ctor_get(v_pre_917_, 0);
if (lean_obj_tag(v_pre_928_) == 0)
{
lean_object* v_str_929_; lean_object* v_str_930_; lean_object* v_str_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_str_929_ = lean_ctor_get(v_x_915_, 1);
v_str_930_ = lean_ctor_get(v_pre_916_, 1);
v_str_931_ = lean_ctor_get(v_pre_917_, 1);
v___x_932_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4));
v___x_933_ = lean_string_dec_eq(v_str_931_, v___x_932_);
if (v___x_933_ == 0)
{
return v___x_933_;
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5));
v___x_935_ = lean_string_dec_eq(v_str_930_, v___x_934_);
if (v___x_935_ == 0)
{
return v___x_935_;
}
else
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6));
v___x_937_ = lean_string_dec_eq(v_str_929_, v___x_936_);
if (v___x_937_ == 0)
{
return v___x_937_;
}
else
{
return v_suppressElabErrors_913_;
}
}
}
}
else
{
return v___y_914_;
}
}
default: 
{
return v___y_914_;
}
}
}
case 0:
{
lean_object* v_str_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_str_938_ = lean_ctor_get(v_x_915_, 1);
v___x_939_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7));
v___x_940_ = lean_string_dec_eq(v_str_938_, v___x_939_);
if (v___x_940_ == 0)
{
return v___x_940_;
}
else
{
return v_suppressElabErrors_913_;
}
}
default: 
{
return v___y_914_;
}
}
}
else
{
return v___y_914_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_913_ = stack[0].m_num;
uint8_t v___y_914_ = stack[1].m_num;
lean_object* v_x_915_ = stack[2].m_obj;
uint8_t v_res_941_;
v_res_941_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v_suppressElabErrors_913_, v___y_914_, v_x_915_);
stack->m_num = v_res_941_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_942_, lean_object* v___y_943_, lean_object* v_x_944_){
_start:
{
uint8_t v_suppressElabErrors_boxed_945_; uint8_t v___y_22416__boxed_946_; uint8_t v_res_947_; lean_object* v_r_948_; 
v_suppressElabErrors_boxed_945_ = lean_unbox(v_suppressElabErrors_942_);
v___y_22416__boxed_946_ = lean_unbox(v___y_943_);
v_res_947_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v_suppressElabErrors_boxed_945_, v___y_22416__boxed_946_, v_x_944_);
lean_dec(v_x_944_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(lean_object* v_opts_949_, lean_object* v_opt_950_){
_start:
{
lean_object* v_name_951_; lean_object* v_defValue_952_; lean_object* v_map_953_; lean_object* v___x_954_; 
v_name_951_ = lean_ctor_get(v_opt_950_, 0);
v_defValue_952_ = lean_ctor_get(v_opt_950_, 1);
v_map_953_ = lean_ctor_get(v_opts_949_, 0);
v___x_954_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_953_, v_name_951_);
if (lean_obj_tag(v___x_954_) == 0)
{
uint8_t v___x_955_; 
v___x_955_ = lean_unbox(v_defValue_952_);
return v___x_955_;
}
else
{
lean_object* v_val_956_; 
v_val_956_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_956_);
lean_dec_ref_known(v___x_954_, 1);
if (lean_obj_tag(v_val_956_) == 1)
{
uint8_t v_v_957_; 
v_v_957_ = lean_ctor_get_uint8(v_val_956_, 0);
lean_dec_ref_known(v_val_956_, 0);
return v_v_957_;
}
else
{
uint8_t v___x_958_; 
lean_dec(v_val_956_);
v___x_958_ = lean_unbox(v_defValue_952_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_949_ = stack[0].m_obj;
lean_object* v_opt_950_ = stack[1].m_obj;
uint8_t v_res_959_;
v_res_959_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_949_, v_opt_950_);
stack->m_num = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(lean_object* v_opts_960_, lean_object* v_opt_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_960_, v_opt_961_);
lean_dec_ref(v_opt_961_);
lean_dec_ref(v_opts_960_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(lean_object* v_msgData_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; uint8_t v___x_972_; lean_object* v_env_973_; lean_object* v___x_974_; lean_object* v_toCold_975_; lean_object* v_mctx_976_; lean_object* v_lctx_977_; lean_object* v_options_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_970_);
v___x_972_ = 0;
v_env_973_ = l_Lean_Environment_setRecordingDeps(v_env_971_, v___x_972_);
v___x_974_ = lean_st_ref_get(v___y_966_);
v_toCold_975_ = lean_ctor_get(v___y_967_, 0);
v_mctx_976_ = lean_ctor_get(v___x_974_, 0);
lean_inc_ref(v_mctx_976_);
lean_dec(v___x_974_);
v_lctx_977_ = lean_ctor_get(v___y_965_, 2);
v_options_978_ = lean_ctor_get(v_toCold_975_, 2);
lean_inc_ref(v_options_978_);
lean_inc_ref(v_lctx_977_);
v___x_979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_979_, 0, v_env_973_);
lean_ctor_set(v___x_979_, 1, v_mctx_976_);
lean_ctor_set(v___x_979_, 2, v_lctx_977_);
lean_ctor_set(v___x_979_, 3, v_options_978_);
v___x_980_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v_msgData_964_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_964_ = stack[0].m_obj;
lean_object* v___y_965_ = stack[1].m_obj;
lean_object* v___y_966_ = stack[2].m_obj;
lean_object* v___y_967_ = stack[3].m_obj;
lean_object* v___y_968_ = stack[4].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(lean_object* v_msgData_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(lean_object* v_ref_991_, lean_object* v_msgData_992_, uint8_t v_severity_993_, uint8_t v_isSilent_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___y_1001_; uint8_t v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; uint8_t v___y_1007_; lean_object* v_toCold_1008_; lean_object* v___y_1009_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1041_; uint8_t v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1065_; lean_object* v___y_1066_; uint8_t v___y_1067_; uint8_t v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; uint8_t v___y_1075_; uint8_t v___y_1076_; uint8_t v___y_1077_; uint8_t v___x_1088_; uint8_t v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; uint8_t v___y_1094_; uint8_t v___x_1102_; 
v___x_1088_ = 2;
v___x_1102_ = l_Lean_instBEqMessageSeverity_beq(v_severity_993_, v___x_1088_);
if (v___x_1102_ == 0)
{
v___y_1094_ = v___x_1102_;
goto v___jp_1093_;
}
else
{
uint8_t v___x_1103_; 
lean_inc_ref(v_msgData_992_);
v___x_1103_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_992_);
v___y_1094_ = v___x_1103_;
goto v___jp_1093_;
}
v___jp_1000_:
{
lean_object* v_currNamespace_1010_; lean_object* v_openDecls_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_env_1016_; lean_object* v_nextMacroScope_1017_; lean_object* v_ngen_1018_; lean_object* v_auxDeclNGen_1019_; lean_object* v_traceState_1020_; lean_object* v_cache_1021_; lean_object* v_recordedDeps_1022_; lean_object* v_messages_1023_; lean_object* v_infoState_1024_; lean_object* v_snapshotTasks_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1036_; 
v_currNamespace_1010_ = lean_ctor_get(v_toCold_1008_, 4);
v_openDecls_1011_ = lean_ctor_get(v_toCold_1008_, 5);
lean_inc(v_openDecls_1011_);
lean_inc(v_currNamespace_1010_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_currNamespace_1010_);
lean_ctor_set(v___x_1012_, 1, v_openDecls_1011_);
v___x_1013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___y_1006_);
lean_inc_ref(v___y_1003_);
lean_inc_ref(v___y_1005_);
v___x_1014_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1014_, 0, v___y_1005_);
lean_ctor_set(v___x_1014_, 1, v___y_1004_);
lean_ctor_set(v___x_1014_, 2, v___y_1001_);
lean_ctor_set(v___x_1014_, 3, v___y_1003_);
lean_ctor_set(v___x_1014_, 4, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*5, v___y_1007_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*5 + 1, v___y_1002_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*5 + 2, v_isSilent_994_);
v___x_1015_ = lean_st_ref_take(v___y_1009_);
v_env_1016_ = lean_ctor_get(v___x_1015_, 0);
v_nextMacroScope_1017_ = lean_ctor_get(v___x_1015_, 1);
v_ngen_1018_ = lean_ctor_get(v___x_1015_, 2);
v_auxDeclNGen_1019_ = lean_ctor_get(v___x_1015_, 3);
v_traceState_1020_ = lean_ctor_get(v___x_1015_, 4);
v_cache_1021_ = lean_ctor_get(v___x_1015_, 5);
v_recordedDeps_1022_ = lean_ctor_get(v___x_1015_, 6);
v_messages_1023_ = lean_ctor_get(v___x_1015_, 7);
v_infoState_1024_ = lean_ctor_get(v___x_1015_, 8);
v_snapshotTasks_1025_ = lean_ctor_get(v___x_1015_, 9);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1027_ = v___x_1015_;
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snapshotTasks_1025_);
lean_inc(v_infoState_1024_);
lean_inc(v_messages_1023_);
lean_inc(v_recordedDeps_1022_);
lean_inc(v_cache_1021_);
lean_inc(v_traceState_1020_);
lean_inc(v_auxDeclNGen_1019_);
lean_inc(v_ngen_1018_);
lean_inc(v_nextMacroScope_1017_);
lean_inc(v_env_1016_);
lean_dec(v___x_1015_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = l_Lean_MessageLog_add(v___x_1014_, v_messages_1023_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 7, v___x_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_env_1016_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_nextMacroScope_1017_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_ngen_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_auxDeclNGen_1019_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_traceState_1020_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v_cache_1021_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_recordedDeps_1022_);
lean_ctor_set(v_reuseFailAlloc_1035_, 7, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1035_, 8, v_infoState_1024_);
lean_ctor_set(v_reuseFailAlloc_1035_, 9, v_snapshotTasks_1025_);
v___x_1032_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_st_ref_put(v___y_1009_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1029_);
return v___x_1034_;
}
}
}
v___jp_1037_:
{
lean_object* v_fileName_1046_; lean_object* v_fileMap_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1063_; 
v_fileName_1046_ = lean_ctor_get(v___y_1041_, 0);
v_fileMap_1047_ = lean_ctor_get(v___y_1041_, 1);
v___x_1048_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_992_);
v___x_1049_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v___x_1048_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1063_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1063_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_inc_ref_n(v_fileMap_1047_, 2);
v___x_1054_ = l_Lean_FileMap_toPosition(v_fileMap_1047_, v___y_1044_);
lean_dec(v___y_1044_);
v___x_1055_ = l_Lean_FileMap_toPosition(v_fileMap_1047_, v___y_1045_);
lean_dec(v___y_1045_);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0));
if (v___y_1042_ == 0)
{
lean_del_object(v___x_1052_);
lean_dec_ref(v___y_1038_);
v___y_1001_ = v___x_1056_;
v___y_1002_ = v___y_1040_;
v___y_1003_ = v___x_1057_;
v___y_1004_ = v___x_1054_;
v___y_1005_ = v_fileName_1046_;
v___y_1006_ = v_a_1050_;
v___y_1007_ = v___y_1043_;
v_toCold_1008_ = v___y_1039_;
v___y_1009_ = v___y_998_;
goto v___jp_1000_;
}
else
{
uint8_t v___x_1058_; 
lean_inc(v_a_1050_);
v___x_1058_ = l_Lean_MessageData_hasTag(v___y_1038_, v_a_1050_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec_ref_known(v___x_1056_, 1);
lean_dec_ref(v___x_1054_);
lean_dec(v_a_1050_);
v___x_1059_ = lean_box(0);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1059_);
v___x_1061_ = v___x_1052_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_del_object(v___x_1052_);
v___y_1001_ = v___x_1056_;
v___y_1002_ = v___y_1040_;
v___y_1003_ = v___x_1057_;
v___y_1004_ = v___x_1054_;
v___y_1005_ = v_fileName_1046_;
v___y_1006_ = v_a_1050_;
v___y_1007_ = v___y_1043_;
v_toCold_1008_ = v___y_1039_;
v___y_1009_ = v___y_998_;
goto v___jp_1000_;
}
}
}
}
v___jp_1064_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Syntax_getTailPos_x3f(v___y_1069_, v___y_1070_);
lean_dec(v___y_1069_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_inc(v___y_1071_);
v___y_1038_ = v___y_1065_;
v___y_1039_ = v___y_1066_;
v___y_1040_ = v___y_1068_;
v___y_1041_ = v___y_1066_;
v___y_1042_ = v___y_1067_;
v___y_1043_ = v___y_1070_;
v___y_1044_ = v___y_1071_;
v___y_1045_ = v___y_1071_;
goto v___jp_1037_;
}
else
{
lean_object* v_val_1073_; 
v_val_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___y_1038_ = v___y_1065_;
v___y_1039_ = v___y_1066_;
v___y_1040_ = v___y_1068_;
v___y_1041_ = v___y_1066_;
v___y_1042_ = v___y_1067_;
v___y_1043_ = v___y_1070_;
v___y_1044_ = v___y_1071_;
v___y_1045_ = v_val_1073_;
goto v___jp_1037_;
}
}
v___jp_1074_:
{
lean_object* v_toCold_1078_; lean_object* v_ref_1079_; uint8_t v_suppressElabErrors_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v_ref_1084_; lean_object* v___x_1085_; 
v_toCold_1078_ = lean_ctor_get(v___y_997_, 0);
v_ref_1079_ = lean_ctor_get(v___y_997_, 2);
v_suppressElabErrors_1080_ = lean_ctor_get_uint8(v___y_997_, sizeof(void*)*3 + 2);
v___x_1081_ = lean_box(v_suppressElabErrors_1080_);
v___x_1082_ = lean_box(v___y_1075_);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1083_, 0, v___x_1081_);
lean_closure_set(v___f_1083_, 1, v___x_1082_);
v_ref_1084_ = l_Lean_replaceRef(v_ref_991_, v_ref_1079_);
v___x_1085_ = l_Lean_Syntax_getPos_x3f(v_ref_1084_, v___y_1076_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___y_1065_ = v___f_1083_;
v___y_1066_ = v_toCold_1078_;
v___y_1067_ = v_suppressElabErrors_1080_;
v___y_1068_ = v___y_1077_;
v___y_1069_ = v_ref_1084_;
v___y_1070_ = v___y_1076_;
v___y_1071_ = v___x_1086_;
goto v___jp_1064_;
}
else
{
lean_object* v_val_1087_; 
v_val_1087_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v___x_1085_, 1);
v___y_1065_ = v___f_1083_;
v___y_1066_ = v_toCold_1078_;
v___y_1067_ = v_suppressElabErrors_1080_;
v___y_1068_ = v___y_1077_;
v___y_1069_ = v_ref_1084_;
v___y_1070_ = v___y_1076_;
v___y_1071_ = v_val_1087_;
goto v___jp_1064_;
}
}
v___jp_1089_:
{
if (v___y_1092_ == 0)
{
v___y_1075_ = v___y_1090_;
v___y_1076_ = v___y_1091_;
v___y_1077_ = v_severity_993_;
goto v___jp_1074_;
}
else
{
v___y_1075_ = v___y_1090_;
v___y_1076_ = v___y_1091_;
v___y_1077_ = v___x_1088_;
goto v___jp_1074_;
}
}
v___jp_1093_:
{
if (v___y_1094_ == 0)
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = 1;
v___x_1096_ = l_Lean_instBEqMessageSeverity_beq(v_severity_993_, v___x_1095_);
if (v___x_1096_ == 0)
{
v___y_1090_ = v___y_1094_;
v___y_1091_ = v___y_1094_;
v___y_1092_ = v___x_1096_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_997_);
v___x_1098_ = l_Lean_warningAsError;
v___x_1099_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v___x_1097_, v___x_1098_);
lean_dec_ref(v___x_1097_);
v___y_1090_ = v___y_1094_;
v___y_1091_ = v___y_1094_;
v___y_1092_ = v___x_1099_;
goto v___jp_1089_;
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref(v_msgData_992_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_991_ = stack[0].m_obj;
lean_object* v_msgData_992_ = stack[1].m_obj;
uint8_t v_severity_993_ = stack[2].m_num;
uint8_t v_isSilent_994_ = stack[3].m_num;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v___y_996_ = stack[5].m_obj;
lean_object* v___y_997_ = stack[6].m_obj;
lean_object* v___y_998_ = stack[7].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_991_, v_msgData_992_, v_severity_993_, v_isSilent_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_ref_1105_, lean_object* v_msgData_1106_, lean_object* v_severity_1107_, lean_object* v_isSilent_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_severity_boxed_1114_; uint8_t v_isSilent_boxed_1115_; lean_object* v_res_1116_; 
v_severity_boxed_1114_ = lean_unbox(v_severity_1107_);
v_isSilent_boxed_1115_ = lean_unbox(v_isSilent_1108_);
v_res_1116_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1105_, v_msgData_1106_, v_severity_boxed_1114_, v_isSilent_boxed_1115_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v_ref_1105_);
return v_res_1116_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(lean_object* v_msgData_1117_, uint8_t v_severity_1118_, uint8_t v_isSilent_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_ref_1127_; lean_object* v___x_1128_; 
v_ref_1127_ = lean_ctor_get(v___y_1124_, 2);
v___x_1128_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1127_, v_msgData_1117_, v_severity_1118_, v_isSilent_1119_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1117_ = stack[0].m_obj;
uint8_t v_severity_1118_ = stack[1].m_num;
uint8_t v_isSilent_1119_ = stack[2].m_num;
lean_object* v___y_1120_ = stack[3].m_obj;
lean_object* v___y_1121_ = stack[4].m_obj;
lean_object* v___y_1122_ = stack[5].m_obj;
lean_object* v___y_1123_ = stack[6].m_obj;
lean_object* v___y_1124_ = stack[7].m_obj;
lean_object* v___y_1125_ = stack[8].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1117_, v_severity_1118_, v_isSilent_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(lean_object* v_msgData_1130_, lean_object* v_severity_1131_, lean_object* v_isSilent_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v_severity_boxed_1140_; uint8_t v_isSilent_boxed_1141_; lean_object* v_res_1142_; 
v_severity_boxed_1140_ = lean_unbox(v_severity_1131_);
v_isSilent_boxed_1141_ = lean_unbox(v_isSilent_1132_);
v_res_1142_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1130_, v_severity_boxed_1140_, v_isSilent_boxed_1141_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1142_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(lean_object* v_msgData_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = 2;
v___x_1152_ = 0;
v___x_1153_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1143_, v___x_1151_, v___x_1152_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1153_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1143_ = stack[0].m_obj;
lean_object* v___y_1144_ = stack[1].m_obj;
lean_object* v___y_1145_ = stack[2].m_obj;
lean_object* v___y_1146_ = stack[3].m_obj;
lean_object* v___y_1147_ = stack[4].m_obj;
lean_object* v___y_1148_ = stack[5].m_obj;
lean_object* v___y_1149_ = stack[6].m_obj;
lean_object* v_res_1154_;
v_res_1154_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v_msgData_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
stack->m_obj
 = v_res_1154_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(lean_object* v_msgData_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v_msgData_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1163_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_){
_start:
{
lean_object* v_a_1172_; uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1176_ == 0)
{
lean_inc_ref(v_b_1170_);
return v_b_1170_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_a_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_a_1179_ = lean_array_uget_borrowed(v_as_1167_, v_i_1169_);
v___x_1180_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
lean_inc(v_a_1179_);
v___x_1181_ = l_Lean_Syntax_isOfKind(v_a_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
v_a_1172_ = v___x_1178_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = l_Lean_Syntax_getArg(v_a_1179_, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_1183_);
v___x_1185_ = l_Lean_Syntax_isOfKind(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_dec(v___x_1183_);
v_a_1172_ = v___x_1178_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1186_ = l_Lean_TSyntax_getId(v___x_1183_);
lean_dec(v___x_1183_);
v___x_1187_ = l_Lean_extractMacroScopes(v___x_1186_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1177_);
return v___x_1190_;
}
}
}
v___jp_1171_:
{
size_t v___x_1173_; size_t v___x_1174_; 
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1169_, v___x_1173_);
v_i_1169_ = v___x_1174_;
v_b_1170_ = v_a_1172_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1167_ = stack[0].m_obj;
size_t v_sz_1168_ = stack[1].m_num;
size_t v_i_1169_ = stack[2].m_num;
lean_object* v_b_1170_ = stack[3].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_1167_, v_sz_1168_, v_i_1169_, v_b_1170_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___boxed(lean_object* v_as_1192_, lean_object* v_sz_1193_, lean_object* v_i_1194_, lean_object* v_b_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1193_);
lean_dec(v_sz_1193_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_1192_, v_sz_boxed_1196_, v_i_boxed_1197_, v_b_1195_);
lean_dec_ref(v_b_1195_);
lean_dec_ref(v_as_1192_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v_ks_1203_; lean_object* v_vs_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1228_; 
v_ks_1203_ = lean_ctor_get(v_x_1199_, 0);
v_vs_1204_ = lean_ctor_get(v_x_1199_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1206_ = v_x_1199_;
v_isShared_1207_ = v_isSharedCheck_1228_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_vs_1204_);
lean_inc(v_ks_1203_);
lean_dec(v_x_1199_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1228_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_array_get_size(v_ks_1203_);
v___x_1209_ = lean_nat_dec_lt(v_x_1200_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_dec(v_x_1200_);
v___x_1210_ = lean_array_push(v_ks_1203_, v_x_1201_);
v___x_1211_ = lean_array_push(v_vs_1204_, v_x_1202_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1211_);
lean_ctor_set(v___x_1206_, 0, v___x_1210_);
v___x_1213_ = v___x_1206_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v_k_x27_1215_; uint8_t v___x_1216_; 
v_k_x27_1215_ = lean_array_fget_borrowed(v_ks_1203_, v_x_1200_);
v___x_1216_ = l_Lean_instBEqMVarId_beq(v_x_1201_, v_k_x27_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1218_; 
if (v_isShared_1207_ == 0)
{
v___x_1218_ = v___x_1206_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_ks_1203_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_vs_1204_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_x_1200_, v___x_1219_);
lean_dec(v_x_1200_);
v_x_1199_ = v___x_1218_;
v_x_1200_ = v___x_1220_;
goto _start;
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = lean_array_fset(v_ks_1203_, v_x_1200_, v_x_1201_);
v___x_1224_ = lean_array_fset(v_vs_1204_, v_x_1200_, v_x_1202_);
lean_dec(v_x_1200_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1224_);
lean_ctor_set(v___x_1206_, 0, v___x_1223_);
v___x_1226_ = v___x_1206_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(lean_object* v_n_1229_, lean_object* v_k_1230_, lean_object* v_v_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_n_1229_, v___x_1232_, v_k_1230_, v_v_1231_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1234_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(lean_object* v_x_1235_, size_t v_x_1236_, size_t v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 0)
{
lean_object* v_es_1240_; size_t v___x_1241_; size_t v___x_1242_; lean_object* v_j_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_es_1240_ = lean_ctor_get(v_x_1235_, 0);
v___x_1241_ = ((size_t)31ULL);
v___x_1242_ = lean_usize_land(v_x_1236_, v___x_1241_);
v_j_1243_ = lean_usize_to_nat(v___x_1242_);
v___x_1244_ = lean_array_get_size(v_es_1240_);
v___x_1245_ = lean_nat_dec_lt(v_j_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec(v_j_1243_);
lean_dec(v_x_1239_);
lean_dec(v_x_1238_);
return v_x_1235_;
}
else
{
lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1284_; 
lean_inc_ref(v_es_1240_);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v_x_1235_, 0);
lean_dec(v_unused_1285_);
v___x_1247_ = v_x_1235_;
v_isShared_1248_ = v_isSharedCheck_1284_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v_x_1235_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1284_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_v_1249_; lean_object* v___x_1250_; lean_object* v_xs_x27_1251_; lean_object* v___y_1253_; 
v_v_1249_ = lean_array_fget(v_es_1240_, v_j_1243_);
v___x_1250_ = lean_box(0);
v_xs_x27_1251_ = lean_array_fset(v_es_1240_, v_j_1243_, v___x_1250_);
switch(lean_obj_tag(v_v_1249_))
{
case 0:
{
lean_object* v_key_1258_; lean_object* v_val_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1269_; 
v_key_1258_ = lean_ctor_get(v_v_1249_, 0);
v_val_1259_ = lean_ctor_get(v_v_1249_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_v_1249_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1261_ = v_v_1249_;
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_val_1259_);
lean_inc(v_key_1258_);
lean_dec(v_v_1249_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Lean_instBEqMVarId_beq(v_x_1238_, v_key_1258_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_del_object(v___x_1261_);
v___x_1264_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1258_, v_val_1259_, v_x_1238_, v_x_1239_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___y_1253_ = v___x_1265_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1267_; 
lean_dec(v_val_1259_);
lean_dec(v_key_1258_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_x_1239_);
lean_ctor_set(v___x_1261_, 0, v_x_1238_);
v___x_1267_ = v___x_1261_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_x_1238_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_x_1239_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v___y_1253_ = v___x_1267_;
goto v___jp_1252_;
}
}
}
}
case 1:
{
lean_object* v_node_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1282_; 
v_node_1270_ = lean_ctor_get(v_v_1249_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_v_1249_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1272_ = v_v_1249_;
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_node_1270_);
lean_dec(v_v_1249_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1274_ = ((size_t)5ULL);
v___x_1275_ = lean_usize_shift_right(v_x_1236_, v___x_1274_);
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_x_1237_, v___x_1276_);
v___x_1278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_node_1270_, v___x_1275_, v___x_1277_, v_x_1238_, v_x_1239_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1278_);
v___x_1280_ = v___x_1272_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v___y_1253_ = v___x_1280_;
goto v___jp_1252_;
}
}
}
default: 
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_x_1238_);
lean_ctor_set(v___x_1283_, 1, v_x_1239_);
v___y_1253_ = v___x_1283_;
goto v___jp_1252_;
}
}
v___jp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_array_fset(v_xs_x27_1251_, v_j_1243_, v___y_1253_);
lean_dec(v_j_1243_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1254_);
v___x_1256_ = v___x_1247_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
else
{
lean_object* v_ks_1286_; lean_object* v_vs_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1305_; 
v_ks_1286_ = lean_ctor_get(v_x_1235_, 0);
v_vs_1287_ = lean_ctor_get(v_x_1235_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1289_ = v_x_1235_;
v_isShared_1290_ = v_isSharedCheck_1305_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_vs_1287_);
lean_inc(v_ks_1286_);
lean_dec(v_x_1235_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1305_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_ks_1286_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_vs_1287_);
v___x_1292_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v_newNode_1293_; size_t v___x_1294_; uint8_t v___x_1295_; 
v_newNode_1293_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v___x_1292_, v_x_1238_, v_x_1239_);
v___x_1294_ = ((size_t)7ULL);
v___x_1295_ = lean_usize_dec_le(v___x_1294_, v_x_1237_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1293_);
v___x_1297_ = lean_unsigned_to_nat(4u);
v___x_1298_ = lean_nat_dec_lt(v___x_1296_, v___x_1297_);
lean_dec(v___x_1296_);
if (v___x_1298_ == 0)
{
lean_object* v_ks_1299_; lean_object* v_vs_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_ks_1299_ = lean_ctor_get(v_newNode_1293_, 0);
lean_inc_ref(v_ks_1299_);
v_vs_1300_ = lean_ctor_get(v_newNode_1293_, 1);
lean_inc_ref(v_vs_1300_);
lean_dec_ref(v_newNode_1293_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0);
v___x_1303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_x_1237_, v_ks_1299_, v_vs_1300_, v___x_1301_, v___x_1302_);
lean_dec_ref(v_vs_1300_);
lean_dec_ref(v_ks_1299_);
return v___x_1303_;
}
else
{
return v_newNode_1293_;
}
}
else
{
return v_newNode_1293_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1235_ = stack[0].m_obj;
size_t v_x_1236_ = stack[1].m_num;
size_t v_x_1237_ = stack[2].m_num;
lean_object* v_x_1238_ = stack[3].m_obj;
lean_object* v_x_1239_ = stack[4].m_obj;
lean_object* v_res_1306_;
v_res_1306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1235_, v_x_1236_, v_x_1237_, v_x_1238_, v_x_1239_);
stack->m_obj
 = v_res_1306_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(size_t v_depth_1307_, lean_object* v_keys_1308_, lean_object* v_vals_1309_, lean_object* v_i_1310_, lean_object* v_entries_1311_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_array_get_size(v_keys_1308_);
v___x_1313_ = lean_nat_dec_lt(v_i_1310_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec(v_i_1310_);
return v_entries_1311_;
}
else
{
lean_object* v_k_1314_; lean_object* v_v_1315_; uint64_t v___x_1316_; size_t v_h_1317_; size_t v___x_1318_; lean_object* v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v_h_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_k_1314_ = lean_array_fget_borrowed(v_keys_1308_, v_i_1310_);
v_v_1315_ = lean_array_fget_borrowed(v_vals_1309_, v_i_1310_);
v___x_1316_ = l_Lean_instHashableMVarId_hash(v_k_1314_);
v_h_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = ((size_t)5ULL);
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_sub(v_depth_1307_, v___x_1320_);
v___x_1322_ = lean_usize_mul(v___x_1318_, v___x_1321_);
v_h_1323_ = lean_usize_shift_right(v_h_1317_, v___x_1322_);
v___x_1324_ = lean_nat_add(v_i_1310_, v___x_1319_);
lean_dec(v_i_1310_);
lean_inc(v_v_1315_);
lean_inc(v_k_1314_);
v___x_1325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_entries_1311_, v_h_1323_, v_depth_1307_, v_k_1314_, v_v_1315_);
v_i_1310_ = v___x_1324_;
v_entries_1311_ = v___x_1325_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1307_ = stack[0].m_num;
lean_object* v_keys_1308_ = stack[1].m_obj;
lean_object* v_vals_1309_ = stack[2].m_obj;
lean_object* v_i_1310_ = stack[3].m_obj;
lean_object* v_entries_1311_ = stack[4].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_1307_, v_keys_1308_, v_vals_1309_, v_i_1310_, v_entries_1311_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_depth_1328_, lean_object* v_keys_1329_, lean_object* v_vals_1330_, lean_object* v_i_1331_, lean_object* v_entries_1332_){
_start:
{
size_t v_depth_boxed_1333_; lean_object* v_res_1334_; 
v_depth_boxed_1333_ = lean_unbox_usize(v_depth_1328_);
lean_dec(v_depth_1328_);
v_res_1334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_boxed_1333_, v_keys_1329_, v_vals_1330_, v_i_1331_, v_entries_1332_);
lean_dec_ref(v_vals_1330_);
lean_dec_ref(v_keys_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
size_t v_x_23134__boxed_1340_; size_t v_x_23135__boxed_1341_; lean_object* v_res_1342_; 
v_x_23134__boxed_1340_ = lean_unbox_usize(v_x_1336_);
lean_dec(v_x_1336_);
v_x_23135__boxed_1341_ = lean_unbox_usize(v_x_1337_);
lean_dec(v_x_1337_);
v_res_1342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1335_, v_x_23134__boxed_1340_, v_x_23135__boxed_1341_, v_x_1338_, v_x_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
uint64_t v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = l_Lean_instHashableMVarId_hash(v_x_1344_);
v___x_1347_ = lean_uint64_to_usize(v___x_1346_);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1343_, v___x_1347_, v___x_1348_, v_x_1344_, v_x_1345_);
return v___x_1349_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(lean_object* v_mvarId_1350_, lean_object* v_val_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v_mctx_1355_; lean_object* v_cache_1356_; lean_object* v_zetaDeltaFVarIds_1357_; lean_object* v_postponed_1358_; lean_object* v_diag_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1389_; 
v___x_1354_ = lean_st_ref_take(v___y_1352_);
v_mctx_1355_ = lean_ctor_get(v___x_1354_, 0);
v_cache_1356_ = lean_ctor_get(v___x_1354_, 1);
v_zetaDeltaFVarIds_1357_ = lean_ctor_get(v___x_1354_, 2);
v_postponed_1358_ = lean_ctor_get(v___x_1354_, 3);
v_diag_1359_ = lean_ctor_get(v___x_1354_, 4);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1361_ = v___x_1354_;
v_isShared_1362_ = v_isSharedCheck_1389_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_diag_1359_);
lean_inc(v_postponed_1358_);
lean_inc(v_zetaDeltaFVarIds_1357_);
lean_inc(v_cache_1356_);
lean_inc(v_mctx_1355_);
lean_dec(v___x_1354_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1389_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_depth_1363_; lean_object* v_levelAssignDepth_1364_; lean_object* v_lmvarCounter_1365_; lean_object* v_mvarCounter_1366_; lean_object* v_lDecls_1367_; lean_object* v_decls_1368_; lean_object* v_userNames_1369_; lean_object* v_lAssignment_1370_; lean_object* v_eAssignment_1371_; lean_object* v_dAssignment_1372_; lean_object* v_instanceTypedMVars_1373_; lean_object* v_synthNormMemo_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1388_; 
v_depth_1363_ = lean_ctor_get(v_mctx_1355_, 0);
v_levelAssignDepth_1364_ = lean_ctor_get(v_mctx_1355_, 1);
v_lmvarCounter_1365_ = lean_ctor_get(v_mctx_1355_, 2);
v_mvarCounter_1366_ = lean_ctor_get(v_mctx_1355_, 3);
v_lDecls_1367_ = lean_ctor_get(v_mctx_1355_, 4);
v_decls_1368_ = lean_ctor_get(v_mctx_1355_, 5);
v_userNames_1369_ = lean_ctor_get(v_mctx_1355_, 6);
v_lAssignment_1370_ = lean_ctor_get(v_mctx_1355_, 7);
v_eAssignment_1371_ = lean_ctor_get(v_mctx_1355_, 8);
v_dAssignment_1372_ = lean_ctor_get(v_mctx_1355_, 9);
v_instanceTypedMVars_1373_ = lean_ctor_get(v_mctx_1355_, 10);
v_synthNormMemo_1374_ = lean_ctor_get(v_mctx_1355_, 11);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_mctx_1355_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1376_ = v_mctx_1355_;
v_isShared_1377_ = v_isSharedCheck_1388_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_synthNormMemo_1374_);
lean_inc(v_instanceTypedMVars_1373_);
lean_inc(v_dAssignment_1372_);
lean_inc(v_eAssignment_1371_);
lean_inc(v_lAssignment_1370_);
lean_inc(v_userNames_1369_);
lean_inc(v_decls_1368_);
lean_inc(v_lDecls_1367_);
lean_inc(v_mvarCounter_1366_);
lean_inc(v_lmvarCounter_1365_);
lean_inc(v_levelAssignDepth_1364_);
lean_inc(v_depth_1363_);
lean_dec(v_mctx_1355_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1388_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_eAssignment_1371_, v_mvarId_1350_, v_val_1351_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 8, v___x_1379_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_depth_1363_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_levelAssignDepth_1364_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_lmvarCounter_1365_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_mvarCounter_1366_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_lDecls_1367_);
lean_ctor_set(v_reuseFailAlloc_1387_, 5, v_decls_1368_);
lean_ctor_set(v_reuseFailAlloc_1387_, 6, v_userNames_1369_);
lean_ctor_set(v_reuseFailAlloc_1387_, 7, v_lAssignment_1370_);
lean_ctor_set(v_reuseFailAlloc_1387_, 8, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1387_, 9, v_dAssignment_1372_);
lean_ctor_set(v_reuseFailAlloc_1387_, 10, v_instanceTypedMVars_1373_);
lean_ctor_set(v_reuseFailAlloc_1387_, 11, v_synthNormMemo_1374_);
v___x_1381_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1383_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1381_);
v___x_1383_ = v___x_1361_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_cache_1356_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_zetaDeltaFVarIds_1357_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_postponed_1358_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_diag_1359_);
v___x_1383_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_st_ref_put(v___y_1352_, v___x_1383_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1378_);
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1350_ = stack[0].m_obj;
lean_object* v_val_1351_ = stack[1].m_obj;
lean_object* v___y_1352_ = stack[2].m_obj;
lean_object* v_res_1390_;
v_res_1390_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1350_, v_val_1351_, v___y_1352_);
stack->m_obj
 = v_res_1390_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(lean_object* v_mvarId_1391_, lean_object* v_val_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1391_, v_val_1392_, v___y_1393_);
lean_dec(v___y_1393_);
return v_res_1395_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = l_Lean_NameSet_empty;
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__0));
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__2));
v___x_1403_ = l_Lean_stringToMessageData(v___x_1402_);
return v___x_1403_;
}
}
lean_object* l_Lean_Elab_Tactic_renameInaccessibles(lean_object* v_mvarId_1406_, lean_object* v_hs_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1415_ = lean_array_get_size(v_hs_1407_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_nat_dec_eq(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_inc(v_mvarId_1406_);
v___x_1418_ = l_Lean_MVarId_getDecl(v_mvarId_1406_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1521_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1521_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1521_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v_fst_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1519_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_sz_1425_ = lean_array_size(v_hs_1407_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_hs_1407_, v_sz_1425_, v___x_1426_, v___x_1424_);
v_fst_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1427_, 1);
lean_dec(v_unused_1520_);
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1519_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_fst_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1519_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_fst_1428_) == 0)
{
lean_object* v___x_1433_; 
lean_del_object(v___x_1430_);
lean_dec(v_a_1419_);
lean_dec_ref(v_hs_1407_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_mvarId_1406_);
v___x_1433_ = v___x_1421_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_mvarId_1406_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
else
{
lean_object* v_val_1435_; 
v_val_1435_ = lean_ctor_get(v_fst_1428_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v_fst_1428_, 1);
if (lean_obj_tag(v_val_1435_) == 1)
{
lean_object* v_val_1436_; lean_object* v_userName_1437_; lean_object* v_lctx_1438_; lean_object* v_type_1439_; lean_object* v_localInstances_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_del_object(v___x_1421_);
v_val_1436_ = lean_ctor_get(v_val_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v_val_1435_, 1);
v_userName_1437_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_userName_1437_);
v_lctx_1438_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref_n(v_lctx_1438_, 2);
v_type_1439_ = lean_ctor_get(v_a_1419_, 2);
lean_inc_ref(v_type_1439_);
v_localInstances_1440_ = lean_ctor_get(v_a_1419_, 4);
lean_inc_ref(v_localInstances_1440_);
lean_dec(v_a_1419_);
v___x_1441_ = lean_local_ctx_num_indices(v_lctx_1438_);
v___x_1442_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__1, &l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1442_);
lean_ctor_set(v___x_1430_, 0, v_hs_1407_);
v___x_1444_ = v___x_1430_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_hs_1407_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_lctx_1438_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v___x_1441_, v___x_1441_, v_val_1436_, v___x_1416_, v___x_1445_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_val_1436_);
lean_dec(v___x_1441_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v_snd_1448_; lean_object* v_snd_1449_; lean_object* v_fst_1450_; lean_object* v_fst_1451_; lean_object* v_fst_1452_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v_snd_1448_ = lean_ctor_get(v_a_1447_, 1);
lean_inc(v_snd_1448_);
v_snd_1449_ = lean_ctor_get(v_snd_1448_, 1);
lean_inc(v_snd_1449_);
v_fst_1450_ = lean_ctor_get(v_a_1447_, 0);
lean_inc(v_fst_1450_);
lean_dec(v_a_1447_);
v_fst_1451_ = lean_ctor_get(v_snd_1448_, 0);
lean_inc(v_fst_1451_);
lean_dec(v_snd_1448_);
v_fst_1452_ = lean_ctor_get(v_snd_1449_, 0);
lean_inc(v_fst_1452_);
lean_dec(v_snd_1449_);
v___x_1495_ = lean_array_get_size(v_fst_1451_);
lean_dec(v_fst_1451_);
v___x_1496_ = lean_nat_dec_eq(v___x_1495_, v___x_1416_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__3, &l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3);
v___x_1498_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v___x_1497_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec_ref_known(v___x_1498_, 1);
v___y_1454_ = v_a_1408_;
v___y_1455_ = v_a_1409_;
v___y_1456_ = v_a_1410_;
v___y_1457_ = v_a_1411_;
v___y_1458_ = v_a_1412_;
v___y_1459_ = v_a_1413_;
goto v___jp_1453_;
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_fst_1452_);
lean_dec(v_fst_1450_);
lean_dec_ref(v_localInstances_1440_);
lean_dec_ref(v_type_1439_);
lean_dec(v_userName_1437_);
lean_dec(v_mvarId_1406_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
v___y_1454_ = v_a_1408_;
v___y_1455_ = v_a_1409_;
v___y_1456_ = v_a_1410_;
v___y_1457_ = v_a_1411_;
v___y_1458_ = v_a_1412_;
v___y_1459_ = v_a_1413_;
goto v___jp_1453_;
}
v___jp_1453_:
{
uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = 2;
v___x_1461_ = l_Lean_Meta_mkFreshExprMVarAt(v_fst_1450_, v_localInstances_1440_, v_type_1439_, v___x_1460_, v_userName_1437_, v___x_1416_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; size_t v_sz_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Expr_mvarId_x21(v_a_1462_);
v_sz_1464_ = lean_array_size(v_fst_1452_);
v___x_1465_ = lean_box_usize(v_sz_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1));
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1467_, 0, v_fst_1452_);
lean_closure_set(v___f_1467_, 1, v___x_1465_);
lean_closure_set(v___f_1467_, 2, v___x_1466_);
lean_closure_set(v___f_1467_, 3, v___x_1423_);
lean_inc(v___x_1463_);
v___x_1468_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed), 10, 3);
lean_closure_set(v___x_1468_, 0, lean_box(0));
lean_closure_set(v___x_1468_, 1, v___x_1463_);
lean_closure_set(v___x_1468_, 2, v___f_1467_);
v___x_1469_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v___x_1468_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref_known(v___x_1469_, 1);
v___x_1470_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1406_, v_a_1462_, v___y_1457_);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1478_);
v___x_1472_ = v___x_1470_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v___x_1470_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1463_);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1463_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v___x_1463_);
lean_dec(v_a_1462_);
lean_dec(v_mvarId_1406_);
v_a_1479_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1469_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1469_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_fst_1452_);
lean_dec(v_mvarId_1406_);
v_a_1487_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1461_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1461_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v_localInstances_1440_);
lean_dec_ref(v_type_1439_);
lean_dec(v_userName_1437_);
lean_dec(v_mvarId_1406_);
v_a_1507_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1446_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1446_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
else
{
lean_object* v___x_1517_; 
lean_dec(v_val_1435_);
lean_del_object(v___x_1430_);
lean_dec(v_a_1419_);
lean_dec_ref(v_hs_1407_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_mvarId_1406_);
v___x_1517_ = v___x_1421_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_mvarId_1406_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_hs_1407_);
lean_dec(v_mvarId_1406_);
v_a_1522_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1418_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1418_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v___x_1530_; 
lean_dec_ref(v_hs_1407_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_mvarId_1406_);
return v___x_1530_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_renameInaccessibles_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1406_ = stack[0].m_obj;
lean_object* v_hs_1407_ = stack[1].m_obj;
lean_object* v_a_1408_ = stack[2].m_obj;
lean_object* v_a_1409_ = stack[3].m_obj;
lean_object* v_a_1410_ = stack[4].m_obj;
lean_object* v_a_1411_ = stack[5].m_obj;
lean_object* v_a_1412_ = stack[6].m_obj;
lean_object* v_a_1413_ = stack[7].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Lean_Elab_Tactic_renameInaccessibles(v_mvarId_1406_, v_hs_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___boxed(lean_object* v_mvarId_1532_, lean_object* v_hs_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Elab_Tactic_renameInaccessibles(v_mvarId_1532_, v_hs_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
return v_res_1541_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(lean_object* v_00_u03b1_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1543_ = stack[1].m_obj;
lean_object* v___y_1544_ = stack[2].m_obj;
lean_object* v___y_1545_ = stack[3].m_obj;
lean_object* v___y_1546_ = stack[4].m_obj;
lean_object* v___y_1547_ = stack[5].m_obj;
lean_object* v___y_1548_ = stack[6].m_obj;
lean_object* v___y_1549_ = stack[7].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(lean_box(0), v_x_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(v_00_u03b1_1553_, v_x_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1562_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(lean_object* v_mvarId_1563_, lean_object* v_val_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1563_, v_val_1564_, v___y_1568_);
return v___x_1572_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1563_ = stack[0].m_obj;
lean_object* v_val_1564_ = stack[1].m_obj;
lean_object* v___y_1565_ = stack[2].m_obj;
lean_object* v___y_1566_ = stack[3].m_obj;
lean_object* v___y_1567_ = stack[4].m_obj;
lean_object* v___y_1568_ = stack[5].m_obj;
lean_object* v___y_1569_ = stack[6].m_obj;
lean_object* v___y_1570_ = stack[7].m_obj;
lean_object* v_res_1573_;
v_res_1573_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(v_mvarId_1563_, v_val_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
stack->m_obj
 = v_res_1573_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(lean_object* v_mvarId_1574_, lean_object* v_val_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(v_mvarId_1574_, v_val_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1583_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(lean_object* v_upperBound_1584_, lean_object* v___x_1585_, lean_object* v_val_1586_, lean_object* v_inst_1587_, lean_object* v_R_1588_, lean_object* v_a_1589_, lean_object* v_b_1590_, lean_object* v_c_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_1584_, v___x_1585_, v_val_1586_, v_a_1589_, v_b_1590_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1584_ = stack[0].m_obj;
lean_object* v___x_1585_ = stack[1].m_obj;
lean_object* v_val_1586_ = stack[2].m_obj;
lean_object* v_a_1589_ = stack[5].m_obj;
lean_object* v_b_1590_ = stack[6].m_obj;
lean_object* v___y_1592_ = stack[8].m_obj;
lean_object* v___y_1593_ = stack[9].m_obj;
lean_object* v___y_1594_ = stack[10].m_obj;
lean_object* v___y_1595_ = stack[11].m_obj;
lean_object* v___y_1596_ = stack[12].m_obj;
lean_object* v___y_1597_ = stack[13].m_obj;
lean_object* v_res_1600_;
v_res_1600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(v_upperBound_1584_, v___x_1585_, v_val_1586_, lean_box(0), lean_box(0), v_a_1589_, v_b_1590_, lean_box(0), v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
stack->m_obj
 = v_res_1600_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(lean_object* v_upperBound_1601_, lean_object* v___x_1602_, lean_object* v_val_1603_, lean_object* v_inst_1604_, lean_object* v_R_1605_, lean_object* v_a_1606_, lean_object* v_b_1607_, lean_object* v_c_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(v_upperBound_1601_, v___x_1602_, v_val_1603_, v_inst_1604_, v_R_1605_, v_a_1606_, v_b_1607_, v_c_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_val_1603_);
lean_dec(v___x_1602_);
lean_dec(v_upperBound_1601_);
return v_res_1616_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1617_ = stack[0].m_obj;
lean_object* v___y_1618_ = stack[1].m_obj;
lean_object* v___y_1619_ = stack[2].m_obj;
lean_object* v___y_1620_ = stack[3].m_obj;
lean_object* v___y_1621_ = stack[4].m_obj;
lean_object* v___y_1622_ = stack[5].m_obj;
lean_object* v_res_1625_;
v_res_1625_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
stack->m_obj
 = v_res_1625_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1633_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1634_ = stack[0].m_obj;
lean_object* v___y_1635_ = stack[1].m_obj;
lean_object* v___y_1636_ = stack[2].m_obj;
lean_object* v___y_1637_ = stack[3].m_obj;
lean_object* v___y_1638_ = stack[4].m_obj;
lean_object* v___y_1639_ = stack[5].m_obj;
lean_object* v_res_1642_;
v_res_1642_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1650_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(lean_object* v_00_u03b1_1651_, lean_object* v_x_1652_, lean_object* v_ctx_x3f_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_1652_, v_ctx_x3f_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1652_ = stack[1].m_obj;
lean_object* v_ctx_x3f_1653_ = stack[2].m_obj;
lean_object* v___y_1654_ = stack[3].m_obj;
lean_object* v___y_1655_ = stack[4].m_obj;
lean_object* v___y_1656_ = stack[5].m_obj;
lean_object* v___y_1657_ = stack[6].m_obj;
lean_object* v___y_1658_ = stack[7].m_obj;
lean_object* v___y_1659_ = stack[8].m_obj;
lean_object* v_res_1662_;
v_res_1662_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(lean_box(0), v_x_1652_, v_ctx_x3f_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
stack->m_obj
 = v_res_1662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_x_1664_, lean_object* v_ctx_x3f_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(v_00_u03b1_1663_, v_x_1664_, v_ctx_x3f_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(lean_object* v_00_u03b2_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_x_1675_, v_x_1676_, v_x_1677_);
return v___x_1678_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1679_, lean_object* v_x_1680_, size_t v_x_1681_, size_t v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1680_, v_x_1681_, v_x_1682_, v_x_1683_, v_x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1680_ = stack[1].m_obj;
size_t v_x_1681_ = stack[2].m_num;
size_t v_x_1682_ = stack[3].m_num;
lean_object* v_x_1683_ = stack[4].m_obj;
lean_object* v_x_1684_ = stack[5].m_obj;
lean_object* v_res_1686_;
v_res_1686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(lean_box(0), v_x_1680_, v_x_1681_, v_x_1682_, v_x_1683_, v_x_1684_);
stack->m_obj
 = v_res_1686_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_){
_start:
{
size_t v_x_24080__boxed_1693_; size_t v_x_24081__boxed_1694_; lean_object* v_res_1695_; 
v_x_24080__boxed_1693_ = lean_unbox_usize(v_x_1689_);
lean_dec(v_x_1689_);
v_x_24081__boxed_1694_ = lean_unbox_usize(v_x_1690_);
lean_dec(v_x_1690_);
v_res_1695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(v_00_u03b2_1687_, v_x_1688_, v_x_24080__boxed_1693_, v_x_24081__boxed_1694_, v_x_1691_, v_x_1692_);
return v_res_1695_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(lean_object* v_ref_1696_, lean_object* v_msgData_1697_, uint8_t v_severity_1698_, uint8_t v_isSilent_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1696_, v_msgData_1697_, v_severity_1698_, v_isSilent_1699_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1696_ = stack[0].m_obj;
lean_object* v_msgData_1697_ = stack[1].m_obj;
uint8_t v_severity_1698_ = stack[2].m_num;
uint8_t v_isSilent_1699_ = stack[3].m_num;
lean_object* v___y_1700_ = stack[4].m_obj;
lean_object* v___y_1701_ = stack[5].m_obj;
lean_object* v___y_1702_ = stack[6].m_obj;
lean_object* v___y_1703_ = stack[7].m_obj;
lean_object* v___y_1704_ = stack[8].m_obj;
lean_object* v___y_1705_ = stack[9].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_1696_, v_msgData_1697_, v_severity_1698_, v_isSilent_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(lean_object* v_ref_1709_, lean_object* v_msgData_1710_, lean_object* v_severity_1711_, lean_object* v_isSilent_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v_severity_boxed_1720_; uint8_t v_isSilent_boxed_1721_; lean_object* v_res_1722_; 
v_severity_boxed_1720_ = lean_unbox(v_severity_1711_);
v_isSilent_boxed_1721_ = lean_unbox(v_isSilent_1712_);
v_res_1722_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_1709_, v_msgData_1710_, v_severity_boxed_1720_, v_isSilent_boxed_1721_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v_ref_1709_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(lean_object* v_00_u03b2_1723_, lean_object* v_n_1724_, lean_object* v_k_1725_, lean_object* v_v_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v_n_1724_, v_k_1725_, v_v_1726_);
return v___x_1727_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1728_, size_t v_depth_1729_, lean_object* v_keys_1730_, lean_object* v_vals_1731_, lean_object* v_heq_1732_, lean_object* v_i_1733_, lean_object* v_entries_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_1729_, v_keys_1730_, v_vals_1731_, v_i_1733_, v_entries_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1729_ = stack[1].m_num;
lean_object* v_keys_1730_ = stack[2].m_obj;
lean_object* v_vals_1731_ = stack[3].m_obj;
lean_object* v_i_1733_ = stack[5].m_obj;
lean_object* v_entries_1734_ = stack[6].m_obj;
lean_object* v_res_1736_;
v_res_1736_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(lean_box(0), v_depth_1729_, v_keys_1730_, v_vals_1731_, lean_box(0), v_i_1733_, v_entries_1734_);
stack->m_obj
 = v_res_1736_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1737_, lean_object* v_depth_1738_, lean_object* v_keys_1739_, lean_object* v_vals_1740_, lean_object* v_heq_1741_, lean_object* v_i_1742_, lean_object* v_entries_1743_){
_start:
{
size_t v_depth_boxed_1744_; lean_object* v_res_1745_; 
v_depth_boxed_1744_ = lean_unbox_usize(v_depth_1738_);
lean_dec(v_depth_1738_);
v_res_1745_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(v_00_u03b2_1737_, v_depth_boxed_1744_, v_keys_1739_, v_vals_1740_, v_heq_1741_, v_i_1742_, v_entries_1743_);
lean_dec_ref(v_vals_1740_);
lean_dec_ref(v_keys_1739_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_x_1747_, v_x_1748_, v_x_1749_, v_x_1750_);
return v___x_1751_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_RenameInaccessibles(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_RenameInaccessibles(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
}
#ifdef __cplusplus
}
#endif
