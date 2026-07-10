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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_MacroScopesView_equalScope(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_9_ = lean_apply_7(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed(lean_object* v_x_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(v_x_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(lean_object* v_mvarId_19_, lean_object* v_x_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_28_, 0, v_x_20_);
lean_closure_set(v___f_28_, 1, v___y_21_);
lean_closure_set(v___f_28_, 2, v___y_22_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_19_, v___f_28_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
return v___x_29_;
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___boxed(lean_object* v_mvarId_38_, lean_object* v_x_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(v_mvarId_38_, v_x_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(lean_object* v_00_u03b1_48_, lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(lean_object* v_as_70_, size_t v_sz_71_, size_t v_i_72_, lean_object* v_b_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_usize_dec_lt(v_i_72_, v_sz_71_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_b_73_);
return v___x_82_;
}
else
{
lean_object* v_a_83_; lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_a_83_ = lean_array_uget_borrowed(v_as_70_, v_i_72_);
v_fst_84_ = lean_ctor_get(v_a_83_, 0);
v_snd_85_ = lean_ctor_get(v_a_83_, 1);
lean_inc(v_fst_84_);
v___x_86_ = l_Lean_mkFVar(v_fst_84_);
lean_inc(v_snd_85_);
v___x_87_ = l_Lean_Elab_Term_addLocalVarInfo(v_snd_85_, v___x_86_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v___x_88_; size_t v___x_89_; size_t v___x_90_; 
lean_dec_ref_known(v___x_87_, 1);
v___x_88_ = lean_box(0);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_add(v_i_72_, v___x_89_);
v_i_72_ = v___x_90_;
v_b_73_ = v___x_88_;
goto _start;
}
else
{
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0___boxed(lean_object* v_as_92_, lean_object* v_sz_93_, lean_object* v_i_94_, lean_object* v_b_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
size_t v_sz_boxed_103_; size_t v_i_boxed_104_; lean_object* v_res_105_; 
v_sz_boxed_103_ = lean_unbox_usize(v_sz_93_);
lean_dec(v_sz_93_);
v_i_boxed_104_ = lean_unbox_usize(v_i_94_);
lean_dec(v_i_94_);
v_res_105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_as_92_, v_sz_boxed_103_, v_i_boxed_104_, v_b_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec_ref(v_as_92_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___lam__0(lean_object* v_fst_106_, size_t v_sz_107_, size_t v___x_108_, lean_object* v___x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_fst_106_, v_sz_107_, v___x_108_, v___x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; 
v_unused_125_ = lean_ctor_get(v___x_117_, 0);
lean_dec(v_unused_125_);
v___x_119_ = v___x_117_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_dec(v___x_117_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_109_);
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_109_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed(lean_object* v_fst_126_, lean_object* v_sz_127_, lean_object* v___x_128_, lean_object* v___x_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
size_t v_sz_boxed_137_; size_t v___x_22435__boxed_138_; lean_object* v_res_139_; 
v_sz_boxed_137_ = lean_unbox_usize(v_sz_127_);
lean_dec(v_sz_127_);
v___x_22435__boxed_138_ = lean_unbox_usize(v___x_128_);
lean_dec(v___x_128_);
v_res_139_ = l_Lean_Elab_Tactic_renameInaccessibles___lam__0(v_fst_126_, v_sz_boxed_137_, v___x_22435__boxed_138_, v___x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v_fst_126_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_unsigned_to_nat(32u);
v___x_141_ = lean_mk_empty_array_with_capacity(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_143_ = ((size_t)5ULL);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_unsigned_to_nat(32u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_148_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_144_);
lean_ctor_set(v___x_148_, 3, v___x_144_);
lean_ctor_set_usize(v___x_148_, 4, v___x_143_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; lean_object* v_infoState_152_; lean_object* v_trees_153_; lean_object* v___x_154_; lean_object* v_infoState_155_; lean_object* v_env_156_; lean_object* v_nextMacroScope_157_; lean_object* v_ngen_158_; lean_object* v_auxDeclNGen_159_; lean_object* v_traceState_160_; lean_object* v_cache_161_; lean_object* v_messages_162_; lean_object* v_snapshotTasks_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_184_; 
v___x_151_ = lean_st_ref_get(v___y_149_);
v_infoState_152_ = lean_ctor_get(v___x_151_, 7);
lean_inc_ref(v_infoState_152_);
lean_dec(v___x_151_);
v_trees_153_ = lean_ctor_get(v_infoState_152_, 2);
lean_inc_ref(v_trees_153_);
lean_dec_ref(v_infoState_152_);
v___x_154_ = lean_st_ref_take(v___y_149_);
v_infoState_155_ = lean_ctor_get(v___x_154_, 7);
v_env_156_ = lean_ctor_get(v___x_154_, 0);
v_nextMacroScope_157_ = lean_ctor_get(v___x_154_, 1);
v_ngen_158_ = lean_ctor_get(v___x_154_, 2);
v_auxDeclNGen_159_ = lean_ctor_get(v___x_154_, 3);
v_traceState_160_ = lean_ctor_get(v___x_154_, 4);
v_cache_161_ = lean_ctor_get(v___x_154_, 5);
v_messages_162_ = lean_ctor_get(v___x_154_, 6);
v_snapshotTasks_163_ = lean_ctor_get(v___x_154_, 8);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_184_ == 0)
{
v___x_165_ = v___x_154_;
v_isShared_166_ = v_isSharedCheck_184_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_snapshotTasks_163_);
lean_inc(v_infoState_155_);
lean_inc(v_messages_162_);
lean_inc(v_cache_161_);
lean_inc(v_traceState_160_);
lean_inc(v_auxDeclNGen_159_);
lean_inc(v_ngen_158_);
lean_inc(v_nextMacroScope_157_);
lean_inc(v_env_156_);
lean_dec(v___x_154_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_184_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
uint8_t v_enabled_167_; lean_object* v_assignment_168_; lean_object* v_lazyAssignment_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_182_; 
v_enabled_167_ = lean_ctor_get_uint8(v_infoState_155_, sizeof(void*)*3);
v_assignment_168_ = lean_ctor_get(v_infoState_155_, 0);
v_lazyAssignment_169_ = lean_ctor_get(v_infoState_155_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_infoState_155_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_infoState_155_, 2);
lean_dec(v_unused_183_);
v___x_171_ = v_infoState_155_;
v_isShared_172_ = v_isSharedCheck_182_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_lazyAssignment_169_);
lean_inc(v_assignment_168_);
lean_dec(v_infoState_155_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_182_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 2, v___x_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_assignment_168_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_lazyAssignment_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v___x_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, sizeof(void*)*3, v_enabled_167_);
v___x_175_ = v_reuseFailAlloc_181_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 7, v___x_175_);
v___x_177_ = v___x_165_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_env_156_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_nextMacroScope_157_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_ngen_158_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v_auxDeclNGen_159_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v_traceState_160_);
lean_ctor_set(v_reuseFailAlloc_180_, 5, v_cache_161_);
lean_ctor_set(v_reuseFailAlloc_180_, 6, v_messages_162_);
lean_ctor_set(v_reuseFailAlloc_180_, 7, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_180_, 8, v_snapshotTasks_163_);
v___x_177_ = v_reuseFailAlloc_180_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_st_ref_set(v___y_149_, v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v_trees_153_);
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_185_);
lean_dec(v___y_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(lean_object* v___x_188_, lean_object* v_ctx_x3f_189_, size_t v_sz_190_, size_t v_i_191_, lean_object* v_bs_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_usize_dec_lt(v_i_191_, v_sz_190_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec_ref(v_ctx_x3f_189_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v_bs_192_);
return v___x_201_;
}
else
{
lean_object* v_assignment_202_; lean_object* v___x_203_; 
v_assignment_202_ = lean_ctor_get(v___x_188_, 0);
lean_inc_ref(v_ctx_x3f_189_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
lean_inc(v___y_196_);
lean_inc_ref(v___y_195_);
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
v___x_203_ = lean_apply_7(v_ctx_x3f_189_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, lean_box(0));
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v_v_205_; lean_object* v___x_206_; lean_object* v_bs_x27_207_; lean_object* v_a_209_; lean_object* v_tree_214_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_203_, 1);
v_v_205_ = lean_array_uget(v_bs_192_, v_i_191_);
v___x_206_ = lean_unsigned_to_nat(0u);
v_bs_x27_207_ = lean_array_uset(v_bs_192_, v_i_191_, v___x_206_);
v_tree_214_ = l_Lean_Elab_InfoTree_substitute(v_v_205_, v_assignment_202_);
if (lean_obj_tag(v_a_204_) == 0)
{
v_a_209_ = v_tree_214_;
goto v___jp_208_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
v_val_215_ = lean_ctor_get(v_a_204_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v_a_204_, 1);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_val_215_);
lean_ctor_set(v___x_216_, 1, v_tree_214_);
v_a_209_ = v___x_216_;
goto v___jp_208_;
}
v___jp_208_:
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((size_t)1ULL);
v___x_211_ = lean_usize_add(v_i_191_, v___x_210_);
v___x_212_ = lean_array_uset(v_bs_x27_207_, v_i_191_, v_a_209_);
v_i_191_ = v___x_211_;
v_bs_192_ = v___x_212_;
goto _start;
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v_bs_192_);
lean_dec_ref(v_ctx_x3f_189_);
v_a_217_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_203_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_203_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12___boxed(lean_object* v___x_225_, lean_object* v_ctx_x3f_226_, lean_object* v_sz_227_, lean_object* v_i_228_, lean_object* v_bs_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
size_t v_sz_boxed_237_; size_t v_i_boxed_238_; lean_object* v_res_239_; 
v_sz_boxed_237_ = lean_unbox_usize(v_sz_227_);
lean_dec(v_sz_227_);
v_i_boxed_238_ = lean_unbox_usize(v_i_228_);
lean_dec(v_i_228_);
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_225_, v_ctx_x3f_226_, v_sz_boxed_237_, v_i_boxed_238_, v_bs_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec_ref(v___x_225_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(lean_object* v___x_240_, lean_object* v_ctx_x3f_241_, lean_object* v_x_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v_cs_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_276_; 
v_cs_250_ = lean_ctor_get(v_x_242_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_242_);
if (v_isSharedCheck_276_ == 0)
{
v___x_252_ = v_x_242_;
v_isShared_253_ = v_isSharedCheck_276_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_cs_250_);
lean_dec(v_x_242_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_276_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
size_t v_sz_254_; size_t v___x_255_; lean_object* v___x_256_; 
v_sz_254_ = lean_array_size(v_cs_250_);
v___x_255_ = ((size_t)0ULL);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_240_, v_ctx_x3f_241_, v_sz_254_, v___x_255_, v_cs_250_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_267_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_267_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v_a_257_);
v___x_262_ = v___x_252_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_del_object(v___x_252_);
v_a_268_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_256_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_256_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
else
{
lean_object* v_vs_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_303_; 
v_vs_277_ = lean_ctor_get(v_x_242_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_242_);
if (v_isSharedCheck_303_ == 0)
{
v___x_279_ = v_x_242_;
v_isShared_280_ = v_isSharedCheck_303_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_vs_277_);
lean_dec(v_x_242_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_303_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
size_t v_sz_281_; size_t v___x_282_; lean_object* v___x_283_; 
v_sz_281_ = lean_array_size(v_vs_277_);
v___x_282_ = ((size_t)0ULL);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_240_, v_ctx_x3f_241_, v_sz_281_, v___x_282_, v_vs_277_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_294_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_294_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v_a_284_);
v___x_289_ = v___x_279_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_293_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_291_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_289_);
v___x_291_ = v___x_286_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_del_object(v___x_279_);
v_a_295_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_283_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_283_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(lean_object* v___x_304_, lean_object* v_ctx_x3f_305_, size_t v_sz_306_, size_t v_i_307_, lean_object* v_bs_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_lt(v_i_307_, v_sz_306_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v_ctx_x3f_305_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_bs_308_);
return v___x_317_;
}
else
{
lean_object* v_v_318_; lean_object* v___x_319_; 
v_v_318_ = lean_array_uget_borrowed(v_bs_308_, v_i_307_);
lean_inc(v_v_318_);
lean_inc_ref(v_ctx_x3f_305_);
v___x_319_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_304_, v_ctx_x3f_305_, v_v_318_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v_bs_x27_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v___x_321_ = lean_unsigned_to_nat(0u);
v_bs_x27_322_ = lean_array_uset(v_bs_308_, v_i_307_, v___x_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_307_, v___x_323_);
v___x_325_ = lean_array_uset(v_bs_x27_322_, v_i_307_, v_a_320_);
v_i_307_ = v___x_324_;
v_bs_308_ = v___x_325_;
goto _start;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_bs_308_);
lean_dec_ref(v_ctx_x3f_305_);
v_a_327_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_319_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_319_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v___x_335_, lean_object* v_ctx_x3f_336_, lean_object* v_sz_337_, lean_object* v_i_338_, lean_object* v_bs_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v_i_boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_337_);
lean_dec(v_sz_337_);
v_i_boxed_348_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_335_, v_ctx_x3f_336_, v_sz_boxed_347_, v_i_boxed_348_, v_bs_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec_ref(v___x_335_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11___boxed(lean_object* v___x_350_, lean_object* v_ctx_x3f_351_, lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_350_, v_ctx_x3f_351_, v_x_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v___x_350_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(lean_object* v___x_361_, lean_object* v_ctx_x3f_362_, lean_object* v_t_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_root_371_; lean_object* v_tail_372_; lean_object* v_size_373_; size_t v_shift_374_; lean_object* v_tailOff_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_411_; 
v_root_371_ = lean_ctor_get(v_t_363_, 0);
v_tail_372_ = lean_ctor_get(v_t_363_, 1);
v_size_373_ = lean_ctor_get(v_t_363_, 2);
v_shift_374_ = lean_ctor_get_usize(v_t_363_, 4);
v_tailOff_375_ = lean_ctor_get(v_t_363_, 3);
v_isSharedCheck_411_ = !lean_is_exclusive(v_t_363_);
if (v_isSharedCheck_411_ == 0)
{
v___x_377_ = v_t_363_;
v_isShared_378_ = v_isSharedCheck_411_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_tailOff_375_);
lean_inc(v_size_373_);
lean_inc(v_tail_372_);
lean_inc(v_root_371_);
lean_dec(v_t_363_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_411_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; 
lean_inc_ref(v_ctx_x3f_362_);
v___x_379_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_361_, v_ctx_x3f_362_, v_root_371_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; size_t v_sz_381_; size_t v___x_382_; lean_object* v___x_383_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v_sz_381_ = lean_array_size(v_tail_372_);
v___x_382_ = ((size_t)0ULL);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_361_, v_ctx_x3f_362_, v_sz_381_, v___x_382_, v_tail_372_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_394_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_394_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_a_384_);
lean_ctor_set(v___x_377_, 0, v_a_380_);
v___x_389_ = v___x_377_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_a_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_size_373_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_tailOff_375_);
lean_ctor_set_usize(v_reuseFailAlloc_393_, 4, v_shift_374_);
v___x_389_ = v_reuseFailAlloc_393_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_a_380_);
lean_del_object(v___x_377_);
lean_dec(v_tailOff_375_);
lean_dec(v_size_373_);
v_a_395_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_383_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_383_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_del_object(v___x_377_);
lean_dec(v_tailOff_375_);
lean_dec(v_size_373_);
lean_dec_ref(v_tail_372_);
lean_dec_ref(v_ctx_x3f_362_);
v_a_403_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_379_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_379_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6___boxed(lean_object* v___x_412_, lean_object* v_ctx_x3f_413_, lean_object* v_t_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v___x_412_, v_ctx_x3f_413_, v_t_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v___x_412_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(lean_object* v___y_423_, lean_object* v_ctx_x3f_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v_a_430_, lean_object* v_a_x3f_431_){
_start:
{
lean_object* v___x_433_; lean_object* v_infoState_434_; lean_object* v_trees_435_; lean_object* v___x_436_; 
v___x_433_ = lean_st_ref_get(v___y_423_);
v_infoState_434_ = lean_ctor_get(v___x_433_, 7);
lean_inc_ref(v_infoState_434_);
lean_dec(v___x_433_);
v_trees_435_ = lean_ctor_get(v_infoState_434_, 2);
lean_inc_ref(v_trees_435_);
v___x_436_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v_infoState_434_, v_ctx_x3f_424_, v_trees_435_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_423_);
lean_dec_ref(v_infoState_434_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_475_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_475_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_475_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_475_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_infoState_442_; lean_object* v_env_443_; lean_object* v_nextMacroScope_444_; lean_object* v_ngen_445_; lean_object* v_auxDeclNGen_446_; lean_object* v_traceState_447_; lean_object* v_cache_448_; lean_object* v_messages_449_; lean_object* v_snapshotTasks_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_474_; 
v___x_441_ = lean_st_ref_take(v___y_423_);
v_infoState_442_ = lean_ctor_get(v___x_441_, 7);
v_env_443_ = lean_ctor_get(v___x_441_, 0);
v_nextMacroScope_444_ = lean_ctor_get(v___x_441_, 1);
v_ngen_445_ = lean_ctor_get(v___x_441_, 2);
v_auxDeclNGen_446_ = lean_ctor_get(v___x_441_, 3);
v_traceState_447_ = lean_ctor_get(v___x_441_, 4);
v_cache_448_ = lean_ctor_get(v___x_441_, 5);
v_messages_449_ = lean_ctor_get(v___x_441_, 6);
v_snapshotTasks_450_ = lean_ctor_get(v___x_441_, 8);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_474_ == 0)
{
v___x_452_ = v___x_441_;
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snapshotTasks_450_);
lean_inc(v_infoState_442_);
lean_inc(v_messages_449_);
lean_inc(v_cache_448_);
lean_inc(v_traceState_447_);
lean_inc(v_auxDeclNGen_446_);
lean_inc(v_ngen_445_);
lean_inc(v_nextMacroScope_444_);
lean_inc(v_env_443_);
lean_dec(v___x_441_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v_enabled_454_; lean_object* v_assignment_455_; lean_object* v_lazyAssignment_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_472_; 
v_enabled_454_ = lean_ctor_get_uint8(v_infoState_442_, sizeof(void*)*3);
v_assignment_455_ = lean_ctor_get(v_infoState_442_, 0);
v_lazyAssignment_456_ = lean_ctor_get(v_infoState_442_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_infoState_442_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_infoState_442_, 2);
lean_dec(v_unused_473_);
v___x_458_ = v_infoState_442_;
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_lazyAssignment_456_);
lean_inc(v_assignment_455_);
lean_dec(v_infoState_442_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_PersistentArray_append___redArg(v_a_430_, v_a_437_);
lean_dec(v_a_437_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 2, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_assignment_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_lazyAssignment_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v___x_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*3, v_enabled_454_);
v___x_462_ = v_reuseFailAlloc_471_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 7, v___x_462_);
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_env_443_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_nextMacroScope_444_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_ngen_445_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_auxDeclNGen_446_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_traceState_447_);
lean_ctor_set(v_reuseFailAlloc_470_, 5, v_cache_448_);
lean_ctor_set(v_reuseFailAlloc_470_, 6, v_messages_449_);
lean_ctor_set(v_reuseFailAlloc_470_, 7, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_470_, 8, v_snapshotTasks_450_);
v___x_464_ = v_reuseFailAlloc_470_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = lean_st_ref_set(v___y_423_, v___x_464_);
v___x_466_ = lean_box(0);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_466_);
v___x_468_ = v___x_439_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v_a_430_);
v_a_476_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_436_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_436_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_484_, lean_object* v_ctx_x3f_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v_a_491_, lean_object* v_a_x3f_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_484_, v_ctx_x3f_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v_a_491_, v_a_x3f_492_);
lean_dec(v_a_x3f_492_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_484_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(lean_object* v_x_495_, lean_object* v_ctx_x3f_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v_infoState_505_; uint8_t v_enabled_506_; uint8_t v___x_507_; 
v___x_504_ = lean_st_ref_get(v___y_502_);
v_infoState_505_ = lean_ctor_get(v___x_504_, 7);
lean_inc_ref(v_infoState_505_);
lean_dec(v___x_504_);
v_enabled_506_ = lean_ctor_get_uint8(v_infoState_505_, sizeof(void*)*3);
lean_dec_ref(v_infoState_505_);
v___x_507_ = lean_bool_not(v_enabled_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v_r_510_; 
v___x_508_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_502_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v_r_510_ = lean_apply_7(v_x_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_535_; 
v_a_511_ = lean_ctor_get(v_r_510_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_535_ == 0)
{
v___x_513_ = v_r_510_;
v_isShared_514_ = v_isSharedCheck_535_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v_r_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_535_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
lean_inc(v_a_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 1);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_534_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; 
v___x_517_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_502_, v_ctx_x3f_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v_a_509_, v___x_516_);
lean_dec_ref(v___x_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_517_, 0);
lean_dec(v_unused_525_);
v___x_519_ = v___x_517_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_dec(v___x_517_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_a_511_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_511_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_511_);
v_a_526_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_517_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_517_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_a_536_ = lean_ctor_get(v_r_510_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v_r_510_, 1);
v___x_537_ = lean_box(0);
v___x_538_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_502_, v_ctx_x3f_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v_a_509_, v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v___x_538_, 0);
lean_dec(v_unused_546_);
v___x_540_ = v___x_538_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_dec(v___x_538_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 1);
lean_ctor_set(v___x_540_, 0, v_a_536_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_536_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_536_);
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
else
{
lean_object* v___x_555_; 
lean_dec_ref(v_ctx_x3f_496_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_555_ = lean_apply_7(v_x_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___boxed(lean_object* v_x_556_, lean_object* v_ctx_x3f_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_556_, v_ctx_x3f_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v___x_572_; lean_object* v_mctx_573_; lean_object* v_options_574_; lean_object* v_currNamespace_575_; lean_object* v_openDecls_576_; lean_object* v___x_577_; lean_object* v_ngen_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_570_ = lean_st_ref_get(v___y_568_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = lean_st_ref_get(v___y_566_);
v_mctx_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_572_);
v_options_574_ = lean_ctor_get(v___y_567_, 2);
v_currNamespace_575_ = lean_ctor_get(v___y_567_, 6);
v_openDecls_576_ = lean_ctor_get(v___y_567_, 7);
v___x_577_ = lean_st_ref_get(v___y_568_);
v_ngen_578_ = lean_ctor_get(v___x_577_, 2);
lean_inc_ref(v_ngen_578_);
lean_dec(v___x_577_);
v___x_579_ = lean_box(0);
v___x_580_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_576_);
lean_inc(v_currNamespace_575_);
lean_inc_ref(v_options_574_);
v___x_581_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_581_, 0, v_env_571_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v_mctx_573_);
lean_ctor_set(v___x_581_, 4, v_options_574_);
lean_ctor_set(v___x_581_, 5, v_currNamespace_575_);
lean_ctor_set(v___x_581_, 6, v_openDecls_576_);
lean_ctor_set(v___x_581_, 7, v_ngen_578_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_620_; 
v___x_595_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_591_, v___y_592_, v___y_593_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_620_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_620_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_620_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_fileMap_600_; lean_object* v_env_601_; lean_object* v_mctx_602_; lean_object* v_options_603_; lean_object* v_currNamespace_604_; lean_object* v_openDecls_605_; lean_object* v_ngen_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_617_; 
v_fileMap_600_ = lean_ctor_get(v___y_592_, 1);
v_env_601_ = lean_ctor_get(v_a_596_, 0);
v_mctx_602_ = lean_ctor_get(v_a_596_, 3);
v_options_603_ = lean_ctor_get(v_a_596_, 4);
v_currNamespace_604_ = lean_ctor_get(v_a_596_, 5);
v_openDecls_605_ = lean_ctor_get(v_a_596_, 6);
v_ngen_606_ = lean_ctor_get(v_a_596_, 7);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; 
v_unused_618_ = lean_ctor_get(v_a_596_, 2);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_a_596_, 1);
lean_dec(v_unused_619_);
v___x_608_ = v_a_596_;
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_ngen_606_);
lean_inc(v_openDecls_605_);
lean_inc(v_currNamespace_604_);
lean_inc(v_options_603_);
lean_inc(v_mctx_602_);
lean_inc(v_env_601_);
lean_dec(v_a_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_box(0);
lean_inc_ref(v_fileMap_600_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 2, v_fileMap_600_);
lean_ctor_set(v___x_608_, 1, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_env_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_fileMap_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_mctx_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_options_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_currNamespace_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_openDecls_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_ngen_606_);
v___x_612_ = v_reuseFailAlloc_616_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_612_);
v___x_614_ = v___x_598_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2___boxed(lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v___x_636_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_a_637_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_642_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed(lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___f_664_; lean_object* v___x_665_; 
v___f_664_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0));
v___x_665_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_656_, v___f_664_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(lean_object* v_snd_675_, lean_object* v___x_676_, lean_object* v_____r_677_, lean_object* v_lctx_678_, lean_object* v_hs_679_, lean_object* v_info_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_688_ = l_Lean_NameSet_insert(v_snd_675_, v___x_676_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_info_680_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_hs_679_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_lctx_678_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(lean_object* v_snd_694_, lean_object* v___x_695_, lean_object* v_____r_696_, lean_object* v_lctx_697_, lean_object* v_hs_698_, lean_object* v_info_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_694_, v___x_695_, v_____r_696_, v_lctx_697_, v_hs_698_, v_info_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(lean_object* v_fst_708_, lean_object* v___f_709_, lean_object* v_snd_710_, lean_object* v_____r_711_, lean_object* v_lctx_712_, lean_object* v_info_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_721_ = lean_array_pop(v_fst_708_);
v___x_722_ = lean_array_get_size(v___x_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v_snd_710_);
v___x_725_ = lean_box(0);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
v___x_726_ = lean_apply_11(v___f_709_, v___x_725_, v_lctx_712_, v___x_721_, v_info_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v___f_709_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_info_713_);
lean_ctor_set(v___x_727_, 1, v_snd_710_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_721_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_lctx_712_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(lean_object* v_fst_732_, lean_object* v___f_733_, lean_object* v_snd_734_, lean_object* v_____r_735_, lean_object* v_lctx_736_, lean_object* v_info_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_732_, v___f_733_, v_snd_734_, v_____r_735_, v_lctx_736_, v_info_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(lean_object* v_upperBound_754_, lean_object* v___x_755_, lean_object* v_val_756_, lean_object* v_a_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_a_767_; lean_object* v___y_772_; uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_lt(v_a_757_, v_upperBound_754_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v_a_757_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_b_758_);
return v___x_792_;
}
else
{
lean_object* v_snd_793_; lean_object* v_snd_794_; lean_object* v_fst_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_867_; 
v_snd_793_ = lean_ctor_get(v_b_758_, 1);
lean_inc(v_snd_793_);
v_snd_794_ = lean_ctor_get(v_snd_793_, 1);
lean_inc(v_snd_794_);
v_fst_795_ = lean_ctor_get(v_b_758_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_b_758_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_b_758_, 1);
lean_dec(v_unused_868_);
v___x_797_ = v_b_758_;
v_isShared_798_ = v_isSharedCheck_867_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_fst_795_);
lean_dec(v_b_758_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_867_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_fst_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_865_; 
v_fst_799_ = lean_ctor_get(v_snd_793_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_snd_793_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_snd_793_, 1);
lean_dec(v_unused_866_);
v___x_801_ = v_snd_793_;
v_isShared_802_ = v_isSharedCheck_865_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_fst_799_);
lean_dec(v_snd_793_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_865_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_864_; 
v_fst_803_ = lean_ctor_get(v_snd_794_, 0);
v_snd_804_ = lean_ctor_get(v_snd_794_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_864_ == 0)
{
v___x_806_ = v_snd_794_;
v_isShared_807_ = v_isSharedCheck_864_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snd_804_);
lean_inc(v_fst_803_);
lean_dec(v_snd_794_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_864_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_808_ = lean_nat_sub(v___x_755_, v_a_757_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_sub(v___x_808_, v___x_809_);
lean_dec(v___x_808_);
v___x_811_ = l_Lean_LocalContext_getAt_x3f(v_fst_795_, v___x_810_);
lean_dec(v___x_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_813_; 
if (v_isShared_807_ == 0)
{
v___x_813_ = v___x_806_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_803_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_snd_804_);
v___x_813_ = v_reuseFailAlloc_820_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_813_);
v___x_815_ = v___x_801_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_799_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_813_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_815_);
v___x_817_ = v___x_797_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fst_795_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v_a_767_ = v___x_817_;
goto v___jp_766_;
}
}
}
}
else
{
lean_object* v_val_821_; uint8_t v___x_822_; 
v_val_821_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_811_, 1);
v___x_822_ = l_Lean_LocalDecl_isImplementationDetail(v_val_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_849_; uint8_t v___x_850_; uint8_t v___x_851_; 
lean_del_object(v___x_801_);
lean_del_object(v___x_797_);
v___x_823_ = l_Lean_LocalDecl_userName(v_val_821_);
lean_inc_n(v___x_823_, 2);
lean_inc(v_snd_804_);
v___f_824_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_824_, 0, v_snd_804_);
lean_closure_set(v___f_824_, 1, v___x_823_);
v___x_849_ = l_Lean_extractMacroScopes(v___x_823_);
v___x_850_ = l_Lean_MacroScopesView_equalScope(v___x_849_, v_val_756_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_bool_not(v___x_850_);
if (v___x_851_ == 0)
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_NameSet_contains(v_snd_804_, v___x_823_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref(v___f_824_);
lean_dec(v_val_821_);
lean_del_object(v___x_806_);
v___x_853_ = lean_box(0);
v___x_854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_804_, v___x_823_, v___x_853_, v_fst_795_, v_fst_799_, v_fst_803_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_772_ = v___x_854_;
goto v___jp_771_;
}
else
{
lean_dec(v___x_823_);
goto v___jp_825_;
}
}
else
{
lean_dec(v___x_823_);
goto v___jp_825_;
}
v___jp_825_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
v___x_827_ = lean_box(0);
v___x_828_ = lean_array_get_size(v_fst_799_);
v___x_829_ = lean_nat_sub(v___x_828_, v___x_809_);
v___x_830_ = lean_array_get_borrowed(v___x_827_, v_fst_799_, v___x_829_);
lean_dec(v___x_829_);
lean_inc(v___x_830_);
v___x_831_ = l_Lean_Syntax_isOfKind(v___x_830_, v___x_826_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v_val_821_);
lean_del_object(v___x_806_);
v___x_832_ = lean_box(0);
v___x_833_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_799_, v___f_824_, v_snd_804_, v___x_832_, v_fst_795_, v_fst_803_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_772_ = v___x_833_;
goto v___jp_771_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Lean_Syntax_getArg(v___x_830_, v___x_834_);
v___x_836_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_835_);
v___x_837_ = l_Lean_Syntax_isOfKind(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v___x_835_);
lean_dec(v_val_821_);
lean_del_object(v___x_806_);
v___x_838_ = lean_box(0);
v___x_839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_799_, v___f_824_, v_snd_804_, v___x_838_, v_fst_795_, v_fst_803_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_772_ = v___x_839_;
goto v___jp_771_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_840_ = l_Lean_TSyntax_getId(v___x_835_);
v___x_841_ = l_Lean_LocalDecl_fvarId(v_val_821_);
lean_dec(v_val_821_);
lean_inc(v___x_841_);
v___x_842_ = l_Lean_LocalContext_setUserName(v_fst_795_, v___x_841_, v___x_840_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_835_);
lean_ctor_set(v___x_806_, 0, v___x_841_);
v___x_844_ = v___x_806_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_835_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_array_push(v_fst_803_, v___x_844_);
v___x_846_ = lean_box(0);
v___x_847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_799_, v___f_824_, v_snd_804_, v___x_846_, v___x_842_, v___x_845_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_772_ = v___x_847_;
goto v___jp_771_;
}
}
}
}
}
else
{
lean_object* v___x_856_; 
lean_dec(v_val_821_);
if (v_isShared_807_ == 0)
{
v___x_856_ = v___x_806_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_803_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_snd_804_);
v___x_856_ = v_reuseFailAlloc_863_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_856_);
v___x_858_ = v___x_801_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_fst_799_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_858_);
v___x_860_ = v___x_797_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_795_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
v_a_767_ = v___x_860_;
goto v___jp_766_;
}
}
}
}
}
}
}
}
}
v___jp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_a_757_, v___x_768_);
lean_dec(v_a_757_);
v_a_757_ = v___x_769_;
v_b_758_ = v_a_767_;
goto _start;
}
v___jp_771_:
{
if (lean_obj_tag(v___y_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v_a_773_ = lean_ctor_get(v___y_772_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___y_772_);
if (v_isSharedCheck_782_ == 0)
{
v___x_775_ = v___y_772_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___y_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
if (lean_obj_tag(v_a_773_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; 
lean_dec(v_a_757_);
v_a_777_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v_a_773_, 1);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_a_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v_a_781_; 
lean_del_object(v___x_775_);
v_a_781_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v_a_773_, 1);
v_a_767_ = v_a_781_;
goto v___jp_766_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_757_);
v_a_783_ = lean_ctor_get(v___y_772_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___y_772_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___y_772_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___y_772_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___boxed(lean_object* v_upperBound_869_, lean_object* v___x_870_, lean_object* v_val_871_, lean_object* v_a_872_, lean_object* v_b_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_869_, v___x_870_, v_val_871_, v_a_872_, v_b_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v_val_871_);
lean_dec(v___x_870_);
lean_dec(v_upperBound_869_);
return v_res_881_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(uint8_t v___y_890_, uint8_t v_suppressElabErrors_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 1)
{
lean_object* v_pre_893_; 
v_pre_893_ = lean_ctor_get(v_x_892_, 0);
switch(lean_obj_tag(v_pre_893_))
{
case 1:
{
lean_object* v_pre_894_; 
v_pre_894_ = lean_ctor_get(v_pre_893_, 0);
switch(lean_obj_tag(v_pre_894_))
{
case 0:
{
lean_object* v_str_895_; lean_object* v_str_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_str_895_ = lean_ctor_get(v_x_892_, 1);
v_str_896_ = lean_ctor_get(v_pre_893_, 1);
v___x_897_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0));
v___x_898_ = lean_string_dec_eq(v_str_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1));
v___x_900_ = lean_string_dec_eq(v_str_896_, v___x_899_);
if (v___x_900_ == 0)
{
return v___y_890_;
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2));
v___x_902_ = lean_string_dec_eq(v_str_895_, v___x_901_);
if (v___x_902_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3));
v___x_904_ = lean_string_dec_eq(v_str_895_, v___x_903_);
if (v___x_904_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
}
case 1:
{
lean_object* v_pre_905_; 
v_pre_905_ = lean_ctor_get(v_pre_894_, 0);
if (lean_obj_tag(v_pre_905_) == 0)
{
lean_object* v_str_906_; lean_object* v_str_907_; lean_object* v_str_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_str_906_ = lean_ctor_get(v_x_892_, 1);
v_str_907_ = lean_ctor_get(v_pre_893_, 1);
v_str_908_ = lean_ctor_get(v_pre_894_, 1);
v___x_909_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4));
v___x_910_ = lean_string_dec_eq(v_str_908_, v___x_909_);
if (v___x_910_ == 0)
{
return v___y_890_;
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5));
v___x_912_ = lean_string_dec_eq(v_str_907_, v___x_911_);
if (v___x_912_ == 0)
{
return v___y_890_;
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6));
v___x_914_ = lean_string_dec_eq(v_str_906_, v___x_913_);
if (v___x_914_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
}
}
else
{
return v___y_890_;
}
}
default: 
{
return v___y_890_;
}
}
}
case 0:
{
lean_object* v_str_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_str_915_ = lean_ctor_get(v_x_892_, 1);
v___x_916_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7));
v___x_917_ = lean_string_dec_eq(v_str_915_, v___x_916_);
if (v___x_917_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
default: 
{
return v___y_890_;
}
}
}
else
{
return v___y_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed(lean_object* v___y_918_, lean_object* v_suppressElabErrors_919_, lean_object* v_x_920_){
_start:
{
uint8_t v___y_23637__boxed_921_; uint8_t v_suppressElabErrors_boxed_922_; uint8_t v_res_923_; lean_object* v_r_924_; 
v___y_23637__boxed_921_ = lean_unbox(v___y_918_);
v_suppressElabErrors_boxed_922_ = lean_unbox(v_suppressElabErrors_919_);
v_res_923_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v___y_23637__boxed_921_, v_suppressElabErrors_boxed_922_, v_x_920_);
lean_dec(v_x_920_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(lean_object* v_opts_925_, lean_object* v_opt_926_){
_start:
{
lean_object* v_name_927_; lean_object* v_defValue_928_; lean_object* v_map_929_; lean_object* v___x_930_; 
v_name_927_ = lean_ctor_get(v_opt_926_, 0);
v_defValue_928_ = lean_ctor_get(v_opt_926_, 1);
v_map_929_ = lean_ctor_get(v_opts_925_, 0);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_929_, v_name_927_);
if (lean_obj_tag(v___x_930_) == 0)
{
uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_defValue_928_);
return v___x_931_;
}
else
{
lean_object* v_val_932_; 
v_val_932_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v___x_930_, 1);
if (lean_obj_tag(v_val_932_) == 1)
{
uint8_t v_v_933_; 
v_v_933_ = lean_ctor_get_uint8(v_val_932_, 0);
lean_dec_ref_known(v_val_932_, 0);
return v_v_933_;
}
else
{
uint8_t v___x_934_; 
lean_dec(v_val_932_);
v___x_934_ = lean_unbox(v_defValue_928_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(lean_object* v_opts_935_, lean_object* v_opt_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_935_, v_opt_936_);
lean_dec_ref(v_opt_936_);
lean_dec_ref(v_opts_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(lean_object* v_msgData_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v_env_946_; lean_object* v___x_947_; lean_object* v_mctx_948_; lean_object* v_lctx_949_; lean_object* v_options_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_945_ = lean_st_ref_get(v___y_943_);
v_env_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_env_946_);
lean_dec(v___x_945_);
v___x_947_ = lean_st_ref_get(v___y_941_);
v_mctx_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc_ref(v_mctx_948_);
lean_dec(v___x_947_);
v_lctx_949_ = lean_ctor_get(v___y_940_, 2);
v_options_950_ = lean_ctor_get(v___y_942_, 2);
lean_inc_ref(v_options_950_);
lean_inc_ref(v_lctx_949_);
v___x_951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_951_, 0, v_env_946_);
lean_ctor_set(v___x_951_, 1, v_mctx_948_);
lean_ctor_set(v___x_951_, 2, v_lctx_949_);
lean_ctor_set(v___x_951_, 3, v_options_950_);
v___x_952_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v_msgData_939_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(lean_object* v_msgData_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(lean_object* v_ref_962_, lean_object* v_msgData_963_, uint8_t v_severity_964_, uint8_t v_isSilent_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_1008_; uint8_t v___y_1009_; uint8_t v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; uint8_t v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1044_; uint8_t v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; uint8_t v___y_1050_; uint8_t v___x_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; uint8_t v___y_1061_; uint8_t v___y_1062_; uint8_t v___y_1063_; uint8_t v___y_1065_; uint8_t v___x_1080_; 
v___x_1055_ = 2;
v___x_1080_ = l_Lean_instBEqMessageSeverity_beq(v_severity_964_, v___x_1055_);
if (v___x_1080_ == 0)
{
v___y_1065_ = v___x_1080_;
goto v___jp_1064_;
}
else
{
uint8_t v___x_1081_; 
lean_inc_ref(v_msgData_963_);
v___x_1081_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_963_);
v___y_1065_ = v___x_1081_;
goto v___jp_1064_;
}
v___jp_971_:
{
lean_object* v___x_981_; lean_object* v_currNamespace_982_; lean_object* v_openDecls_983_; lean_object* v_env_984_; lean_object* v_nextMacroScope_985_; lean_object* v_ngen_986_; lean_object* v_auxDeclNGen_987_; lean_object* v_traceState_988_; lean_object* v_cache_989_; lean_object* v_messages_990_; lean_object* v_infoState_991_; lean_object* v_snapshotTasks_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1006_; 
v___x_981_ = lean_st_ref_take(v___y_980_);
v_currNamespace_982_ = lean_ctor_get(v___y_979_, 6);
v_openDecls_983_ = lean_ctor_get(v___y_979_, 7);
v_env_984_ = lean_ctor_get(v___x_981_, 0);
v_nextMacroScope_985_ = lean_ctor_get(v___x_981_, 1);
v_ngen_986_ = lean_ctor_get(v___x_981_, 2);
v_auxDeclNGen_987_ = lean_ctor_get(v___x_981_, 3);
v_traceState_988_ = lean_ctor_get(v___x_981_, 4);
v_cache_989_ = lean_ctor_get(v___x_981_, 5);
v_messages_990_ = lean_ctor_get(v___x_981_, 6);
v_infoState_991_ = lean_ctor_get(v___x_981_, 7);
v_snapshotTasks_992_ = lean_ctor_get(v___x_981_, 8);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_994_ = v___x_981_;
v_isShared_995_ = v_isSharedCheck_1006_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snapshotTasks_992_);
lean_inc(v_infoState_991_);
lean_inc(v_messages_990_);
lean_inc(v_cache_989_);
lean_inc(v_traceState_988_);
lean_inc(v_auxDeclNGen_987_);
lean_inc(v_ngen_986_);
lean_inc(v_nextMacroScope_985_);
lean_inc(v_env_984_);
lean_dec(v___x_981_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1006_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_inc(v_openDecls_983_);
lean_inc(v_currNamespace_982_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v_currNamespace_982_);
lean_ctor_set(v___x_996_, 1, v_openDecls_983_);
v___x_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___y_978_);
lean_inc_ref(v___y_972_);
lean_inc_ref(v___y_977_);
v___x_998_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_998_, 0, v___y_977_);
lean_ctor_set(v___x_998_, 1, v___y_974_);
lean_ctor_set(v___x_998_, 2, v___y_975_);
lean_ctor_set(v___x_998_, 3, v___y_972_);
lean_ctor_set(v___x_998_, 4, v___x_997_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*5, v___y_973_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*5 + 1, v___y_976_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*5 + 2, v_isSilent_965_);
v___x_999_ = l_Lean_MessageLog_add(v___x_998_, v_messages_990_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 6, v___x_999_);
v___x_1001_ = v___x_994_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_env_984_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_nextMacroScope_985_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_ngen_986_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_auxDeclNGen_987_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_traceState_988_);
lean_ctor_set(v_reuseFailAlloc_1005_, 5, v_cache_989_);
lean_ctor_set(v_reuseFailAlloc_1005_, 6, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1005_, 7, v_infoState_991_);
lean_ctor_set(v_reuseFailAlloc_1005_, 8, v_snapshotTasks_992_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_st_ref_set(v___y_980_, v___x_1001_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
}
v___jp_1007_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1031_; 
v___x_1016_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_963_);
v___x_1017_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v___x_1016_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_inc_ref_n(v___y_1012_, 2);
v___x_1022_ = l_Lean_FileMap_toPosition(v___y_1012_, v___y_1011_);
lean_dec(v___y_1011_);
v___x_1023_ = l_Lean_FileMap_toPosition(v___y_1012_, v___y_1015_);
lean_dec(v___y_1015_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0));
if (v___y_1014_ == 0)
{
lean_del_object(v___x_1020_);
lean_dec_ref(v___y_1008_);
v___y_972_ = v___x_1025_;
v___y_973_ = v___y_1009_;
v___y_974_ = v___x_1022_;
v___y_975_ = v___x_1024_;
v___y_976_ = v___y_1010_;
v___y_977_ = v___y_1013_;
v___y_978_ = v_a_1018_;
v___y_979_ = v___y_968_;
v___y_980_ = v___y_969_;
goto v___jp_971_;
}
else
{
uint8_t v___x_1026_; 
lean_inc(v_a_1018_);
v___x_1026_ = l_Lean_MessageData_hasTag(v___y_1008_, v_a_1018_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_dec_ref_known(v___x_1024_, 1);
lean_dec_ref(v___x_1022_);
lean_dec(v_a_1018_);
v___x_1027_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1027_);
v___x_1029_ = v___x_1020_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
lean_del_object(v___x_1020_);
v___y_972_ = v___x_1025_;
v___y_973_ = v___y_1009_;
v___y_974_ = v___x_1022_;
v___y_975_ = v___x_1024_;
v___y_976_ = v___y_1010_;
v___y_977_ = v___y_1013_;
v___y_978_ = v_a_1018_;
v___y_979_ = v___y_968_;
v___y_980_ = v___y_969_;
goto v___jp_971_;
}
}
}
}
v___jp_1032_:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Syntax_getTailPos_x3f(v___y_1038_, v___y_1034_);
lean_dec(v___y_1038_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_inc(v___y_1040_);
v___y_1008_ = v___y_1033_;
v___y_1009_ = v___y_1034_;
v___y_1010_ = v___y_1036_;
v___y_1011_ = v___y_1040_;
v___y_1012_ = v___y_1035_;
v___y_1013_ = v___y_1037_;
v___y_1014_ = v___y_1039_;
v___y_1015_ = v___y_1040_;
goto v___jp_1007_;
}
else
{
lean_object* v_val_1042_; 
v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___y_1008_ = v___y_1033_;
v___y_1009_ = v___y_1034_;
v___y_1010_ = v___y_1036_;
v___y_1011_ = v___y_1040_;
v___y_1012_ = v___y_1035_;
v___y_1013_ = v___y_1037_;
v___y_1014_ = v___y_1039_;
v___y_1015_ = v_val_1042_;
goto v___jp_1007_;
}
}
v___jp_1043_:
{
lean_object* v_ref_1051_; lean_object* v___x_1052_; 
v_ref_1051_ = l_Lean_replaceRef(v_ref_962_, v___y_1046_);
v___x_1052_ = l_Lean_Syntax_getPos_x3f(v_ref_1051_, v___y_1045_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___y_1033_ = v___y_1044_;
v___y_1034_ = v___y_1045_;
v___y_1035_ = v___y_1047_;
v___y_1036_ = v___y_1050_;
v___y_1037_ = v___y_1048_;
v___y_1038_ = v_ref_1051_;
v___y_1039_ = v___y_1049_;
v___y_1040_ = v___x_1053_;
goto v___jp_1032_;
}
else
{
lean_object* v_val_1054_; 
v_val_1054_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v___x_1052_, 1);
v___y_1033_ = v___y_1044_;
v___y_1034_ = v___y_1045_;
v___y_1035_ = v___y_1047_;
v___y_1036_ = v___y_1050_;
v___y_1037_ = v___y_1048_;
v___y_1038_ = v_ref_1051_;
v___y_1039_ = v___y_1049_;
v___y_1040_ = v_val_1054_;
goto v___jp_1032_;
}
}
v___jp_1056_:
{
if (v___y_1063_ == 0)
{
v___y_1044_ = v___y_1057_;
v___y_1045_ = v___y_1062_;
v___y_1046_ = v___y_1058_;
v___y_1047_ = v___y_1059_;
v___y_1048_ = v___y_1060_;
v___y_1049_ = v___y_1061_;
v___y_1050_ = v_severity_964_;
goto v___jp_1043_;
}
else
{
v___y_1044_ = v___y_1057_;
v___y_1045_ = v___y_1062_;
v___y_1046_ = v___y_1058_;
v___y_1047_ = v___y_1059_;
v___y_1048_ = v___y_1060_;
v___y_1049_ = v___y_1061_;
v___y_1050_ = v___x_1055_;
goto v___jp_1043_;
}
}
v___jp_1064_:
{
if (v___y_1065_ == 0)
{
lean_object* v_fileName_1066_; lean_object* v_fileMap_1067_; lean_object* v_options_1068_; lean_object* v_ref_1069_; uint8_t v_suppressElabErrors_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___f_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; 
v_fileName_1066_ = lean_ctor_get(v___y_968_, 0);
v_fileMap_1067_ = lean_ctor_get(v___y_968_, 1);
v_options_1068_ = lean_ctor_get(v___y_968_, 2);
v_ref_1069_ = lean_ctor_get(v___y_968_, 5);
v_suppressElabErrors_1070_ = lean_ctor_get_uint8(v___y_968_, sizeof(void*)*14 + 1);
v___x_1071_ = lean_box(v___y_1065_);
v___x_1072_ = lean_box(v_suppressElabErrors_1070_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1073_, 0, v___x_1071_);
lean_closure_set(v___f_1073_, 1, v___x_1072_);
v___x_1074_ = 1;
v___x_1075_ = l_Lean_instBEqMessageSeverity_beq(v_severity_964_, v___x_1074_);
if (v___x_1075_ == 0)
{
v___y_1057_ = v___f_1073_;
v___y_1058_ = v_ref_1069_;
v___y_1059_ = v_fileMap_1067_;
v___y_1060_ = v_fileName_1066_;
v___y_1061_ = v_suppressElabErrors_1070_;
v___y_1062_ = v___y_1065_;
v___y_1063_ = v___x_1075_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = l_Lean_warningAsError;
v___x_1077_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_options_1068_, v___x_1076_);
v___y_1057_ = v___f_1073_;
v___y_1058_ = v_ref_1069_;
v___y_1059_ = v_fileMap_1067_;
v___y_1060_ = v_fileName_1066_;
v___y_1061_ = v_suppressElabErrors_1070_;
v___y_1062_ = v___y_1065_;
v___y_1063_ = v___x_1077_;
goto v___jp_1056_;
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec_ref(v_msgData_963_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_ref_1082_, lean_object* v_msgData_1083_, lean_object* v_severity_1084_, lean_object* v_isSilent_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v_severity_boxed_1091_; uint8_t v_isSilent_boxed_1092_; lean_object* v_res_1093_; 
v_severity_boxed_1091_ = lean_unbox(v_severity_1084_);
v_isSilent_boxed_1092_ = lean_unbox(v_isSilent_1085_);
v_res_1093_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1082_, v_msgData_1083_, v_severity_boxed_1091_, v_isSilent_boxed_1092_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v_ref_1082_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(lean_object* v_msgData_1094_, uint8_t v_severity_1095_, uint8_t v_isSilent_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_ref_1104_; lean_object* v___x_1105_; 
v_ref_1104_ = lean_ctor_get(v___y_1101_, 5);
v___x_1105_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1104_, v_msgData_1094_, v_severity_1095_, v_isSilent_1096_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(lean_object* v_msgData_1106_, lean_object* v_severity_1107_, lean_object* v_isSilent_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v_severity_boxed_1116_; uint8_t v_isSilent_boxed_1117_; lean_object* v_res_1118_; 
v_severity_boxed_1116_ = lean_unbox(v_severity_1107_);
v_isSilent_boxed_1117_ = lean_unbox(v_isSilent_1108_);
v_res_1118_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1106_, v_severity_boxed_1116_, v_isSilent_boxed_1117_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(lean_object* v_msgData_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = 2;
v___x_1128_ = 0;
v___x_1129_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1119_, v___x_1127_, v___x_1128_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(lean_object* v_msgData_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v_msgData_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(lean_object* v_as_1142_, size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_a_1147_; uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1151_ == 0)
{
lean_inc_ref(v_b_1145_);
return v_b_1145_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_a_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_a_1154_ = lean_array_uget_borrowed(v_as_1142_, v_i_1144_);
v___x_1155_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
lean_inc(v_a_1154_);
v___x_1156_ = l_Lean_Syntax_isOfKind(v_a_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
v_a_1147_ = v___x_1153_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = l_Lean_Syntax_getArg(v_a_1154_, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_1158_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v___x_1158_);
v_a_1147_ = v___x_1153_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1161_ = l_Lean_TSyntax_getId(v___x_1158_);
lean_dec(v___x_1158_);
v___x_1162_ = l_Lean_extractMacroScopes(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1152_);
return v___x_1165_;
}
}
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1144_, v___x_1148_);
v_i_1144_ = v___x_1149_;
v_b_1145_ = v_a_1147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___boxed(lean_object* v_as_1166_, lean_object* v_sz_1167_, lean_object* v_i_1168_, lean_object* v_b_1169_){
_start:
{
size_t v_sz_boxed_1170_; size_t v_i_boxed_1171_; lean_object* v_res_1172_; 
v_sz_boxed_1170_ = lean_unbox_usize(v_sz_1167_);
lean_dec(v_sz_1167_);
v_i_boxed_1171_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_1166_, v_sz_boxed_1170_, v_i_boxed_1171_, v_b_1169_);
lean_dec_ref(v_b_1169_);
lean_dec_ref(v_as_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v_ks_1177_; lean_object* v_vs_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1202_; 
v_ks_1177_ = lean_ctor_get(v_x_1173_, 0);
v_vs_1178_ = lean_ctor_get(v_x_1173_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1180_ = v_x_1173_;
v_isShared_1181_ = v_isSharedCheck_1202_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_vs_1178_);
lean_inc(v_ks_1177_);
lean_dec(v_x_1173_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1202_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = lean_array_get_size(v_ks_1177_);
v___x_1183_ = lean_nat_dec_lt(v_x_1174_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_dec(v_x_1174_);
v___x_1184_ = lean_array_push(v_ks_1177_, v_x_1175_);
v___x_1185_ = lean_array_push(v_vs_1178_, v_x_1176_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1185_);
lean_ctor_set(v___x_1180_, 0, v___x_1184_);
v___x_1187_ = v___x_1180_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
else
{
lean_object* v_k_x27_1189_; uint8_t v___x_1190_; 
v_k_x27_1189_ = lean_array_fget_borrowed(v_ks_1177_, v_x_1174_);
v___x_1190_ = l_Lean_instBEqMVarId_beq(v_x_1175_, v_k_x27_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1192_; 
if (v_isShared_1181_ == 0)
{
v___x_1192_ = v___x_1180_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_ks_1177_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_vs_1178_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = lean_nat_add(v_x_1174_, v___x_1193_);
lean_dec(v_x_1174_);
v_x_1173_ = v___x_1192_;
v_x_1174_ = v___x_1194_;
goto _start;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lean_array_fset(v_ks_1177_, v_x_1174_, v_x_1175_);
v___x_1198_ = lean_array_fset(v_vs_1178_, v_x_1174_, v_x_1176_);
lean_dec(v_x_1174_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1198_);
lean_ctor_set(v___x_1180_, 0, v___x_1197_);
v___x_1200_ = v___x_1180_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(lean_object* v_n_1203_, lean_object* v_k_1204_, lean_object* v_v_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_n_1203_, v___x_1206_, v_k_1204_, v_v_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(lean_object* v_x_1209_, size_t v_x_1210_, size_t v_x_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 0)
{
lean_object* v_es_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v_j_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_es_1214_ = lean_ctor_get(v_x_1209_, 0);
v___x_1215_ = ((size_t)31ULL);
v___x_1216_ = lean_usize_land(v_x_1210_, v___x_1215_);
v_j_1217_ = lean_usize_to_nat(v___x_1216_);
v___x_1218_ = lean_array_get_size(v_es_1214_);
v___x_1219_ = lean_nat_dec_lt(v_j_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_dec(v_j_1217_);
lean_dec(v_x_1213_);
lean_dec(v_x_1212_);
return v_x_1209_;
}
else
{
lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1258_; 
lean_inc_ref(v_es_1214_);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1209_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_x_1209_, 0);
lean_dec(v_unused_1259_);
v___x_1221_ = v_x_1209_;
v_isShared_1222_ = v_isSharedCheck_1258_;
goto v_resetjp_1220_;
}
else
{
lean_dec(v_x_1209_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1258_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_v_1223_; lean_object* v___x_1224_; lean_object* v_xs_x27_1225_; lean_object* v___y_1227_; 
v_v_1223_ = lean_array_fget(v_es_1214_, v_j_1217_);
v___x_1224_ = lean_box(0);
v_xs_x27_1225_ = lean_array_fset(v_es_1214_, v_j_1217_, v___x_1224_);
switch(lean_obj_tag(v_v_1223_))
{
case 0:
{
lean_object* v_key_1232_; lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1243_; 
v_key_1232_ = lean_ctor_get(v_v_1223_, 0);
v_val_1233_ = lean_ctor_get(v_v_1223_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_v_1223_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1235_ = v_v_1223_;
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_inc(v_key_1232_);
lean_dec(v_v_1223_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_instBEqMVarId_beq(v_x_1212_, v_key_1232_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_del_object(v___x_1235_);
v___x_1238_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1232_, v_val_1233_, v_x_1212_, v_x_1213_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
v___y_1227_ = v___x_1239_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1241_; 
lean_dec(v_val_1233_);
lean_dec(v_key_1232_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_x_1213_);
lean_ctor_set(v___x_1235_, 0, v_x_1212_);
v___x_1241_ = v___x_1235_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_x_1212_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_x_1213_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
v___y_1227_ = v___x_1241_;
goto v___jp_1226_;
}
}
}
}
case 1:
{
lean_object* v_node_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1256_; 
v_node_1244_ = lean_ctor_get(v_v_1223_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_v_1223_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1246_ = v_v_1223_;
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_node_1244_);
lean_dec(v_v_1223_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1248_ = ((size_t)5ULL);
v___x_1249_ = lean_usize_shift_right(v_x_1210_, v___x_1248_);
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_x_1211_, v___x_1250_);
v___x_1252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_node_1244_, v___x_1249_, v___x_1251_, v_x_1212_, v_x_1213_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1252_);
v___x_1254_ = v___x_1246_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v___y_1227_ = v___x_1254_;
goto v___jp_1226_;
}
}
}
default: 
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_x_1212_);
lean_ctor_set(v___x_1257_, 1, v_x_1213_);
v___y_1227_ = v___x_1257_;
goto v___jp_1226_;
}
}
v___jp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_array_fset(v_xs_x27_1225_, v_j_1217_, v___y_1227_);
lean_dec(v_j_1217_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1228_);
v___x_1230_ = v___x_1221_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
else
{
lean_object* v_ks_1260_; lean_object* v_vs_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1281_; 
v_ks_1260_ = lean_ctor_get(v_x_1209_, 0);
v_vs_1261_ = lean_ctor_get(v_x_1209_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1209_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1263_ = v_x_1209_;
v_isShared_1264_ = v_isSharedCheck_1281_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_vs_1261_);
lean_inc(v_ks_1260_);
lean_dec(v_x_1209_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1281_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_ks_1260_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_vs_1261_);
v___x_1266_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v_newNode_1267_; uint8_t v___y_1269_; size_t v___x_1275_; uint8_t v___x_1276_; 
v_newNode_1267_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v___x_1266_, v_x_1212_, v_x_1213_);
v___x_1275_ = ((size_t)7ULL);
v___x_1276_ = lean_usize_dec_le(v___x_1275_, v_x_1211_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1267_);
v___x_1278_ = lean_unsigned_to_nat(4u);
v___x_1279_ = lean_nat_dec_lt(v___x_1277_, v___x_1278_);
lean_dec(v___x_1277_);
v___y_1269_ = v___x_1279_;
goto v___jp_1268_;
}
else
{
v___y_1269_ = v___x_1276_;
goto v___jp_1268_;
}
v___jp_1268_:
{
if (v___y_1269_ == 0)
{
lean_object* v_ks_1270_; lean_object* v_vs_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_ks_1270_ = lean_ctor_get(v_newNode_1267_, 0);
lean_inc_ref(v_ks_1270_);
v_vs_1271_ = lean_ctor_get(v_newNode_1267_, 1);
lean_inc_ref(v_vs_1271_);
lean_dec_ref(v_newNode_1267_);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0);
v___x_1274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_x_1211_, v_ks_1270_, v_vs_1271_, v___x_1272_, v___x_1273_);
lean_dec_ref(v_vs_1271_);
lean_dec_ref(v_ks_1270_);
return v___x_1274_;
}
else
{
return v_newNode_1267_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(size_t v_depth_1282_, lean_object* v_keys_1283_, lean_object* v_vals_1284_, lean_object* v_i_1285_, lean_object* v_entries_1286_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_array_get_size(v_keys_1283_);
v___x_1288_ = lean_nat_dec_lt(v_i_1285_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec(v_i_1285_);
return v_entries_1286_;
}
else
{
lean_object* v_k_1289_; lean_object* v_v_1290_; uint64_t v___x_1291_; size_t v_h_1292_; size_t v___x_1293_; lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v_h_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_k_1289_ = lean_array_fget_borrowed(v_keys_1283_, v_i_1285_);
v_v_1290_ = lean_array_fget_borrowed(v_vals_1284_, v_i_1285_);
v___x_1291_ = l_Lean_instHashableMVarId_hash(v_k_1289_);
v_h_1292_ = lean_uint64_to_usize(v___x_1291_);
v___x_1293_ = ((size_t)5ULL);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_sub(v_depth_1282_, v___x_1295_);
v___x_1297_ = lean_usize_mul(v___x_1293_, v___x_1296_);
v_h_1298_ = lean_usize_shift_right(v_h_1292_, v___x_1297_);
v___x_1299_ = lean_nat_add(v_i_1285_, v___x_1294_);
lean_dec(v_i_1285_);
lean_inc(v_v_1290_);
lean_inc(v_k_1289_);
v___x_1300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_entries_1286_, v_h_1298_, v_depth_1282_, v_k_1289_, v_v_1290_);
v_i_1285_ = v___x_1299_;
v_entries_1286_ = v___x_1300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_depth_1302_, lean_object* v_keys_1303_, lean_object* v_vals_1304_, lean_object* v_i_1305_, lean_object* v_entries_1306_){
_start:
{
size_t v_depth_boxed_1307_; lean_object* v_res_1308_; 
v_depth_boxed_1307_ = lean_unbox_usize(v_depth_1302_);
lean_dec(v_depth_1302_);
v_res_1308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_boxed_1307_, v_keys_1303_, v_vals_1304_, v_i_1305_, v_entries_1306_);
lean_dec_ref(v_vals_1304_);
lean_dec_ref(v_keys_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
size_t v_x_24133__boxed_1314_; size_t v_x_24134__boxed_1315_; lean_object* v_res_1316_; 
v_x_24133__boxed_1314_ = lean_unbox_usize(v_x_1310_);
lean_dec(v_x_1310_);
v_x_24134__boxed_1315_ = lean_unbox_usize(v_x_1311_);
lean_dec(v_x_1311_);
v_res_1316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1309_, v_x_24133__boxed_1314_, v_x_24134__boxed_1315_, v_x_1312_, v_x_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(lean_object* v_x_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
uint64_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = l_Lean_instHashableMVarId_hash(v_x_1318_);
v___x_1321_ = lean_uint64_to_usize(v___x_1320_);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1317_, v___x_1321_, v___x_1322_, v_x_1318_, v_x_1319_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(lean_object* v_mvarId_1324_, lean_object* v_val_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v_mctx_1329_; lean_object* v_cache_1330_; lean_object* v_zetaDeltaFVarIds_1331_; lean_object* v_postponed_1332_; lean_object* v_diag_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1361_; 
v___x_1328_ = lean_st_ref_take(v___y_1326_);
v_mctx_1329_ = lean_ctor_get(v___x_1328_, 0);
v_cache_1330_ = lean_ctor_get(v___x_1328_, 1);
v_zetaDeltaFVarIds_1331_ = lean_ctor_get(v___x_1328_, 2);
v_postponed_1332_ = lean_ctor_get(v___x_1328_, 3);
v_diag_1333_ = lean_ctor_get(v___x_1328_, 4);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1335_ = v___x_1328_;
v_isShared_1336_ = v_isSharedCheck_1361_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_diag_1333_);
lean_inc(v_postponed_1332_);
lean_inc(v_zetaDeltaFVarIds_1331_);
lean_inc(v_cache_1330_);
lean_inc(v_mctx_1329_);
lean_dec(v___x_1328_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1361_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_depth_1337_; lean_object* v_levelAssignDepth_1338_; lean_object* v_lmvarCounter_1339_; lean_object* v_mvarCounter_1340_; lean_object* v_lDecls_1341_; lean_object* v_decls_1342_; lean_object* v_userNames_1343_; lean_object* v_lAssignment_1344_; lean_object* v_eAssignment_1345_; lean_object* v_dAssignment_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1360_; 
v_depth_1337_ = lean_ctor_get(v_mctx_1329_, 0);
v_levelAssignDepth_1338_ = lean_ctor_get(v_mctx_1329_, 1);
v_lmvarCounter_1339_ = lean_ctor_get(v_mctx_1329_, 2);
v_mvarCounter_1340_ = lean_ctor_get(v_mctx_1329_, 3);
v_lDecls_1341_ = lean_ctor_get(v_mctx_1329_, 4);
v_decls_1342_ = lean_ctor_get(v_mctx_1329_, 5);
v_userNames_1343_ = lean_ctor_get(v_mctx_1329_, 6);
v_lAssignment_1344_ = lean_ctor_get(v_mctx_1329_, 7);
v_eAssignment_1345_ = lean_ctor_get(v_mctx_1329_, 8);
v_dAssignment_1346_ = lean_ctor_get(v_mctx_1329_, 9);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_mctx_1329_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1348_ = v_mctx_1329_;
v_isShared_1349_ = v_isSharedCheck_1360_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_dAssignment_1346_);
lean_inc(v_eAssignment_1345_);
lean_inc(v_lAssignment_1344_);
lean_inc(v_userNames_1343_);
lean_inc(v_decls_1342_);
lean_inc(v_lDecls_1341_);
lean_inc(v_mvarCounter_1340_);
lean_inc(v_lmvarCounter_1339_);
lean_inc(v_levelAssignDepth_1338_);
lean_inc(v_depth_1337_);
lean_dec(v_mctx_1329_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1360_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_eAssignment_1345_, v_mvarId_1324_, v_val_1325_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 8, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_depth_1337_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_levelAssignDepth_1338_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_lmvarCounter_1339_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_mvarCounter_1340_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_lDecls_1341_);
lean_ctor_set(v_reuseFailAlloc_1359_, 5, v_decls_1342_);
lean_ctor_set(v_reuseFailAlloc_1359_, 6, v_userNames_1343_);
lean_ctor_set(v_reuseFailAlloc_1359_, 7, v_lAssignment_1344_);
lean_ctor_set(v_reuseFailAlloc_1359_, 8, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1359_, 9, v_dAssignment_1346_);
v___x_1352_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1352_);
v___x_1354_ = v___x_1335_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_cache_1330_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_zetaDeltaFVarIds_1331_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_postponed_1332_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_diag_1333_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_st_ref_set(v___y_1326_, v___x_1354_);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(lean_object* v_mvarId_1362_, lean_object* v_val_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1362_, v_val_1363_, v___y_1364_);
lean_dec(v___y_1364_);
return v_res_1366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = l_Lean_NameSet_empty;
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__0));
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___x_1369_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__2));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles(lean_object* v_mvarId_1377_, lean_object* v_hs_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_array_get_size(v_hs_1378_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_nat_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_inc(v_mvarId_1377_);
v___x_1389_ = l_Lean_MVarId_getDecl(v_mvarId_1377_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1492_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1492_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1492_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; lean_object* v_fst_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1490_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_sz_1396_ = lean_array_size(v_hs_1378_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_hs_1378_, v_sz_1396_, v___x_1397_, v___x_1395_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v___x_1398_, 1);
lean_dec(v_unused_1491_);
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1490_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_fst_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1490_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
if (lean_obj_tag(v_fst_1399_) == 0)
{
lean_object* v___x_1404_; 
lean_del_object(v___x_1401_);
lean_dec(v_a_1390_);
lean_dec_ref(v_hs_1378_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_mvarId_1377_);
v___x_1404_ = v___x_1392_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_mvarId_1377_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_object* v_val_1406_; 
v_val_1406_ = lean_ctor_get(v_fst_1399_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v_fst_1399_, 1);
if (lean_obj_tag(v_val_1406_) == 1)
{
lean_object* v_val_1407_; lean_object* v_userName_1408_; lean_object* v_lctx_1409_; lean_object* v_type_1410_; lean_object* v_localInstances_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_del_object(v___x_1392_);
v_val_1407_ = lean_ctor_get(v_val_1406_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v_val_1406_, 1);
v_userName_1408_ = lean_ctor_get(v_a_1390_, 0);
lean_inc(v_userName_1408_);
v_lctx_1409_ = lean_ctor_get(v_a_1390_, 1);
lean_inc_ref_n(v_lctx_1409_, 2);
v_type_1410_ = lean_ctor_get(v_a_1390_, 2);
lean_inc_ref(v_type_1410_);
v_localInstances_1411_ = lean_ctor_get(v_a_1390_, 4);
lean_inc_ref(v_localInstances_1411_);
lean_dec(v_a_1390_);
v___x_1412_ = lean_local_ctx_num_indices(v_lctx_1409_);
v___x_1413_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__1, &l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v___x_1413_);
lean_ctor_set(v___x_1401_, 0, v_hs_1378_);
v___x_1415_ = v___x_1401_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_hs_1378_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_lctx_1409_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v___x_1412_, v___x_1412_, v_val_1407_, v___x_1387_, v___x_1416_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_val_1407_);
lean_dec(v___x_1412_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v_snd_1419_; lean_object* v_snd_1420_; lean_object* v_fst_1421_; lean_object* v_fst_1422_; lean_object* v_fst_1423_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v_snd_1419_ = lean_ctor_get(v_a_1418_, 1);
lean_inc(v_snd_1419_);
v_snd_1420_ = lean_ctor_get(v_snd_1419_, 1);
lean_inc(v_snd_1420_);
v_fst_1421_ = lean_ctor_get(v_a_1418_, 0);
lean_inc(v_fst_1421_);
lean_dec(v_a_1418_);
v_fst_1422_ = lean_ctor_get(v_snd_1419_, 0);
lean_inc(v_fst_1422_);
lean_dec(v_snd_1419_);
v_fst_1423_ = lean_ctor_get(v_snd_1420_, 0);
lean_inc(v_fst_1423_);
lean_dec(v_snd_1420_);
v___x_1466_ = lean_array_get_size(v_fst_1422_);
lean_dec(v_fst_1422_);
v___x_1467_ = lean_nat_dec_eq(v___x_1466_, v___x_1387_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__3, &l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3);
v___x_1469_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v___x_1468_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref_known(v___x_1469_, 1);
v___y_1425_ = v_a_1379_;
v___y_1426_ = v_a_1380_;
v___y_1427_ = v_a_1381_;
v___y_1428_ = v_a_1382_;
v___y_1429_ = v_a_1383_;
v___y_1430_ = v_a_1384_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_fst_1423_);
lean_dec(v_fst_1421_);
lean_dec_ref(v_localInstances_1411_);
lean_dec_ref(v_type_1410_);
lean_dec(v_userName_1408_);
lean_dec(v_mvarId_1377_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
v___y_1425_ = v_a_1379_;
v___y_1426_ = v_a_1380_;
v___y_1427_ = v_a_1381_;
v___y_1428_ = v_a_1382_;
v___y_1429_ = v_a_1383_;
v___y_1430_ = v_a_1384_;
goto v___jp_1424_;
}
v___jp_1424_:
{
uint8_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = 2;
v___x_1432_ = l_Lean_Meta_mkFreshExprMVarAt(v_fst_1421_, v_localInstances_1411_, v_type_1410_, v___x_1431_, v_userName_1408_, v___x_1387_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; size_t v_sz_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l_Lean_Expr_mvarId_x21(v_a_1433_);
v_sz_1435_ = lean_array_size(v_fst_1423_);
v___x_1436_ = lean_box_usize(v_sz_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1));
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1438_, 0, v_fst_1423_);
lean_closure_set(v___f_1438_, 1, v___x_1436_);
lean_closure_set(v___f_1438_, 2, v___x_1437_);
lean_closure_set(v___f_1438_, 3, v___x_1394_);
lean_inc(v___x_1434_);
v___x_1439_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed), 10, 3);
lean_closure_set(v___x_1439_, 0, lean_box(0));
lean_closure_set(v___x_1439_, 1, v___x_1434_);
lean_closure_set(v___x_1439_, 2, v___f_1438_);
v___x_1440_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v___x_1439_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref_known(v___x_1440_, 1);
v___x_1441_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1377_, v_a_1433_, v___y_1428_);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1449_);
v___x_1443_ = v___x_1441_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v___x_1441_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1434_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1434_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v___x_1434_);
lean_dec(v_a_1433_);
lean_dec(v_mvarId_1377_);
v_a_1450_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1440_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1440_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_fst_1423_);
lean_dec(v_mvarId_1377_);
v_a_1458_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1432_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1432_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_localInstances_1411_);
lean_dec_ref(v_type_1410_);
lean_dec(v_userName_1408_);
lean_dec(v_mvarId_1377_);
v_a_1478_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1417_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1417_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_val_1406_);
lean_del_object(v___x_1401_);
lean_dec(v_a_1390_);
lean_dec_ref(v_hs_1378_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_mvarId_1377_);
v___x_1488_ = v___x_1392_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_mvarId_1377_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec_ref(v_hs_1378_);
lean_dec(v_mvarId_1377_);
v_a_1493_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1389_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1389_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1501_; 
lean_dec_ref(v_hs_1378_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_mvarId_1377_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___boxed(lean_object* v_mvarId_1502_, lean_object* v_hs_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Elab_Tactic_renameInaccessibles(v_mvarId_1502_, v_hs_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(lean_object* v_00_u03b1_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_x_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(v_00_u03b1_1522_, v_x_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(lean_object* v_mvarId_1532_, lean_object* v_val_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1532_, v_val_1533_, v___y_1537_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(lean_object* v_mvarId_1542_, lean_object* v_val_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(v_mvarId_1542_, v_val_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(lean_object* v_upperBound_1552_, lean_object* v___x_1553_, lean_object* v_val_1554_, lean_object* v_inst_1555_, lean_object* v_R_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_, lean_object* v_c_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_1552_, v___x_1553_, v_val_1554_, v_a_1557_, v_b_1558_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(lean_object* v_upperBound_1568_, lean_object* v___x_1569_, lean_object* v_val_1570_, lean_object* v_inst_1571_, lean_object* v_R_1572_, lean_object* v_a_1573_, lean_object* v_b_1574_, lean_object* v_c_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(v_upperBound_1568_, v___x_1569_, v_val_1570_, v_inst_1571_, v_R_1572_, v_a_1573_, v_b_1574_, v_c_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v_val_1570_);
lean_dec(v___x_1569_);
lean_dec(v_upperBound_1568_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_1587_, v___y_1588_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(lean_object* v_00_u03b1_1616_, lean_object* v_x_1617_, lean_object* v_ctx_x3f_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_1617_, v_ctx_x3f_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_x_1628_, lean_object* v_ctx_x3f_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(v_00_u03b1_1627_, v_x_1628_, v_ctx_x3f_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_x_1639_, v_x_1640_, v_x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1643_, lean_object* v_x_1644_, size_t v_x_1645_, size_t v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1644_, v_x_1645_, v_x_1646_, v_x_1647_, v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
size_t v_x_24751__boxed_1656_; size_t v_x_24752__boxed_1657_; lean_object* v_res_1658_; 
v_x_24751__boxed_1656_ = lean_unbox_usize(v_x_1652_);
lean_dec(v_x_1652_);
v_x_24752__boxed_1657_ = lean_unbox_usize(v_x_1653_);
lean_dec(v_x_1653_);
v_res_1658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(v_00_u03b2_1650_, v_x_1651_, v_x_24751__boxed_1656_, v_x_24752__boxed_1657_, v_x_1654_, v_x_1655_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(lean_object* v_ref_1659_, lean_object* v_msgData_1660_, uint8_t v_severity_1661_, uint8_t v_isSilent_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1659_, v_msgData_1660_, v_severity_1661_, v_isSilent_1662_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(lean_object* v_ref_1671_, lean_object* v_msgData_1672_, lean_object* v_severity_1673_, lean_object* v_isSilent_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_severity_boxed_1682_; uint8_t v_isSilent_boxed_1683_; lean_object* v_res_1684_; 
v_severity_boxed_1682_ = lean_unbox(v_severity_1673_);
v_isSilent_boxed_1683_ = lean_unbox(v_isSilent_1674_);
v_res_1684_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_1671_, v_msgData_1672_, v_severity_boxed_1682_, v_isSilent_boxed_1683_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_ref_1671_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(lean_object* v_00_u03b2_1685_, lean_object* v_n_1686_, lean_object* v_k_1687_, lean_object* v_v_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v_n_1686_, v_k_1687_, v_v_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1690_, size_t v_depth_1691_, lean_object* v_keys_1692_, lean_object* v_vals_1693_, lean_object* v_heq_1694_, lean_object* v_i_1695_, lean_object* v_entries_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_1691_, v_keys_1692_, v_vals_1693_, v_i_1695_, v_entries_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1698_, lean_object* v_depth_1699_, lean_object* v_keys_1700_, lean_object* v_vals_1701_, lean_object* v_heq_1702_, lean_object* v_i_1703_, lean_object* v_entries_1704_){
_start:
{
size_t v_depth_boxed_1705_; lean_object* v_res_1706_; 
v_depth_boxed_1705_ = lean_unbox_usize(v_depth_1699_);
lean_dec(v_depth_1699_);
v_res_1706_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(v_00_u03b2_1698_, v_depth_boxed_1705_, v_keys_1700_, v_vals_1701_, v_heq_1702_, v_i_1703_, v_entries_1704_);
lean_dec_ref(v_vals_1701_);
lean_dec_ref(v_keys_1700_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_x_1708_, v_x_1709_, v_x_1710_, v_x_1711_);
return v___x_1712_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
