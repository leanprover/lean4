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
size_t v_sz_boxed_137_; size_t v___x_22488__boxed_138_; lean_object* v_res_139_; 
v_sz_boxed_137_ = lean_unbox_usize(v_sz_127_);
lean_dec(v_sz_127_);
v___x_22488__boxed_138_ = lean_unbox_usize(v___x_128_);
lean_dec(v___x_128_);
v_res_139_ = l_Lean_Elab_Tactic_renameInaccessibles___lam__0(v_fst_126_, v_sz_boxed_137_, v___x_22488__boxed_138_, v___x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
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
lean_object* v___x_504_; lean_object* v_infoState_505_; uint8_t v_enabled_506_; 
v___x_504_ = lean_st_ref_get(v___y_502_);
v_infoState_505_ = lean_ctor_get(v___x_504_, 7);
lean_inc_ref(v_infoState_505_);
lean_dec(v___x_504_);
v_enabled_506_ = lean_ctor_get_uint8(v_infoState_505_, sizeof(void*)*3);
lean_dec_ref(v_infoState_505_);
if (v_enabled_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v_ctx_x3f_496_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_507_ = lean_apply_7(v_x_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
return v___x_507_;
}
else
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___boxed(lean_object* v_x_555_, lean_object* v_ctx_x3f_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_555_, v_ctx_x3f_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v___x_571_; lean_object* v_mctx_572_; lean_object* v_options_573_; lean_object* v_currNamespace_574_; lean_object* v_openDecls_575_; lean_object* v___x_576_; lean_object* v_ngen_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_569_ = lean_st_ref_get(v___y_567_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_env_570_);
lean_dec(v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_565_);
v_mctx_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_mctx_572_);
lean_dec(v___x_571_);
v_options_573_ = lean_ctor_get(v___y_566_, 2);
v_currNamespace_574_ = lean_ctor_get(v___y_566_, 6);
v_openDecls_575_ = lean_ctor_get(v___y_566_, 7);
v___x_576_ = lean_st_ref_get(v___y_567_);
v_ngen_577_ = lean_ctor_get(v___x_576_, 2);
lean_inc_ref(v_ngen_577_);
lean_dec(v___x_576_);
v___x_578_ = lean_box(0);
v___x_579_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_575_);
lean_inc(v_currNamespace_574_);
lean_inc_ref(v_options_573_);
v___x_580_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_580_, 0, v_env_570_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_ctor_set(v___x_580_, 3, v_mctx_572_);
lean_ctor_set(v___x_580_, 4, v_options_573_);
lean_ctor_set(v___x_580_, 5, v_currNamespace_574_);
lean_ctor_set(v___x_580_, 6, v_openDecls_575_);
lean_ctor_set(v___x_580_, 7, v_ngen_577_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_619_; 
v___x_594_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_590_, v___y_591_, v___y_592_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_619_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_619_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_619_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_fileMap_599_; lean_object* v_env_600_; lean_object* v_mctx_601_; lean_object* v_options_602_; lean_object* v_currNamespace_603_; lean_object* v_openDecls_604_; lean_object* v_ngen_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_616_; 
v_fileMap_599_ = lean_ctor_get(v___y_591_, 1);
v_env_600_ = lean_ctor_get(v_a_595_, 0);
v_mctx_601_ = lean_ctor_get(v_a_595_, 3);
v_options_602_ = lean_ctor_get(v_a_595_, 4);
v_currNamespace_603_ = lean_ctor_get(v_a_595_, 5);
v_openDecls_604_ = lean_ctor_get(v_a_595_, 6);
v_ngen_605_ = lean_ctor_get(v_a_595_, 7);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_595_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; 
v_unused_617_ = lean_ctor_get(v_a_595_, 2);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_a_595_, 1);
lean_dec(v_unused_618_);
v___x_607_ = v_a_595_;
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_ngen_605_);
lean_inc(v_openDecls_604_);
lean_inc(v_currNamespace_603_);
lean_inc(v_options_602_);
lean_inc(v_mctx_601_);
lean_inc(v_env_600_);
lean_dec(v_a_595_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
lean_inc_ref(v_fileMap_599_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v_fileMap_599_);
lean_ctor_set(v___x_607_, 1, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_env_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_fileMap_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_mctx_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_options_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_currNamespace_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_openDecls_604_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_ngen_605_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_611_);
v___x_613_ = v___x_597_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2___boxed(lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
v___x_635_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_a_636_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed(lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___f_663_; lean_object* v___x_664_; 
v___f_663_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0));
v___x_664_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_655_, v___f_663_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(lean_object* v_snd_674_, lean_object* v___x_675_, lean_object* v_____r_676_, lean_object* v_lctx_677_, lean_object* v_hs_678_, lean_object* v_info_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_687_ = l_Lean_NameSet_insert(v_snd_674_, v___x_675_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_info_679_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_hs_678_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_lctx_677_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(lean_object* v_snd_693_, lean_object* v___x_694_, lean_object* v_____r_695_, lean_object* v_lctx_696_, lean_object* v_hs_697_, lean_object* v_info_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_693_, v___x_694_, v_____r_695_, v_lctx_696_, v_hs_697_, v_info_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(lean_object* v_fst_707_, lean_object* v___f_708_, lean_object* v_snd_709_, lean_object* v_____r_710_, lean_object* v_lctx_711_, lean_object* v_info_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_720_ = lean_array_pop(v_fst_707_);
v___x_721_ = lean_array_get_size(v___x_720_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_snd_709_);
v___x_724_ = lean_box(0);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
v___x_725_ = lean_apply_11(v___f_708_, v___x_724_, v_lctx_711_, v___x_720_, v_info_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, lean_box(0));
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v___f_708_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_info_712_);
lean_ctor_set(v___x_726_, 1, v_snd_709_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_720_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_lctx_711_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(lean_object* v_fst_731_, lean_object* v___f_732_, lean_object* v_snd_733_, lean_object* v_____r_734_, lean_object* v_lctx_735_, lean_object* v_info_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_731_, v___f_732_, v_snd_733_, v_____r_734_, v_lctx_735_, v_info_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(lean_object* v_upperBound_753_, lean_object* v___x_754_, lean_object* v_val_755_, lean_object* v_a_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_a_766_; lean_object* v___y_771_; uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_lt(v_a_756_, v_upperBound_753_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v_a_756_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_b_757_);
return v___x_791_;
}
else
{
lean_object* v_snd_792_; lean_object* v_snd_793_; lean_object* v_fst_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_865_; 
v_snd_792_ = lean_ctor_get(v_b_757_, 1);
lean_inc(v_snd_792_);
v_snd_793_ = lean_ctor_get(v_snd_792_, 1);
lean_inc(v_snd_793_);
v_fst_794_ = lean_ctor_get(v_b_757_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_b_757_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_b_757_, 1);
lean_dec(v_unused_866_);
v___x_796_ = v_b_757_;
v_isShared_797_ = v_isSharedCheck_865_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_fst_794_);
lean_dec(v_b_757_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_865_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_fst_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_863_; 
v_fst_798_ = lean_ctor_get(v_snd_792_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_snd_792_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_snd_792_, 1);
lean_dec(v_unused_864_);
v___x_800_ = v_snd_792_;
v_isShared_801_ = v_isSharedCheck_863_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_fst_798_);
lean_dec(v_snd_792_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_863_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_862_; 
v_fst_802_ = lean_ctor_get(v_snd_793_, 0);
v_snd_803_ = lean_ctor_get(v_snd_793_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_snd_793_);
if (v_isSharedCheck_862_ == 0)
{
v___x_805_ = v_snd_793_;
v_isShared_806_ = v_isSharedCheck_862_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_inc(v_fst_802_);
lean_dec(v_snd_793_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_862_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = lean_nat_sub(v___x_754_, v_a_756_);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_sub(v___x_807_, v___x_808_);
lean_dec(v___x_807_);
v___x_810_ = l_Lean_LocalContext_getAt_x3f(v_fst_794_, v___x_809_);
lean_dec(v___x_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_812_; 
if (v_isShared_806_ == 0)
{
v___x_812_ = v___x_805_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_802_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_snd_803_);
v___x_812_ = v_reuseFailAlloc_819_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_812_);
v___x_814_ = v___x_800_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fst_798_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_814_);
v___x_816_ = v___x_796_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_fst_794_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v_a_766_ = v___x_816_;
goto v___jp_765_;
}
}
}
}
else
{
lean_object* v_val_820_; uint8_t v___x_821_; 
v_val_820_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_820_);
lean_dec_ref_known(v___x_810_, 1);
v___x_821_ = l_Lean_LocalDecl_isImplementationDetail(v_val_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___f_823_; lean_object* v___x_848_; uint8_t v___x_849_; 
lean_del_object(v___x_800_);
lean_del_object(v___x_796_);
v___x_822_ = l_Lean_LocalDecl_userName(v_val_820_);
lean_inc_n(v___x_822_, 2);
lean_inc(v_snd_803_);
v___f_823_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_823_, 0, v_snd_803_);
lean_closure_set(v___f_823_, 1, v___x_822_);
v___x_848_ = l_Lean_extractMacroScopes(v___x_822_);
v___x_849_ = l_Lean_MacroScopesView_equalScope(v___x_848_, v_val_755_);
lean_dec_ref(v___x_848_);
if (v___x_849_ == 0)
{
lean_dec(v___x_822_);
goto v___jp_824_;
}
else
{
if (v___x_821_ == 0)
{
uint8_t v___x_850_; 
v___x_850_ = l_Lean_NameSet_contains(v_snd_803_, v___x_822_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref(v___f_823_);
lean_dec(v_val_820_);
lean_del_object(v___x_805_);
v___x_851_ = lean_box(0);
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_803_, v___x_822_, v___x_851_, v_fst_794_, v_fst_798_, v_fst_802_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_771_ = v___x_852_;
goto v___jp_770_;
}
else
{
lean_dec(v___x_822_);
goto v___jp_824_;
}
}
else
{
lean_dec(v___x_822_);
goto v___jp_824_;
}
}
v___jp_824_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_825_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
v___x_826_ = lean_box(0);
v___x_827_ = lean_array_get_size(v_fst_798_);
v___x_828_ = lean_nat_sub(v___x_827_, v___x_808_);
v___x_829_ = lean_array_get_borrowed(v___x_826_, v_fst_798_, v___x_828_);
lean_dec(v___x_828_);
lean_inc(v___x_829_);
v___x_830_ = l_Lean_Syntax_isOfKind(v___x_829_, v___x_825_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_val_820_);
lean_del_object(v___x_805_);
v___x_831_ = lean_box(0);
v___x_832_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_798_, v___f_823_, v_snd_803_, v___x_831_, v_fst_794_, v_fst_802_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_771_ = v___x_832_;
goto v___jp_770_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l_Lean_Syntax_getArg(v___x_829_, v___x_833_);
v___x_835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_834_);
v___x_836_ = l_Lean_Syntax_isOfKind(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_834_);
lean_dec(v_val_820_);
lean_del_object(v___x_805_);
v___x_837_ = lean_box(0);
v___x_838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_798_, v___f_823_, v_snd_803_, v___x_837_, v_fst_794_, v_fst_802_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_771_ = v___x_838_;
goto v___jp_770_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_839_ = l_Lean_TSyntax_getId(v___x_834_);
v___x_840_ = l_Lean_LocalDecl_fvarId(v_val_820_);
lean_dec(v_val_820_);
lean_inc(v___x_840_);
v___x_841_ = l_Lean_LocalContext_setUserName(v_fst_794_, v___x_840_, v___x_839_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_834_);
lean_ctor_set(v___x_805_, 0, v___x_840_);
v___x_843_ = v___x_805_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_834_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_array_push(v_fst_802_, v___x_843_);
v___x_845_ = lean_box(0);
v___x_846_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_798_, v___f_823_, v_snd_803_, v___x_845_, v___x_841_, v___x_844_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_771_ = v___x_846_;
goto v___jp_770_;
}
}
}
}
}
else
{
lean_object* v___x_854_; 
lean_dec(v_val_820_);
if (v_isShared_806_ == 0)
{
v___x_854_ = v___x_805_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_802_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_803_);
v___x_854_ = v_reuseFailAlloc_861_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_854_);
v___x_856_ = v___x_800_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_fst_798_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_856_);
v___x_858_ = v___x_796_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_794_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
v_a_766_ = v___x_858_;
goto v___jp_765_;
}
}
}
}
}
}
}
}
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_a_756_, v___x_767_);
lean_dec(v_a_756_);
v_a_756_ = v___x_768_;
v_b_757_ = v_a_766_;
goto _start;
}
v___jp_770_:
{
if (lean_obj_tag(v___y_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_781_; 
v_a_772_ = lean_ctor_get(v___y_771_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___y_771_);
if (v_isSharedCheck_781_ == 0)
{
v___x_774_ = v___y_771_;
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___y_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
if (lean_obj_tag(v_a_772_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; 
lean_dec(v_a_756_);
v_a_776_ = lean_ctor_get(v_a_772_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v_a_772_, 1);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_a_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
lean_object* v_a_780_; 
lean_del_object(v___x_774_);
v_a_780_ = lean_ctor_get(v_a_772_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v_a_772_, 1);
v_a_766_ = v_a_780_;
goto v___jp_765_;
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_756_);
v_a_782_ = lean_ctor_get(v___y_771_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___y_771_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___y_771_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___y_771_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___boxed(lean_object* v_upperBound_867_, lean_object* v___x_868_, lean_object* v_val_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_867_, v___x_868_, v_val_869_, v_a_870_, v_b_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec_ref(v_val_869_);
lean_dec(v___x_868_);
lean_dec(v_upperBound_867_);
return v_res_879_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(uint8_t v___y_888_, uint8_t v_suppressElabErrors_889_, lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_890_) == 1)
{
lean_object* v_pre_891_; 
v_pre_891_ = lean_ctor_get(v_x_890_, 0);
switch(lean_obj_tag(v_pre_891_))
{
case 1:
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_pre_891_, 0);
switch(lean_obj_tag(v_pre_892_))
{
case 0:
{
lean_object* v_str_893_; lean_object* v_str_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_str_893_ = lean_ctor_get(v_x_890_, 1);
v_str_894_ = lean_ctor_get(v_pre_891_, 1);
v___x_895_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0));
v___x_896_ = lean_string_dec_eq(v_str_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1));
v___x_898_ = lean_string_dec_eq(v_str_894_, v___x_897_);
if (v___x_898_ == 0)
{
return v___y_888_;
}
else
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2));
v___x_900_ = lean_string_dec_eq(v_str_893_, v___x_899_);
if (v___x_900_ == 0)
{
return v___y_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3));
v___x_902_ = lean_string_dec_eq(v_str_893_, v___x_901_);
if (v___x_902_ == 0)
{
return v___y_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
}
case 1:
{
lean_object* v_pre_903_; 
v_pre_903_ = lean_ctor_get(v_pre_892_, 0);
if (lean_obj_tag(v_pre_903_) == 0)
{
lean_object* v_str_904_; lean_object* v_str_905_; lean_object* v_str_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_str_904_ = lean_ctor_get(v_x_890_, 1);
v_str_905_ = lean_ctor_get(v_pre_891_, 1);
v_str_906_ = lean_ctor_get(v_pre_892_, 1);
v___x_907_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4));
v___x_908_ = lean_string_dec_eq(v_str_906_, v___x_907_);
if (v___x_908_ == 0)
{
return v___y_888_;
}
else
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5));
v___x_910_ = lean_string_dec_eq(v_str_905_, v___x_909_);
if (v___x_910_ == 0)
{
return v___y_888_;
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6));
v___x_912_ = lean_string_dec_eq(v_str_904_, v___x_911_);
if (v___x_912_ == 0)
{
return v___y_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
}
}
else
{
return v___y_888_;
}
}
default: 
{
return v___y_888_;
}
}
}
case 0:
{
lean_object* v_str_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_str_913_ = lean_ctor_get(v_x_890_, 1);
v___x_914_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7));
v___x_915_ = lean_string_dec_eq(v_str_913_, v___x_914_);
if (v___x_915_ == 0)
{
return v___y_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
default: 
{
return v___y_888_;
}
}
}
else
{
return v___y_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed(lean_object* v___y_916_, lean_object* v_suppressElabErrors_917_, lean_object* v_x_918_){
_start:
{
uint8_t v___y_23686__boxed_919_; uint8_t v_suppressElabErrors_boxed_920_; uint8_t v_res_921_; lean_object* v_r_922_; 
v___y_23686__boxed_919_ = lean_unbox(v___y_916_);
v_suppressElabErrors_boxed_920_ = lean_unbox(v_suppressElabErrors_917_);
v_res_921_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v___y_23686__boxed_919_, v_suppressElabErrors_boxed_920_, v_x_918_);
lean_dec(v_x_918_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(lean_object* v_opts_923_, lean_object* v_opt_924_){
_start:
{
lean_object* v_name_925_; lean_object* v_defValue_926_; lean_object* v_map_927_; lean_object* v___x_928_; 
v_name_925_ = lean_ctor_get(v_opt_924_, 0);
v_defValue_926_ = lean_ctor_get(v_opt_924_, 1);
v_map_927_ = lean_ctor_get(v_opts_923_, 0);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_927_, v_name_925_);
if (lean_obj_tag(v___x_928_) == 0)
{
uint8_t v___x_929_; 
v___x_929_ = lean_unbox(v_defValue_926_);
return v___x_929_;
}
else
{
lean_object* v_val_930_; 
v_val_930_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v___x_928_, 1);
if (lean_obj_tag(v_val_930_) == 1)
{
uint8_t v_v_931_; 
v_v_931_ = lean_ctor_get_uint8(v_val_930_, 0);
lean_dec_ref_known(v_val_930_, 0);
return v_v_931_;
}
else
{
uint8_t v___x_932_; 
lean_dec(v_val_930_);
v___x_932_ = lean_unbox(v_defValue_926_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(lean_object* v_opts_933_, lean_object* v_opt_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_933_, v_opt_934_);
lean_dec_ref(v_opt_934_);
lean_dec_ref(v_opts_933_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(lean_object* v_msgData_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v_env_944_; lean_object* v___x_945_; lean_object* v_mctx_946_; lean_object* v_lctx_947_; lean_object* v_options_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_943_ = lean_st_ref_get(v___y_941_);
v_env_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_env_944_);
lean_dec(v___x_943_);
v___x_945_ = lean_st_ref_get(v___y_939_);
v_mctx_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_mctx_946_);
lean_dec(v___x_945_);
v_lctx_947_ = lean_ctor_get(v___y_938_, 2);
v_options_948_ = lean_ctor_get(v___y_940_, 2);
lean_inc_ref(v_options_948_);
lean_inc_ref(v_lctx_947_);
v___x_949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_949_, 0, v_env_944_);
lean_ctor_set(v___x_949_, 1, v_mctx_946_);
lean_ctor_set(v___x_949_, 2, v_lctx_947_);
lean_ctor_set(v___x_949_, 3, v_options_948_);
v___x_950_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v_msgData_937_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(lean_object* v_msgData_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(lean_object* v_ref_960_, lean_object* v_msgData_961_, uint8_t v_severity_962_, uint8_t v_isSilent_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; uint8_t v___y_1009_; lean_object* v___y_1010_; uint8_t v___y_1011_; uint8_t v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; uint8_t v___y_1048_; uint8_t v___x_1053_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; uint8_t v___y_1060_; uint8_t v___y_1061_; uint8_t v___y_1063_; uint8_t v___x_1078_; 
v___x_1053_ = 2;
v___x_1078_ = l_Lean_instBEqMessageSeverity_beq(v_severity_962_, v___x_1053_);
if (v___x_1078_ == 0)
{
v___y_1063_ = v___x_1078_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1079_; 
lean_inc_ref(v_msgData_961_);
v___x_1079_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_961_);
v___y_1063_ = v___x_1079_;
goto v___jp_1062_;
}
v___jp_969_:
{
lean_object* v___x_979_; lean_object* v_currNamespace_980_; lean_object* v_openDecls_981_; lean_object* v_env_982_; lean_object* v_nextMacroScope_983_; lean_object* v_ngen_984_; lean_object* v_auxDeclNGen_985_; lean_object* v_traceState_986_; lean_object* v_cache_987_; lean_object* v_messages_988_; lean_object* v_infoState_989_; lean_object* v_snapshotTasks_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1004_; 
v___x_979_ = lean_st_ref_take(v___y_978_);
v_currNamespace_980_ = lean_ctor_get(v___y_977_, 6);
v_openDecls_981_ = lean_ctor_get(v___y_977_, 7);
v_env_982_ = lean_ctor_get(v___x_979_, 0);
v_nextMacroScope_983_ = lean_ctor_get(v___x_979_, 1);
v_ngen_984_ = lean_ctor_get(v___x_979_, 2);
v_auxDeclNGen_985_ = lean_ctor_get(v___x_979_, 3);
v_traceState_986_ = lean_ctor_get(v___x_979_, 4);
v_cache_987_ = lean_ctor_get(v___x_979_, 5);
v_messages_988_ = lean_ctor_get(v___x_979_, 6);
v_infoState_989_ = lean_ctor_get(v___x_979_, 7);
v_snapshotTasks_990_ = lean_ctor_get(v___x_979_, 8);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_992_ = v___x_979_;
v_isShared_993_ = v_isSharedCheck_1004_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_snapshotTasks_990_);
lean_inc(v_infoState_989_);
lean_inc(v_messages_988_);
lean_inc(v_cache_987_);
lean_inc(v_traceState_986_);
lean_inc(v_auxDeclNGen_985_);
lean_inc(v_ngen_984_);
lean_inc(v_nextMacroScope_983_);
lean_inc(v_env_982_);
lean_dec(v___x_979_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1004_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_inc(v_openDecls_981_);
lean_inc(v_currNamespace_980_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_currNamespace_980_);
lean_ctor_set(v___x_994_, 1, v_openDecls_981_);
v___x_995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___y_971_);
lean_inc_ref(v___y_972_);
lean_inc_ref(v___y_975_);
v___x_996_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_996_, 0, v___y_975_);
lean_ctor_set(v___x_996_, 1, v___y_974_);
lean_ctor_set(v___x_996_, 2, v___y_970_);
lean_ctor_set(v___x_996_, 3, v___y_972_);
lean_ctor_set(v___x_996_, 4, v___x_995_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5, v___y_973_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5 + 1, v___y_976_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5 + 2, v_isSilent_963_);
v___x_997_ = l_Lean_MessageLog_add(v___x_996_, v_messages_988_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 6, v___x_997_);
v___x_999_ = v___x_992_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_env_982_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_nextMacroScope_983_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_ngen_984_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_auxDeclNGen_985_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_traceState_986_);
lean_ctor_set(v_reuseFailAlloc_1003_, 5, v_cache_987_);
lean_ctor_set(v_reuseFailAlloc_1003_, 6, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1003_, 7, v_infoState_989_);
lean_ctor_set(v_reuseFailAlloc_1003_, 8, v_snapshotTasks_990_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_st_ref_set(v___y_978_, v___x_999_);
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
}
v___jp_1005_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1029_; 
v___x_1014_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_961_);
v___x_1015_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v___x_1014_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1029_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1029_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_inc_ref_n(v___y_1010_, 2);
v___x_1020_ = l_Lean_FileMap_toPosition(v___y_1010_, v___y_1007_);
lean_dec(v___y_1007_);
v___x_1021_ = l_Lean_FileMap_toPosition(v___y_1010_, v___y_1013_);
lean_dec(v___y_1013_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0));
if (v___y_1011_ == 0)
{
lean_del_object(v___x_1018_);
lean_dec_ref(v___y_1006_);
v___y_970_ = v___x_1022_;
v___y_971_ = v_a_1016_;
v___y_972_ = v___x_1023_;
v___y_973_ = v___y_1009_;
v___y_974_ = v___x_1020_;
v___y_975_ = v___y_1008_;
v___y_976_ = v___y_1012_;
v___y_977_ = v___y_966_;
v___y_978_ = v___y_967_;
goto v___jp_969_;
}
else
{
uint8_t v___x_1024_; 
lean_inc(v_a_1016_);
v___x_1024_ = l_Lean_MessageData_hasTag(v___y_1006_, v_a_1016_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_dec_ref_known(v___x_1022_, 1);
lean_dec_ref(v___x_1020_);
lean_dec(v_a_1016_);
v___x_1025_ = lean_box(0);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1025_);
v___x_1027_ = v___x_1018_;
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
else
{
lean_del_object(v___x_1018_);
v___y_970_ = v___x_1022_;
v___y_971_ = v_a_1016_;
v___y_972_ = v___x_1023_;
v___y_973_ = v___y_1009_;
v___y_974_ = v___x_1020_;
v___y_975_ = v___y_1008_;
v___y_976_ = v___y_1012_;
v___y_977_ = v___y_966_;
v___y_978_ = v___y_967_;
goto v___jp_969_;
}
}
}
}
v___jp_1030_:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Syntax_getTailPos_x3f(v___y_1032_, v___y_1033_);
lean_dec(v___y_1032_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_inc(v___y_1038_);
v___y_1006_ = v___y_1031_;
v___y_1007_ = v___y_1038_;
v___y_1008_ = v___y_1034_;
v___y_1009_ = v___y_1033_;
v___y_1010_ = v___y_1035_;
v___y_1011_ = v___y_1037_;
v___y_1012_ = v___y_1036_;
v___y_1013_ = v___y_1038_;
goto v___jp_1005_;
}
else
{
lean_object* v_val_1040_; 
v_val_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___y_1006_ = v___y_1031_;
v___y_1007_ = v___y_1038_;
v___y_1008_ = v___y_1034_;
v___y_1009_ = v___y_1033_;
v___y_1010_ = v___y_1035_;
v___y_1011_ = v___y_1037_;
v___y_1012_ = v___y_1036_;
v___y_1013_ = v_val_1040_;
goto v___jp_1005_;
}
}
v___jp_1041_:
{
lean_object* v_ref_1049_; lean_object* v___x_1050_; 
v_ref_1049_ = l_Lean_replaceRef(v_ref_960_, v___y_1047_);
v___x_1050_ = l_Lean_Syntax_getPos_x3f(v_ref_1049_, v___y_1044_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___y_1031_ = v___y_1042_;
v___y_1032_ = v_ref_1049_;
v___y_1033_ = v___y_1044_;
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___y_1048_;
v___y_1037_ = v___y_1046_;
v___y_1038_ = v___x_1051_;
goto v___jp_1030_;
}
else
{
lean_object* v_val_1052_; 
v_val_1052_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v___x_1050_, 1);
v___y_1031_ = v___y_1042_;
v___y_1032_ = v_ref_1049_;
v___y_1033_ = v___y_1044_;
v___y_1034_ = v___y_1043_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___y_1048_;
v___y_1037_ = v___y_1046_;
v___y_1038_ = v_val_1052_;
goto v___jp_1030_;
}
}
v___jp_1054_:
{
if (v___y_1061_ == 0)
{
v___y_1042_ = v___y_1059_;
v___y_1043_ = v___y_1055_;
v___y_1044_ = v___y_1060_;
v___y_1045_ = v___y_1056_;
v___y_1046_ = v___y_1057_;
v___y_1047_ = v___y_1058_;
v___y_1048_ = v_severity_962_;
goto v___jp_1041_;
}
else
{
v___y_1042_ = v___y_1059_;
v___y_1043_ = v___y_1055_;
v___y_1044_ = v___y_1060_;
v___y_1045_ = v___y_1056_;
v___y_1046_ = v___y_1057_;
v___y_1047_ = v___y_1058_;
v___y_1048_ = v___x_1053_;
goto v___jp_1041_;
}
}
v___jp_1062_:
{
if (v___y_1063_ == 0)
{
lean_object* v_fileName_1064_; lean_object* v_fileMap_1065_; lean_object* v_options_1066_; lean_object* v_ref_1067_; uint8_t v_suppressElabErrors_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___f_1071_; uint8_t v___x_1072_; uint8_t v___x_1073_; 
v_fileName_1064_ = lean_ctor_get(v___y_966_, 0);
v_fileMap_1065_ = lean_ctor_get(v___y_966_, 1);
v_options_1066_ = lean_ctor_get(v___y_966_, 2);
v_ref_1067_ = lean_ctor_get(v___y_966_, 5);
v_suppressElabErrors_1068_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*14 + 1);
v___x_1069_ = lean_box(v___y_1063_);
v___x_1070_ = lean_box(v_suppressElabErrors_1068_);
v___f_1071_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1071_, 0, v___x_1069_);
lean_closure_set(v___f_1071_, 1, v___x_1070_);
v___x_1072_ = 1;
v___x_1073_ = l_Lean_instBEqMessageSeverity_beq(v_severity_962_, v___x_1072_);
if (v___x_1073_ == 0)
{
v___y_1055_ = v_fileName_1064_;
v___y_1056_ = v_fileMap_1065_;
v___y_1057_ = v_suppressElabErrors_1068_;
v___y_1058_ = v_ref_1067_;
v___y_1059_ = v___f_1071_;
v___y_1060_ = v___y_1063_;
v___y_1061_ = v___x_1073_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = l_Lean_warningAsError;
v___x_1075_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_options_1066_, v___x_1074_);
v___y_1055_ = v_fileName_1064_;
v___y_1056_ = v_fileMap_1065_;
v___y_1057_ = v_suppressElabErrors_1068_;
v___y_1058_ = v_ref_1067_;
v___y_1059_ = v___f_1071_;
v___y_1060_ = v___y_1063_;
v___y_1061_ = v___x_1075_;
goto v___jp_1054_;
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec_ref(v_msgData_961_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_ref_1080_, lean_object* v_msgData_1081_, lean_object* v_severity_1082_, lean_object* v_isSilent_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v_severity_boxed_1089_; uint8_t v_isSilent_boxed_1090_; lean_object* v_res_1091_; 
v_severity_boxed_1089_ = lean_unbox(v_severity_1082_);
v_isSilent_boxed_1090_ = lean_unbox(v_isSilent_1083_);
v_res_1091_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1080_, v_msgData_1081_, v_severity_boxed_1089_, v_isSilent_boxed_1090_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v_ref_1080_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(lean_object* v_msgData_1092_, uint8_t v_severity_1093_, uint8_t v_isSilent_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_ref_1102_; lean_object* v___x_1103_; 
v_ref_1102_ = lean_ctor_get(v___y_1099_, 5);
v___x_1103_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1102_, v_msgData_1092_, v_severity_1093_, v_isSilent_1094_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(lean_object* v_msgData_1104_, lean_object* v_severity_1105_, lean_object* v_isSilent_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_severity_boxed_1114_; uint8_t v_isSilent_boxed_1115_; lean_object* v_res_1116_; 
v_severity_boxed_1114_ = lean_unbox(v_severity_1105_);
v_isSilent_boxed_1115_ = lean_unbox(v_isSilent_1106_);
v_res_1116_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1104_, v_severity_boxed_1114_, v_isSilent_boxed_1115_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(lean_object* v_msgData_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = 2;
v___x_1126_ = 0;
v___x_1127_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1117_, v___x_1125_, v___x_1126_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(lean_object* v_msgData_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v_msgData_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(lean_object* v_as_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v_a_1145_; uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
if (v___x_1149_ == 0)
{
lean_inc_ref(v_b_1143_);
return v_b_1143_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_a_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_a_1152_ = lean_array_uget_borrowed(v_as_1140_, v_i_1142_);
v___x_1153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
lean_inc(v_a_1152_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v_a_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
v_a_1145_ = v___x_1151_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = l_Lean_Syntax_getArg(v_a_1152_, v___x_1155_);
v___x_1157_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_1156_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec(v___x_1156_);
v_a_1145_ = v___x_1151_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = l_Lean_TSyntax_getId(v___x_1156_);
lean_dec(v___x_1156_);
v___x_1160_ = l_Lean_extractMacroScopes(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1150_);
return v___x_1163_;
}
}
}
v___jp_1144_:
{
size_t v___x_1146_; size_t v___x_1147_; 
v___x_1146_ = ((size_t)1ULL);
v___x_1147_ = lean_usize_add(v_i_1142_, v___x_1146_);
v_i_1142_ = v___x_1147_;
v_b_1143_ = v_a_1145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___boxed(lean_object* v_as_1164_, lean_object* v_sz_1165_, lean_object* v_i_1166_, lean_object* v_b_1167_){
_start:
{
size_t v_sz_boxed_1168_; size_t v_i_boxed_1169_; lean_object* v_res_1170_; 
v_sz_boxed_1168_ = lean_unbox_usize(v_sz_1165_);
lean_dec(v_sz_1165_);
v_i_boxed_1169_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_1164_, v_sz_boxed_1168_, v_i_boxed_1169_, v_b_1167_);
lean_dec_ref(v_b_1167_);
lean_dec_ref(v_as_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_ks_1175_; lean_object* v_vs_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1200_; 
v_ks_1175_ = lean_ctor_get(v_x_1171_, 0);
v_vs_1176_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1178_ = v_x_1171_;
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_vs_1176_);
lean_inc(v_ks_1175_);
lean_dec(v_x_1171_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_ks_1175_);
v___x_1181_ = lean_nat_dec_lt(v_x_1172_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_x_1172_);
v___x_1182_ = lean_array_push(v_ks_1175_, v_x_1173_);
v___x_1183_ = lean_array_push(v_vs_1176_, v_x_1174_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1183_);
lean_ctor_set(v___x_1178_, 0, v___x_1182_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v_k_x27_1187_; uint8_t v___x_1188_; 
v_k_x27_1187_ = lean_array_fget_borrowed(v_ks_1175_, v_x_1172_);
v___x_1188_ = l_Lean_instBEqMVarId_beq(v_x_1173_, v_k_x27_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; 
if (v_isShared_1179_ == 0)
{
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_ks_1175_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_vs_1176_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_x_1172_, v___x_1191_);
lean_dec(v_x_1172_);
v_x_1171_ = v___x_1190_;
v_x_1172_ = v___x_1192_;
goto _start;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_array_fset(v_ks_1175_, v_x_1172_, v_x_1173_);
v___x_1196_ = lean_array_fset(v_vs_1176_, v_x_1172_, v_x_1174_);
lean_dec(v_x_1172_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1196_);
lean_ctor_set(v___x_1178_, 0, v___x_1195_);
v___x_1198_ = v___x_1178_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(lean_object* v_n_1201_, lean_object* v_k_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_n_1201_, v___x_1204_, v_k_1202_, v_v_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(lean_object* v_x_1207_, size_t v_x_1208_, size_t v_x_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_es_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_j_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_es_1212_ = lean_ctor_get(v_x_1207_, 0);
v___x_1213_ = ((size_t)31ULL);
v___x_1214_ = lean_usize_land(v_x_1208_, v___x_1213_);
v_j_1215_ = lean_usize_to_nat(v___x_1214_);
v___x_1216_ = lean_array_get_size(v_es_1212_);
v___x_1217_ = lean_nat_dec_lt(v_j_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_j_1215_);
lean_dec(v_x_1211_);
lean_dec(v_x_1210_);
return v_x_1207_;
}
else
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1256_; 
lean_inc_ref(v_es_1212_);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_x_1207_, 0);
lean_dec(v_unused_1257_);
v___x_1219_ = v_x_1207_;
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_x_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_v_1221_; lean_object* v___x_1222_; lean_object* v_xs_x27_1223_; lean_object* v___y_1225_; 
v_v_1221_ = lean_array_fget(v_es_1212_, v_j_1215_);
v___x_1222_ = lean_box(0);
v_xs_x27_1223_ = lean_array_fset(v_es_1212_, v_j_1215_, v___x_1222_);
switch(lean_obj_tag(v_v_1221_))
{
case 0:
{
lean_object* v_key_1230_; lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
v_key_1230_ = lean_ctor_get(v_v_1221_, 0);
v_val_1231_ = lean_ctor_get(v_v_1221_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1233_ = v_v_1221_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_inc(v_key_1230_);
lean_dec(v_v_1221_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Lean_instBEqMVarId_beq(v_x_1210_, v_key_1230_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_del_object(v___x_1233_);
v___x_1236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1230_, v_val_1231_, v_x_1210_, v_x_1211_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
v___y_1225_ = v___x_1237_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_val_1231_);
lean_dec(v_key_1230_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v_x_1211_);
lean_ctor_set(v___x_1233_, 0, v_x_1210_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_x_1210_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_x_1211_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v___y_1225_ = v___x_1239_;
goto v___jp_1224_;
}
}
}
}
case 1:
{
lean_object* v_node_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1254_; 
v_node_1242_ = lean_ctor_get(v_v_1221_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1244_ = v_v_1221_;
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_node_1242_);
lean_dec(v_v_1221_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_usize_shift_right(v_x_1208_, v___x_1246_);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_x_1209_, v___x_1248_);
v___x_1250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_node_1242_, v___x_1247_, v___x_1249_, v_x_1210_, v_x_1211_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1250_);
v___x_1252_ = v___x_1244_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v___y_1225_ = v___x_1252_;
goto v___jp_1224_;
}
}
}
default: 
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_x_1210_);
lean_ctor_set(v___x_1255_, 1, v_x_1211_);
v___y_1225_ = v___x_1255_;
goto v___jp_1224_;
}
}
v___jp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_array_fset(v_xs_x27_1223_, v_j_1215_, v___y_1225_);
lean_dec(v_j_1215_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1226_);
v___x_1228_ = v___x_1219_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
else
{
lean_object* v_ks_1258_; lean_object* v_vs_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1279_; 
v_ks_1258_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1259_ = lean_ctor_get(v_x_1207_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1261_ = v_x_1207_;
v_isShared_1262_ = v_isSharedCheck_1279_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_vs_1259_);
lean_inc(v_ks_1258_);
lean_dec(v_x_1207_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1279_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_ks_1258_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_vs_1259_);
v___x_1264_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v_newNode_1265_; uint8_t v___y_1267_; size_t v___x_1273_; uint8_t v___x_1274_; 
v_newNode_1265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v___x_1264_, v_x_1210_, v_x_1211_);
v___x_1273_ = ((size_t)7ULL);
v___x_1274_ = lean_usize_dec_le(v___x_1273_, v_x_1209_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1265_);
v___x_1276_ = lean_unsigned_to_nat(4u);
v___x_1277_ = lean_nat_dec_lt(v___x_1275_, v___x_1276_);
lean_dec(v___x_1275_);
v___y_1267_ = v___x_1277_;
goto v___jp_1266_;
}
else
{
v___y_1267_ = v___x_1274_;
goto v___jp_1266_;
}
v___jp_1266_:
{
if (v___y_1267_ == 0)
{
lean_object* v_ks_1268_; lean_object* v_vs_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_ks_1268_ = lean_ctor_get(v_newNode_1265_, 0);
lean_inc_ref(v_ks_1268_);
v_vs_1269_ = lean_ctor_get(v_newNode_1265_, 1);
lean_inc_ref(v_vs_1269_);
lean_dec_ref(v_newNode_1265_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0);
v___x_1272_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_x_1209_, v_ks_1268_, v_vs_1269_, v___x_1270_, v___x_1271_);
lean_dec_ref(v_vs_1269_);
lean_dec_ref(v_ks_1268_);
return v___x_1272_;
}
else
{
return v_newNode_1265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(size_t v_depth_1280_, lean_object* v_keys_1281_, lean_object* v_vals_1282_, lean_object* v_i_1283_, lean_object* v_entries_1284_){
_start:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = lean_array_get_size(v_keys_1281_);
v___x_1286_ = lean_nat_dec_lt(v_i_1283_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec(v_i_1283_);
return v_entries_1284_;
}
else
{
lean_object* v_k_1287_; lean_object* v_v_1288_; uint64_t v___x_1289_; size_t v_h_1290_; size_t v___x_1291_; lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; size_t v_h_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_k_1287_ = lean_array_fget_borrowed(v_keys_1281_, v_i_1283_);
v_v_1288_ = lean_array_fget_borrowed(v_vals_1282_, v_i_1283_);
v___x_1289_ = l_Lean_instHashableMVarId_hash(v_k_1287_);
v_h_1290_ = lean_uint64_to_usize(v___x_1289_);
v___x_1291_ = ((size_t)5ULL);
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_sub(v_depth_1280_, v___x_1293_);
v___x_1295_ = lean_usize_mul(v___x_1291_, v___x_1294_);
v_h_1296_ = lean_usize_shift_right(v_h_1290_, v___x_1295_);
v___x_1297_ = lean_nat_add(v_i_1283_, v___x_1292_);
lean_dec(v_i_1283_);
lean_inc(v_v_1288_);
lean_inc(v_k_1287_);
v___x_1298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_entries_1284_, v_h_1296_, v_depth_1280_, v_k_1287_, v_v_1288_);
v_i_1283_ = v___x_1297_;
v_entries_1284_ = v___x_1298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_depth_1300_, lean_object* v_keys_1301_, lean_object* v_vals_1302_, lean_object* v_i_1303_, lean_object* v_entries_1304_){
_start:
{
size_t v_depth_boxed_1305_; lean_object* v_res_1306_; 
v_depth_boxed_1305_ = lean_unbox_usize(v_depth_1300_);
lean_dec(v_depth_1300_);
v_res_1306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_boxed_1305_, v_keys_1301_, v_vals_1302_, v_i_1303_, v_entries_1304_);
lean_dec_ref(v_vals_1302_);
lean_dec_ref(v_keys_1301_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
size_t v_x_24182__boxed_1312_; size_t v_x_24183__boxed_1313_; lean_object* v_res_1314_; 
v_x_24182__boxed_1312_ = lean_unbox_usize(v_x_1308_);
lean_dec(v_x_1308_);
v_x_24183__boxed_1313_ = lean_unbox_usize(v_x_1309_);
lean_dec(v_x_1309_);
v_res_1314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1307_, v_x_24182__boxed_1312_, v_x_24183__boxed_1313_, v_x_1310_, v_x_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(lean_object* v_x_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
uint64_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = l_Lean_instHashableMVarId_hash(v_x_1316_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1315_, v___x_1319_, v___x_1320_, v_x_1316_, v_x_1317_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(lean_object* v_mvarId_1322_, lean_object* v_val_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; lean_object* v_mctx_1327_; lean_object* v_cache_1328_; lean_object* v_zetaDeltaFVarIds_1329_; lean_object* v_postponed_1330_; lean_object* v_diag_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1359_; 
v___x_1326_ = lean_st_ref_take(v___y_1324_);
v_mctx_1327_ = lean_ctor_get(v___x_1326_, 0);
v_cache_1328_ = lean_ctor_get(v___x_1326_, 1);
v_zetaDeltaFVarIds_1329_ = lean_ctor_get(v___x_1326_, 2);
v_postponed_1330_ = lean_ctor_get(v___x_1326_, 3);
v_diag_1331_ = lean_ctor_get(v___x_1326_, 4);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1333_ = v___x_1326_;
v_isShared_1334_ = v_isSharedCheck_1359_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_diag_1331_);
lean_inc(v_postponed_1330_);
lean_inc(v_zetaDeltaFVarIds_1329_);
lean_inc(v_cache_1328_);
lean_inc(v_mctx_1327_);
lean_dec(v___x_1326_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1359_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_depth_1335_; lean_object* v_levelAssignDepth_1336_; lean_object* v_lmvarCounter_1337_; lean_object* v_mvarCounter_1338_; lean_object* v_lDecls_1339_; lean_object* v_decls_1340_; lean_object* v_userNames_1341_; lean_object* v_lAssignment_1342_; lean_object* v_eAssignment_1343_; lean_object* v_dAssignment_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1358_; 
v_depth_1335_ = lean_ctor_get(v_mctx_1327_, 0);
v_levelAssignDepth_1336_ = lean_ctor_get(v_mctx_1327_, 1);
v_lmvarCounter_1337_ = lean_ctor_get(v_mctx_1327_, 2);
v_mvarCounter_1338_ = lean_ctor_get(v_mctx_1327_, 3);
v_lDecls_1339_ = lean_ctor_get(v_mctx_1327_, 4);
v_decls_1340_ = lean_ctor_get(v_mctx_1327_, 5);
v_userNames_1341_ = lean_ctor_get(v_mctx_1327_, 6);
v_lAssignment_1342_ = lean_ctor_get(v_mctx_1327_, 7);
v_eAssignment_1343_ = lean_ctor_get(v_mctx_1327_, 8);
v_dAssignment_1344_ = lean_ctor_get(v_mctx_1327_, 9);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_mctx_1327_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1346_ = v_mctx_1327_;
v_isShared_1347_ = v_isSharedCheck_1358_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_dAssignment_1344_);
lean_inc(v_eAssignment_1343_);
lean_inc(v_lAssignment_1342_);
lean_inc(v_userNames_1341_);
lean_inc(v_decls_1340_);
lean_inc(v_lDecls_1339_);
lean_inc(v_mvarCounter_1338_);
lean_inc(v_lmvarCounter_1337_);
lean_inc(v_levelAssignDepth_1336_);
lean_inc(v_depth_1335_);
lean_dec(v_mctx_1327_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1358_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_eAssignment_1343_, v_mvarId_1322_, v_val_1323_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 8, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_depth_1335_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_levelAssignDepth_1336_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_lmvarCounter_1337_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_mvarCounter_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_lDecls_1339_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_decls_1340_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_userNames_1341_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v_lAssignment_1342_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1357_, 9, v_dAssignment_1344_);
v___x_1350_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1350_);
v___x_1352_ = v___x_1333_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_cache_1328_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_zetaDeltaFVarIds_1329_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_postponed_1330_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_diag_1331_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_st_ref_set(v___y_1324_, v___x_1352_);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(lean_object* v_mvarId_1360_, lean_object* v_val_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1360_, v_val_1361_, v___y_1362_);
lean_dec(v___y_1362_);
return v_res_1364_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = l_Lean_NameSet_empty;
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__0));
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v___x_1367_);
return v___x_1369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__2));
v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles(lean_object* v_mvarId_1375_, lean_object* v_hs_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = lean_array_get_size(v_hs_1376_);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_nat_dec_eq(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_inc(v_mvarId_1375_);
v___x_1387_ = l_Lean_MVarId_getDecl(v_mvarId_1375_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1490_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1490_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1490_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_1396_; lean_object* v_fst_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1488_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_sz_1394_ = lean_array_size(v_hs_1376_);
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_hs_1376_, v_sz_1394_, v___x_1395_, v___x_1393_);
v_fst_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v___x_1396_, 1);
lean_dec(v_unused_1489_);
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1488_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_fst_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1488_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
if (lean_obj_tag(v_fst_1397_) == 0)
{
lean_object* v___x_1402_; 
lean_del_object(v___x_1399_);
lean_dec(v_a_1388_);
lean_dec_ref(v_hs_1376_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v_mvarId_1375_);
v___x_1402_ = v___x_1390_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_mvarId_1375_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v_fst_1397_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v_fst_1397_, 1);
if (lean_obj_tag(v_val_1404_) == 1)
{
lean_object* v_val_1405_; lean_object* v_userName_1406_; lean_object* v_lctx_1407_; lean_object* v_type_1408_; lean_object* v_localInstances_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_del_object(v___x_1390_);
v_val_1405_ = lean_ctor_get(v_val_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v_val_1404_, 1);
v_userName_1406_ = lean_ctor_get(v_a_1388_, 0);
lean_inc(v_userName_1406_);
v_lctx_1407_ = lean_ctor_get(v_a_1388_, 1);
lean_inc_ref_n(v_lctx_1407_, 2);
v_type_1408_ = lean_ctor_get(v_a_1388_, 2);
lean_inc_ref(v_type_1408_);
v_localInstances_1409_ = lean_ctor_get(v_a_1388_, 4);
lean_inc_ref(v_localInstances_1409_);
lean_dec(v_a_1388_);
v___x_1410_ = lean_local_ctx_num_indices(v_lctx_1407_);
v___x_1411_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__1, &l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v___x_1411_);
lean_ctor_set(v___x_1399_, 0, v_hs_1376_);
v___x_1413_ = v___x_1399_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_hs_1376_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_lctx_1407_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v___x_1410_, v___x_1410_, v_val_1405_, v___x_1385_, v___x_1414_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_val_1405_);
lean_dec(v___x_1410_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_snd_1417_; lean_object* v_snd_1418_; lean_object* v_fst_1419_; lean_object* v_fst_1420_; lean_object* v_fst_1421_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v_snd_1417_ = lean_ctor_get(v_a_1416_, 1);
lean_inc(v_snd_1417_);
v_snd_1418_ = lean_ctor_get(v_snd_1417_, 1);
lean_inc(v_snd_1418_);
v_fst_1419_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_fst_1419_);
lean_dec(v_a_1416_);
v_fst_1420_ = lean_ctor_get(v_snd_1417_, 0);
lean_inc(v_fst_1420_);
lean_dec(v_snd_1417_);
v_fst_1421_ = lean_ctor_get(v_snd_1418_, 0);
lean_inc(v_fst_1421_);
lean_dec(v_snd_1418_);
v___x_1464_ = lean_array_get_size(v_fst_1420_);
lean_dec(v_fst_1420_);
v___x_1465_ = lean_nat_dec_eq(v___x_1464_, v___x_1385_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__3, &l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3);
v___x_1467_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v___x_1466_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref_known(v___x_1467_, 1);
v___y_1423_ = v_a_1377_;
v___y_1424_ = v_a_1378_;
v___y_1425_ = v_a_1379_;
v___y_1426_ = v_a_1380_;
v___y_1427_ = v_a_1381_;
v___y_1428_ = v_a_1382_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_fst_1421_);
lean_dec(v_fst_1419_);
lean_dec_ref(v_localInstances_1409_);
lean_dec_ref(v_type_1408_);
lean_dec(v_userName_1406_);
lean_dec(v_mvarId_1375_);
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
v___y_1423_ = v_a_1377_;
v___y_1424_ = v_a_1378_;
v___y_1425_ = v_a_1379_;
v___y_1426_ = v_a_1380_;
v___y_1427_ = v_a_1381_;
v___y_1428_ = v_a_1382_;
goto v___jp_1422_;
}
v___jp_1422_:
{
uint8_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = 2;
v___x_1430_ = l_Lean_Meta_mkFreshExprMVarAt(v_fst_1419_, v_localInstances_1409_, v_type_1408_, v___x_1429_, v_userName_1406_, v___x_1385_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Expr_mvarId_x21(v_a_1431_);
v_sz_1433_ = lean_array_size(v_fst_1421_);
v___x_1434_ = lean_box_usize(v_sz_1433_);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1));
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1436_, 0, v_fst_1421_);
lean_closure_set(v___f_1436_, 1, v___x_1434_);
lean_closure_set(v___f_1436_, 2, v___x_1435_);
lean_closure_set(v___f_1436_, 3, v___x_1392_);
lean_inc(v___x_1432_);
v___x_1437_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed), 10, 3);
lean_closure_set(v___x_1437_, 0, lean_box(0));
lean_closure_set(v___x_1437_, 1, v___x_1432_);
lean_closure_set(v___x_1437_, 2, v___f_1436_);
v___x_1438_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v___x_1437_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref_known(v___x_1438_, 1);
v___x_1439_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1375_, v_a_1431_, v___y_1426_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1447_);
v___x_1441_ = v___x_1439_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v___x_1439_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1432_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1432_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v___x_1432_);
lean_dec(v_a_1431_);
lean_dec(v_mvarId_1375_);
v_a_1448_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1438_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1438_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_fst_1421_);
lean_dec(v_mvarId_1375_);
v_a_1456_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1430_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1430_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v_localInstances_1409_);
lean_dec_ref(v_type_1408_);
lean_dec(v_userName_1406_);
lean_dec(v_mvarId_1375_);
v_a_1476_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1415_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1415_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_val_1404_);
lean_del_object(v___x_1399_);
lean_dec(v_a_1388_);
lean_dec_ref(v_hs_1376_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v_mvarId_1375_);
v___x_1486_ = v___x_1390_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_mvarId_1375_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_hs_1376_);
lean_dec(v_mvarId_1375_);
v_a_1491_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1387_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1387_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v___x_1499_; 
lean_dec_ref(v_hs_1376_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_mvarId_1375_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___boxed(lean_object* v_mvarId_1500_, lean_object* v_hs_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Elab_Tactic_renameInaccessibles(v_mvarId_1500_, v_hs_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(lean_object* v_00_u03b1_1510_, lean_object* v_x_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_x_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(v_00_u03b1_1520_, v_x_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(lean_object* v_mvarId_1530_, lean_object* v_val_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1530_, v_val_1531_, v___y_1535_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(lean_object* v_mvarId_1540_, lean_object* v_val_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(v_mvarId_1540_, v_val_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(lean_object* v_upperBound_1550_, lean_object* v___x_1551_, lean_object* v_val_1552_, lean_object* v_inst_1553_, lean_object* v_R_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_, lean_object* v_c_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_1550_, v___x_1551_, v_val_1552_, v_a_1555_, v_b_1556_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(lean_object* v_upperBound_1566_, lean_object* v___x_1567_, lean_object* v_val_1568_, lean_object* v_inst_1569_, lean_object* v_R_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_, lean_object* v_c_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(v_upperBound_1566_, v___x_1567_, v_val_1568_, v_inst_1569_, v_R_1570_, v_a_1571_, v_b_1572_, v_c_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec_ref(v_val_1568_);
lean_dec(v___x_1567_);
lean_dec(v_upperBound_1566_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(lean_object* v_00_u03b1_1614_, lean_object* v_x_1615_, lean_object* v_ctx_x3f_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_1615_, v_ctx_x3f_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_x_1626_, lean_object* v_ctx_x3f_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(v_00_u03b1_1625_, v_x_1626_, v_ctx_x3f_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(lean_object* v_00_u03b2_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_x_1637_, v_x_1638_, v_x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1641_, lean_object* v_x_1642_, size_t v_x_1643_, size_t v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1642_, v_x_1643_, v_x_1644_, v_x_1645_, v_x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
size_t v_x_24800__boxed_1654_; size_t v_x_24801__boxed_1655_; lean_object* v_res_1656_; 
v_x_24800__boxed_1654_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_x_24801__boxed_1655_ = lean_unbox_usize(v_x_1651_);
lean_dec(v_x_1651_);
v_res_1656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(v_00_u03b2_1648_, v_x_1649_, v_x_24800__boxed_1654_, v_x_24801__boxed_1655_, v_x_1652_, v_x_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(lean_object* v_ref_1657_, lean_object* v_msgData_1658_, uint8_t v_severity_1659_, uint8_t v_isSilent_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1657_, v_msgData_1658_, v_severity_1659_, v_isSilent_1660_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(lean_object* v_ref_1669_, lean_object* v_msgData_1670_, lean_object* v_severity_1671_, lean_object* v_isSilent_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
uint8_t v_severity_boxed_1680_; uint8_t v_isSilent_boxed_1681_; lean_object* v_res_1682_; 
v_severity_boxed_1680_ = lean_unbox(v_severity_1671_);
v_isSilent_boxed_1681_ = lean_unbox(v_isSilent_1672_);
v_res_1682_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_1669_, v_msgData_1670_, v_severity_boxed_1680_, v_isSilent_boxed_1681_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_ref_1669_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(lean_object* v_00_u03b2_1683_, lean_object* v_n_1684_, lean_object* v_k_1685_, lean_object* v_v_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v_n_1684_, v_k_1685_, v_v_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1688_, size_t v_depth_1689_, lean_object* v_keys_1690_, lean_object* v_vals_1691_, lean_object* v_heq_1692_, lean_object* v_i_1693_, lean_object* v_entries_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_1689_, v_keys_1690_, v_vals_1691_, v_i_1693_, v_entries_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1696_, lean_object* v_depth_1697_, lean_object* v_keys_1698_, lean_object* v_vals_1699_, lean_object* v_heq_1700_, lean_object* v_i_1701_, lean_object* v_entries_1702_){
_start:
{
size_t v_depth_boxed_1703_; lean_object* v_res_1704_; 
v_depth_boxed_1703_ = lean_unbox_usize(v_depth_1697_);
lean_dec(v_depth_1697_);
v_res_1704_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(v_00_u03b2_1696_, v_depth_boxed_1703_, v_keys_1698_, v_vals_1699_, v_heq_1700_, v_i_1701_, v_entries_1702_);
lean_dec_ref(v_vals_1699_);
lean_dec_ref(v_keys_1698_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_x_1706_, v_x_1707_, v_x_1708_, v_x_1709_);
return v___x_1710_;
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
