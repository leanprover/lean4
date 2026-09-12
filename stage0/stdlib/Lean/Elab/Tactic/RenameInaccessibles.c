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
lean_object* v_a_83_; lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_a_83_ = lean_array_uget_borrowed(v_as_70_, v_i_72_);
v_fst_84_ = lean_ctor_get(v_a_83_, 0);
v_snd_85_ = lean_ctor_get(v_a_83_, 1);
v___x_86_ = lean_box(0);
lean_inc(v_fst_84_);
v___x_87_ = l_Lean_mkFVar(v_fst_84_);
lean_inc(v_snd_85_);
v___x_88_ = l_Lean_Elab_Term_addLocalVarInfo(v_snd_85_, v___x_87_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
if (lean_obj_tag(v___x_88_) == 0)
{
size_t v___x_89_; size_t v___x_90_; 
lean_dec_ref_known(v___x_88_, 1);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_add(v_i_72_, v___x_89_);
v_i_72_ = v___x_90_;
v_b_73_ = v___x_86_;
goto _start;
}
else
{
return v___x_88_;
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
size_t v_sz_boxed_137_; size_t v___x_20405__boxed_138_; lean_object* v_res_139_; 
v_sz_boxed_137_ = lean_unbox_usize(v_sz_127_);
lean_dec(v_sz_127_);
v___x_20405__boxed_138_ = lean_unbox_usize(v___x_128_);
lean_dec(v___x_128_);
v_res_139_ = l_Lean_Elab_Tactic_renameInaccessibles___lam__0(v_fst_126_, v_sz_boxed_137_, v___x_20405__boxed_138_, v___x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
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
v___x_178_ = lean_st_ref_put(v___y_149_, v___x_177_);
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
lean_object* v_assignment_202_; lean_object* v_v_203_; lean_object* v___x_204_; lean_object* v_bs_x27_205_; lean_object* v_a_207_; lean_object* v_tree_212_; lean_object* v___x_213_; 
v_assignment_202_ = lean_ctor_get(v___x_188_, 0);
v_v_203_ = lean_array_uget(v_bs_192_, v_i_191_);
v___x_204_ = lean_unsigned_to_nat(0u);
v_bs_x27_205_ = lean_array_uset(v_bs_192_, v_i_191_, v___x_204_);
v_tree_212_ = l_Lean_Elab_InfoTree_substitute(v_v_203_, v_assignment_202_);
lean_inc_ref(v_ctx_x3f_189_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
lean_inc(v___y_196_);
lean_inc_ref(v___y_195_);
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
v___x_213_ = lean_apply_7(v_ctx_x3f_189_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
if (lean_obj_tag(v_a_214_) == 0)
{
v_a_207_ = v_tree_212_;
goto v___jp_206_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
v_val_215_ = lean_ctor_get(v_a_214_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v_a_214_, 1);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_val_215_);
lean_ctor_set(v___x_216_, 1, v_tree_212_);
v_a_207_ = v___x_216_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v_tree_212_);
lean_dec_ref(v_bs_x27_205_);
lean_dec_ref(v_ctx_x3f_189_);
v_a_217_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_213_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_213_);
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
v___jp_206_:
{
size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_191_, v___x_208_);
v___x_210_ = lean_array_uset(v_bs_x27_205_, v_i_191_, v_a_207_);
v_i_191_ = v___x_209_;
v_bs_192_ = v___x_210_;
goto _start;
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
lean_object* v_v_318_; lean_object* v___x_319_; lean_object* v_bs_x27_320_; lean_object* v___x_321_; 
v_v_318_ = lean_array_uget(v_bs_308_, v_i_307_);
v___x_319_ = lean_unsigned_to_nat(0u);
v_bs_x27_320_ = lean_array_uset(v_bs_308_, v_i_307_, v___x_319_);
lean_inc_ref(v_ctx_x3f_305_);
v___x_321_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_304_, v_ctx_x3f_305_, v_v_318_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_307_, v___x_323_);
v___x_325_ = lean_array_uset(v_bs_x27_320_, v_i_307_, v_a_322_);
v_i_307_ = v___x_324_;
v_bs_308_ = v___x_325_;
goto _start;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_bs_x27_320_);
lean_dec_ref(v_ctx_x3f_305_);
v_a_327_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_321_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_321_);
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
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_460_ = lean_box(0);
v___x_461_ = l_Lean_PersistentArray_append___redArg(v_a_430_, v_a_437_);
lean_dec(v_a_437_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 2, v___x_461_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_assignment_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_lazyAssignment_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v___x_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_471_, sizeof(void*)*3, v_enabled_454_);
v___x_463_ = v_reuseFailAlloc_471_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 7, v___x_463_);
v___x_465_ = v___x_452_;
goto v_reusejp_464_;
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
lean_ctor_set(v_reuseFailAlloc_470_, 7, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_470_, 8, v_snapshotTasks_450_);
v___x_465_ = v_reuseFailAlloc_470_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_st_ref_put(v___y_423_, v___x_465_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_460_);
v___x_468_ = v___x_439_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_460_);
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
lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v___x_571_; lean_object* v_toCold_572_; lean_object* v_mctx_573_; lean_object* v_options_574_; lean_object* v_currNamespace_575_; lean_object* v_openDecls_576_; lean_object* v___x_577_; lean_object* v_ngen_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_569_ = lean_st_ref_get(v___y_567_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_env_570_);
lean_dec(v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_565_);
v_toCold_572_ = lean_ctor_get(v___y_566_, 0);
v_mctx_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_571_);
v_options_574_ = lean_ctor_get(v_toCold_572_, 2);
v_currNamespace_575_ = lean_ctor_get(v_toCold_572_, 4);
v_openDecls_576_ = lean_ctor_get(v_toCold_572_, 5);
v___x_577_ = lean_st_ref_get(v___y_567_);
v_ngen_578_ = lean_ctor_get(v___x_577_, 2);
lean_inc_ref(v_ngen_578_);
lean_dec(v___x_577_);
v___x_579_ = lean_box(0);
v___x_580_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_576_);
lean_inc(v_currNamespace_575_);
lean_inc_ref(v_options_574_);
v___x_581_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_581_, 0, v_env_570_);
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
lean_object* v___x_595_; lean_object* v_toCold_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_621_; 
v___x_595_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_591_, v___y_592_, v___y_593_);
v_toCold_596_ = lean_ctor_get(v___y_592_, 0);
v_a_597_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_621_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_621_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_621_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_fileMap_601_; lean_object* v_env_602_; lean_object* v_mctx_603_; lean_object* v_options_604_; lean_object* v_currNamespace_605_; lean_object* v_openDecls_606_; lean_object* v_ngen_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_618_; 
v_fileMap_601_ = lean_ctor_get(v_toCold_596_, 1);
v_env_602_ = lean_ctor_get(v_a_597_, 0);
v_mctx_603_ = lean_ctor_get(v_a_597_, 3);
v_options_604_ = lean_ctor_get(v_a_597_, 4);
v_currNamespace_605_ = lean_ctor_get(v_a_597_, 5);
v_openDecls_606_ = lean_ctor_get(v_a_597_, 6);
v_ngen_607_ = lean_ctor_get(v_a_597_, 7);
v_isSharedCheck_618_ = !lean_is_exclusive(v_a_597_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_619_ = lean_ctor_get(v_a_597_, 2);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_a_597_, 1);
lean_dec(v_unused_620_);
v___x_609_ = v_a_597_;
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_ngen_607_);
lean_inc(v_openDecls_606_);
lean_inc(v_currNamespace_605_);
lean_inc(v_options_604_);
lean_inc(v_mctx_603_);
lean_inc(v_env_602_);
lean_dec(v_a_597_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_box(0);
lean_inc_ref(v_fileMap_601_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 2, v_fileMap_601_);
lean_ctor_set(v___x_609_, 1, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_env_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_fileMap_601_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_mctx_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_options_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v_currNamespace_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_openDecls_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_ngen_607_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_613_);
v___x_615_ = v___x_599_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2___boxed(lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_647_; 
v___x_637_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_a_638_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed(lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_665_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0));
v___x_666_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_657_, v___f_665_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(lean_object* v_snd_676_, lean_object* v___x_677_, lean_object* v_____r_678_, lean_object* v_lctx_679_, lean_object* v_hs_680_, lean_object* v_info_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = l_Lean_NameSet_insert(v_snd_676_, v___x_677_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_info_681_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_hs_680_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_lctx_679_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(lean_object* v_snd_695_, lean_object* v___x_696_, lean_object* v_____r_697_, lean_object* v_lctx_698_, lean_object* v_hs_699_, lean_object* v_info_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_695_, v___x_696_, v_____r_697_, v_lctx_698_, v_hs_699_, v_info_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(lean_object* v_fst_709_, lean_object* v___f_710_, lean_object* v_snd_711_, lean_object* v_____r_712_, lean_object* v_lctx_713_, lean_object* v_info_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_722_ = lean_array_pop(v_fst_709_);
v___x_723_ = lean_array_get_size(v___x_722_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_nat_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v_snd_711_);
v___x_726_ = lean_box(0);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
v___x_727_ = lean_apply_11(v___f_710_, v___x_726_, v_lctx_713_, v___x_722_, v_info_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, lean_box(0));
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref(v___f_710_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_info_714_);
lean_ctor_set(v___x_728_, 1, v_snd_711_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_722_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_lctx_713_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(lean_object* v_fst_733_, lean_object* v___f_734_, lean_object* v_snd_735_, lean_object* v_____r_736_, lean_object* v_lctx_737_, lean_object* v_info_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_733_, v___f_734_, v_snd_735_, v_____r_736_, v_lctx_737_, v_info_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(lean_object* v_upperBound_755_, lean_object* v___x_756_, lean_object* v_val_757_, lean_object* v_a_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_a_768_; lean_object* v___y_773_; uint8_t v___x_792_; 
v___x_792_ = lean_nat_dec_lt(v_a_758_, v_upperBound_755_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v_a_758_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_b_759_);
return v___x_793_;
}
else
{
lean_object* v_snd_794_; lean_object* v_snd_795_; lean_object* v_fst_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_869_; 
v_snd_794_ = lean_ctor_get(v_b_759_, 1);
lean_inc(v_snd_794_);
v_snd_795_ = lean_ctor_get(v_snd_794_, 1);
lean_inc(v_snd_795_);
v_fst_796_ = lean_ctor_get(v_b_759_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_b_759_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_b_759_, 1);
lean_dec(v_unused_870_);
v___x_798_ = v_b_759_;
v_isShared_799_ = v_isSharedCheck_869_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_fst_796_);
lean_dec(v_b_759_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_869_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fst_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_867_; 
v_fst_800_ = lean_ctor_get(v_snd_794_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_snd_794_, 1);
lean_dec(v_unused_868_);
v___x_802_ = v_snd_794_;
v_isShared_803_ = v_isSharedCheck_867_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_fst_800_);
lean_dec(v_snd_794_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_867_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_866_; 
v_fst_804_ = lean_ctor_get(v_snd_795_, 0);
v_snd_805_ = lean_ctor_get(v_snd_795_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_snd_795_);
if (v_isSharedCheck_866_ == 0)
{
v___x_807_ = v_snd_795_;
v_isShared_808_ = v_isSharedCheck_866_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_inc(v_fst_804_);
lean_dec(v_snd_795_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_866_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_nat_sub(v___x_756_, v_a_758_);
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_sub(v___x_809_, v___x_810_);
lean_dec(v___x_809_);
v___x_812_ = l_Lean_LocalContext_getAt_x3f(v_fst_796_, v___x_811_);
lean_dec(v___x_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_814_; 
if (v_isShared_808_ == 0)
{
v___x_814_ = v___x_807_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_804_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_snd_805_);
v___x_814_ = v_reuseFailAlloc_821_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_814_);
v___x_816_ = v___x_802_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_816_);
v___x_818_ = v___x_798_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_768_ = v___x_818_;
goto v___jp_767_;
}
}
}
}
else
{
lean_object* v_val_822_; uint8_t v___x_823_; 
v_val_822_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v___x_812_, 1);
v___x_823_ = l_Lean_LocalDecl_isImplementationDetail(v_val_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___f_825_; lean_object* v___y_827_; lean_object* v___x_852_; uint8_t v___x_853_; 
lean_del_object(v___x_802_);
lean_del_object(v___x_798_);
v___x_824_ = l_Lean_LocalDecl_userName(v_val_822_);
lean_inc_n(v___x_824_, 2);
lean_inc(v_snd_805_);
v___f_825_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_825_, 0, v_snd_805_);
lean_closure_set(v___f_825_, 1, v___x_824_);
v___x_852_ = l_Lean_extractMacroScopes(v___x_824_);
v___x_853_ = l_Lean_MacroScopesView_equalScope(v___x_852_, v_val_757_);
lean_dec_ref(v___x_852_);
if (v___x_853_ == 0)
{
lean_dec(v___x_824_);
goto v___jp_837_;
}
else
{
if (v___x_823_ == 0)
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_NameSet_contains(v_snd_805_, v___x_824_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref(v___f_825_);
lean_dec(v_val_822_);
lean_del_object(v___x_807_);
v___x_855_ = lean_box(0);
v___x_856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_805_, v___x_824_, v___x_855_, v_fst_796_, v_fst_800_, v_fst_804_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
v___y_773_ = v___x_856_;
goto v___jp_772_;
}
else
{
lean_dec(v___x_824_);
goto v___jp_837_;
}
}
else
{
lean_dec(v___x_824_);
goto v___jp_837_;
}
}
v___jp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_828_ = l_Lean_TSyntax_getId(v___y_827_);
v___x_829_ = l_Lean_LocalDecl_fvarId(v_val_822_);
lean_dec(v_val_822_);
lean_inc(v___x_829_);
v___x_830_ = l_Lean_LocalContext_setUserName(v_fst_796_, v___x_829_, v___x_828_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___y_827_);
lean_ctor_set(v___x_807_, 0, v___x_829_);
v___x_832_ = v___x_807_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___y_827_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_array_push(v_fst_804_, v___x_832_);
v___x_834_ = lean_box(0);
v___x_835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_800_, v___f_825_, v_snd_805_, v___x_834_, v___x_830_, v___x_833_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
v___y_773_ = v___x_835_;
goto v___jp_772_;
}
}
v___jp_837_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
v___x_839_ = lean_box(0);
v___x_840_ = lean_array_get_size(v_fst_800_);
v___x_841_ = lean_nat_sub(v___x_840_, v___x_810_);
v___x_842_ = lean_array_get_borrowed(v___x_839_, v_fst_800_, v___x_841_);
lean_dec(v___x_841_);
lean_inc(v___x_842_);
v___x_843_ = l_Lean_Syntax_isOfKind(v___x_842_, v___x_838_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v_val_822_);
lean_del_object(v___x_807_);
v___x_844_ = lean_box(0);
v___x_845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_800_, v___f_825_, v_snd_805_, v___x_844_, v_fst_796_, v_fst_804_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
v___y_773_ = v___x_845_;
goto v___jp_772_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = l_Lean_Syntax_getArg(v___x_842_, v___x_846_);
if (v___x_823_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_847_);
v___x_849_ = l_Lean_Syntax_isOfKind(v___x_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v___x_847_);
lean_dec(v_val_822_);
lean_del_object(v___x_807_);
v___x_850_ = lean_box(0);
v___x_851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_800_, v___f_825_, v_snd_805_, v___x_850_, v_fst_796_, v_fst_804_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
v___y_773_ = v___x_851_;
goto v___jp_772_;
}
else
{
v___y_827_ = v___x_847_;
goto v___jp_826_;
}
}
else
{
v___y_827_ = v___x_847_;
goto v___jp_826_;
}
}
}
}
else
{
lean_object* v___x_858_; 
lean_dec(v_val_822_);
if (v_isShared_808_ == 0)
{
v___x_858_ = v___x_807_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_fst_804_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_snd_805_);
v___x_858_ = v_reuseFailAlloc_865_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_858_);
v___x_860_ = v___x_802_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_860_);
v___x_862_ = v___x_798_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v_a_768_ = v___x_862_;
goto v___jp_767_;
}
}
}
}
}
}
}
}
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_a_758_, v___x_769_);
lean_dec(v_a_758_);
v_a_758_ = v___x_770_;
v_b_759_ = v_a_768_;
goto _start;
}
v___jp_772_:
{
if (lean_obj_tag(v___y_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_783_; 
v_a_774_ = lean_ctor_get(v___y_773_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___y_773_);
if (v_isSharedCheck_783_ == 0)
{
v___x_776_ = v___y_773_;
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___y_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
if (lean_obj_tag(v_a_774_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; 
lean_dec(v_a_758_);
v_a_778_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v_a_774_, 1);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_a_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v_a_782_; 
lean_del_object(v___x_776_);
v_a_782_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v_a_774_, 1);
v_a_768_ = v_a_782_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_a_758_);
v_a_784_ = lean_ctor_get(v___y_773_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___y_773_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___y_773_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___y_773_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___boxed(lean_object* v_upperBound_871_, lean_object* v___x_872_, lean_object* v_val_873_, lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_871_, v___x_872_, v_val_873_, v_a_874_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_val_873_);
lean_dec(v___x_872_);
lean_dec(v_upperBound_871_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(uint8_t v_suppressElabErrors_892_, uint8_t v___y_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 1)
{
lean_object* v_pre_895_; 
v_pre_895_ = lean_ctor_get(v_x_894_, 0);
switch(lean_obj_tag(v_pre_895_))
{
case 1:
{
lean_object* v_pre_896_; 
v_pre_896_ = lean_ctor_get(v_pre_895_, 0);
switch(lean_obj_tag(v_pre_896_))
{
case 0:
{
lean_object* v_str_897_; lean_object* v_str_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_str_897_ = lean_ctor_get(v_x_894_, 1);
v_str_898_ = lean_ctor_get(v_pre_895_, 1);
v___x_899_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0));
v___x_900_ = lean_string_dec_eq(v_str_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1));
v___x_902_ = lean_string_dec_eq(v_str_898_, v___x_901_);
if (v___x_902_ == 0)
{
return v___x_902_;
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2));
v___x_904_ = lean_string_dec_eq(v_str_897_, v___x_903_);
if (v___x_904_ == 0)
{
return v___x_904_;
}
else
{
return v_suppressElabErrors_892_;
}
}
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3));
v___x_906_ = lean_string_dec_eq(v_str_897_, v___x_905_);
if (v___x_906_ == 0)
{
return v___x_906_;
}
else
{
return v_suppressElabErrors_892_;
}
}
}
case 1:
{
lean_object* v_pre_907_; 
v_pre_907_ = lean_ctor_get(v_pre_896_, 0);
if (lean_obj_tag(v_pre_907_) == 0)
{
lean_object* v_str_908_; lean_object* v_str_909_; lean_object* v_str_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_str_908_ = lean_ctor_get(v_x_894_, 1);
v_str_909_ = lean_ctor_get(v_pre_895_, 1);
v_str_910_ = lean_ctor_get(v_pre_896_, 1);
v___x_911_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4));
v___x_912_ = lean_string_dec_eq(v_str_910_, v___x_911_);
if (v___x_912_ == 0)
{
return v___x_912_;
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5));
v___x_914_ = lean_string_dec_eq(v_str_909_, v___x_913_);
if (v___x_914_ == 0)
{
return v___x_914_;
}
else
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6));
v___x_916_ = lean_string_dec_eq(v_str_908_, v___x_915_);
if (v___x_916_ == 0)
{
return v___x_916_;
}
else
{
return v_suppressElabErrors_892_;
}
}
}
}
else
{
return v___y_893_;
}
}
default: 
{
return v___y_893_;
}
}
}
case 0:
{
lean_object* v_str_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_str_917_ = lean_ctor_get(v_x_894_, 1);
v___x_918_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7));
v___x_919_ = lean_string_dec_eq(v_str_917_, v___x_918_);
if (v___x_919_ == 0)
{
return v___x_919_;
}
else
{
return v_suppressElabErrors_892_;
}
}
default: 
{
return v___y_893_;
}
}
}
else
{
return v___y_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_920_, lean_object* v___y_921_, lean_object* v_x_922_){
_start:
{
uint8_t v_suppressElabErrors_boxed_923_; uint8_t v___y_21607__boxed_924_; uint8_t v_res_925_; lean_object* v_r_926_; 
v_suppressElabErrors_boxed_923_ = lean_unbox(v_suppressElabErrors_920_);
v___y_21607__boxed_924_ = lean_unbox(v___y_921_);
v_res_925_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v_suppressElabErrors_boxed_923_, v___y_21607__boxed_924_, v_x_922_);
lean_dec(v_x_922_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(lean_object* v_opts_927_, lean_object* v_opt_928_){
_start:
{
lean_object* v_name_929_; lean_object* v_defValue_930_; lean_object* v_map_931_; lean_object* v___x_932_; 
v_name_929_ = lean_ctor_get(v_opt_928_, 0);
v_defValue_930_ = lean_ctor_get(v_opt_928_, 1);
v_map_931_ = lean_ctor_get(v_opts_927_, 0);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_931_, v_name_929_);
if (lean_obj_tag(v___x_932_) == 0)
{
uint8_t v___x_933_; 
v___x_933_ = lean_unbox(v_defValue_930_);
return v___x_933_;
}
else
{
lean_object* v_val_934_; 
v_val_934_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v___x_932_, 1);
if (lean_obj_tag(v_val_934_) == 1)
{
uint8_t v_v_935_; 
v_v_935_ = lean_ctor_get_uint8(v_val_934_, 0);
lean_dec_ref_known(v_val_934_, 0);
return v_v_935_;
}
else
{
uint8_t v___x_936_; 
lean_dec(v_val_934_);
v___x_936_ = lean_unbox(v_defValue_930_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(lean_object* v_opts_937_, lean_object* v_opt_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_937_, v_opt_938_);
lean_dec_ref(v_opt_938_);
lean_dec_ref(v_opts_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(lean_object* v_msgData_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v_env_948_; lean_object* v___x_949_; lean_object* v_toCold_950_; lean_object* v_mctx_951_; lean_object* v_lctx_952_; lean_object* v_options_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_947_ = lean_st_ref_get(v___y_945_);
v_env_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_947_);
v___x_949_ = lean_st_ref_get(v___y_943_);
v_toCold_950_ = lean_ctor_get(v___y_944_, 0);
v_mctx_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_mctx_951_);
lean_dec(v___x_949_);
v_lctx_952_ = lean_ctor_get(v___y_942_, 2);
v_options_953_ = lean_ctor_get(v_toCold_950_, 2);
lean_inc_ref(v_options_953_);
lean_inc_ref(v_lctx_952_);
v___x_954_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_954_, 0, v_env_948_);
lean_ctor_set(v___x_954_, 1, v_mctx_951_);
lean_ctor_set(v___x_954_, 2, v_lctx_952_);
lean_ctor_set(v___x_954_, 3, v_options_953_);
v___x_955_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_msgData_941_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(lean_object* v_msgData_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(lean_object* v_ref_965_, lean_object* v_msgData_966_, uint8_t v_severity_967_, uint8_t v_isSilent_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v_currNamespace_982_; lean_object* v_openDecls_983_; lean_object* v___y_984_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; uint8_t v___y_1013_; lean_object* v___y_1014_; uint8_t v___y_1015_; uint8_t v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1041_; uint8_t v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; uint8_t v___y_1053_; uint8_t v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; uint8_t v___x_1063_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; uint8_t v___y_1071_; lean_object* v___y_1072_; uint8_t v___y_1073_; uint8_t v___y_1075_; uint8_t v___x_1093_; 
v___x_1063_ = 2;
v___x_1093_ = l_Lean_instBEqMessageSeverity_beq(v_severity_967_, v___x_1063_);
if (v___x_1093_ == 0)
{
v___y_1075_ = v___x_1093_;
goto v___jp_1074_;
}
else
{
uint8_t v___x_1094_; 
lean_inc_ref(v_msgData_966_);
v___x_1094_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_966_);
v___y_1075_ = v___x_1094_;
goto v___jp_1074_;
}
v___jp_974_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_env_989_; lean_object* v_nextMacroScope_990_; lean_object* v_ngen_991_; lean_object* v_auxDeclNGen_992_; lean_object* v_traceState_993_; lean_object* v_cache_994_; lean_object* v_messages_995_; lean_object* v_infoState_996_; lean_object* v_snapshotTasks_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1008_; 
lean_inc(v_openDecls_983_);
lean_inc(v_currNamespace_982_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_currNamespace_982_);
lean_ctor_set(v___x_985_, 1, v_openDecls_983_);
v___x_986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___y_976_);
lean_inc_ref(v___y_980_);
lean_inc_ref(v___y_981_);
v___x_987_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_987_, 0, v___y_981_);
lean_ctor_set(v___x_987_, 1, v___y_977_);
lean_ctor_set(v___x_987_, 2, v___y_979_);
lean_ctor_set(v___x_987_, 3, v___y_980_);
lean_ctor_set(v___x_987_, 4, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*5, v___y_978_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*5 + 1, v___y_975_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*5 + 2, v_isSilent_968_);
v___x_988_ = lean_st_ref_take(v___y_984_);
v_env_989_ = lean_ctor_get(v___x_988_, 0);
v_nextMacroScope_990_ = lean_ctor_get(v___x_988_, 1);
v_ngen_991_ = lean_ctor_get(v___x_988_, 2);
v_auxDeclNGen_992_ = lean_ctor_get(v___x_988_, 3);
v_traceState_993_ = lean_ctor_get(v___x_988_, 4);
v_cache_994_ = lean_ctor_get(v___x_988_, 5);
v_messages_995_ = lean_ctor_get(v___x_988_, 6);
v_infoState_996_ = lean_ctor_get(v___x_988_, 7);
v_snapshotTasks_997_ = lean_ctor_get(v___x_988_, 8);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_999_ = v___x_988_;
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snapshotTasks_997_);
lean_inc(v_infoState_996_);
lean_inc(v_messages_995_);
lean_inc(v_cache_994_);
lean_inc(v_traceState_993_);
lean_inc(v_auxDeclNGen_992_);
lean_inc(v_ngen_991_);
lean_inc(v_nextMacroScope_990_);
lean_inc(v_env_989_);
lean_dec(v___x_988_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1001_ = lean_box(0);
v___x_1002_ = l_Lean_MessageLog_add(v___x_987_, v_messages_995_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 6, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_env_989_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_nextMacroScope_990_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ngen_991_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_auxDeclNGen_992_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_traceState_993_);
lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_cache_994_);
lean_ctor_set(v_reuseFailAlloc_1007_, 6, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1007_, 7, v_infoState_996_);
lean_ctor_set(v_reuseFailAlloc_1007_, 8, v_snapshotTasks_997_);
v___x_1004_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_st_ref_put(v___y_984_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
return v___x_1006_;
}
}
}
v___jp_1009_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1035_; 
v___x_1020_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_966_);
v___x_1021_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v___x_1020_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1035_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1035_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_inc_ref_n(v___y_1017_, 2);
v___x_1026_ = l_Lean_FileMap_toPosition(v___y_1017_, v___y_1014_);
lean_dec(v___y_1014_);
v___x_1027_ = l_Lean_FileMap_toPosition(v___y_1017_, v___y_1019_);
lean_dec(v___y_1019_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0));
if (v___y_1016_ == 0)
{
lean_del_object(v___x_1024_);
lean_dec_ref(v___y_1011_);
v___y_975_ = v___y_1013_;
v___y_976_ = v_a_1022_;
v___y_977_ = v___x_1026_;
v___y_978_ = v___y_1015_;
v___y_979_ = v___x_1028_;
v___y_980_ = v___x_1029_;
v___y_981_ = v___y_1018_;
v_currNamespace_982_ = v___y_1012_;
v_openDecls_983_ = v___y_1010_;
v___y_984_ = v___y_972_;
goto v___jp_974_;
}
else
{
uint8_t v___x_1030_; 
lean_inc(v_a_1022_);
v___x_1030_ = l_Lean_MessageData_hasTag(v___y_1011_, v_a_1022_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec_ref_known(v___x_1028_, 1);
lean_dec_ref(v___x_1026_);
lean_dec(v_a_1022_);
v___x_1031_ = lean_box(0);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1031_);
v___x_1033_ = v___x_1024_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
lean_del_object(v___x_1024_);
v___y_975_ = v___y_1013_;
v___y_976_ = v_a_1022_;
v___y_977_ = v___x_1026_;
v___y_978_ = v___y_1015_;
v___y_979_ = v___x_1028_;
v___y_980_ = v___x_1029_;
v___y_981_ = v___y_1018_;
v_currNamespace_982_ = v___y_1012_;
v_openDecls_983_ = v___y_1010_;
v___y_984_ = v___y_972_;
goto v___jp_974_;
}
}
}
}
v___jp_1036_:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Syntax_getTailPos_x3f(v___y_1041_, v___y_1042_);
lean_dec(v___y_1041_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_inc(v___y_1046_);
v___y_1010_ = v___y_1037_;
v___y_1011_ = v___y_1038_;
v___y_1012_ = v___y_1039_;
v___y_1013_ = v___y_1040_;
v___y_1014_ = v___y_1046_;
v___y_1015_ = v___y_1042_;
v___y_1016_ = v___y_1043_;
v___y_1017_ = v___y_1044_;
v___y_1018_ = v___y_1045_;
v___y_1019_ = v___y_1046_;
goto v___jp_1009_;
}
else
{
lean_object* v_val_1048_; 
v_val_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___y_1010_ = v___y_1037_;
v___y_1011_ = v___y_1038_;
v___y_1012_ = v___y_1039_;
v___y_1013_ = v___y_1040_;
v___y_1014_ = v___y_1046_;
v___y_1015_ = v___y_1042_;
v___y_1016_ = v___y_1043_;
v___y_1017_ = v___y_1044_;
v___y_1018_ = v___y_1045_;
v___y_1019_ = v_val_1048_;
goto v___jp_1009_;
}
}
v___jp_1049_:
{
lean_object* v_ref_1059_; lean_object* v___x_1060_; 
v_ref_1059_ = l_Lean_replaceRef(v_ref_965_, v___y_1056_);
v___x_1060_ = l_Lean_Syntax_getPos_x3f(v_ref_1059_, v___y_1053_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___y_1037_ = v___y_1050_;
v___y_1038_ = v___y_1051_;
v___y_1039_ = v___y_1052_;
v___y_1040_ = v___y_1058_;
v___y_1041_ = v_ref_1059_;
v___y_1042_ = v___y_1053_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1055_;
v___y_1045_ = v___y_1057_;
v___y_1046_ = v___x_1061_;
goto v___jp_1036_;
}
else
{
lean_object* v_val_1062_; 
v_val_1062_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_val_1062_);
lean_dec_ref_known(v___x_1060_, 1);
v___y_1037_ = v___y_1050_;
v___y_1038_ = v___y_1051_;
v___y_1039_ = v___y_1052_;
v___y_1040_ = v___y_1058_;
v___y_1041_ = v_ref_1059_;
v___y_1042_ = v___y_1053_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1055_;
v___y_1045_ = v___y_1057_;
v___y_1046_ = v_val_1062_;
goto v___jp_1036_;
}
}
v___jp_1064_:
{
if (v___y_1073_ == 0)
{
v___y_1050_ = v___y_1065_;
v___y_1051_ = v___y_1066_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1070_;
v___y_1054_ = v___y_1071_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1072_;
v___y_1057_ = v___y_1069_;
v___y_1058_ = v_severity_967_;
goto v___jp_1049_;
}
else
{
v___y_1050_ = v___y_1065_;
v___y_1051_ = v___y_1066_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1070_;
v___y_1054_ = v___y_1071_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1072_;
v___y_1057_ = v___y_1069_;
v___y_1058_ = v___x_1063_;
goto v___jp_1049_;
}
}
v___jp_1074_:
{
if (v___y_1075_ == 0)
{
lean_object* v_toCold_1076_; lean_object* v_ref_1077_; uint8_t v_suppressElabErrors_1078_; lean_object* v_fileName_1079_; lean_object* v_fileMap_1080_; lean_object* v_options_1081_; lean_object* v_currNamespace_1082_; lean_object* v_openDecls_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___f_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; 
v_toCold_1076_ = lean_ctor_get(v___y_971_, 0);
v_ref_1077_ = lean_ctor_get(v___y_971_, 2);
v_suppressElabErrors_1078_ = lean_ctor_get_uint8(v___y_971_, sizeof(void*)*3 + 1);
v_fileName_1079_ = lean_ctor_get(v_toCold_1076_, 0);
v_fileMap_1080_ = lean_ctor_get(v_toCold_1076_, 1);
v_options_1081_ = lean_ctor_get(v_toCold_1076_, 2);
v_currNamespace_1082_ = lean_ctor_get(v_toCold_1076_, 4);
v_openDecls_1083_ = lean_ctor_get(v_toCold_1076_, 5);
v___x_1084_ = lean_box(v_suppressElabErrors_1078_);
v___x_1085_ = lean_box(v___y_1075_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1086_, 0, v___x_1084_);
lean_closure_set(v___f_1086_, 1, v___x_1085_);
v___x_1087_ = 1;
v___x_1088_ = l_Lean_instBEqMessageSeverity_beq(v_severity_967_, v___x_1087_);
if (v___x_1088_ == 0)
{
v___y_1065_ = v_openDecls_1083_;
v___y_1066_ = v___f_1086_;
v___y_1067_ = v_currNamespace_1082_;
v___y_1068_ = v_fileMap_1080_;
v___y_1069_ = v_fileName_1079_;
v___y_1070_ = v___y_1075_;
v___y_1071_ = v_suppressElabErrors_1078_;
v___y_1072_ = v_ref_1077_;
v___y_1073_ = v___x_1088_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = l_Lean_warningAsError;
v___x_1090_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_options_1081_, v___x_1089_);
v___y_1065_ = v_openDecls_1083_;
v___y_1066_ = v___f_1086_;
v___y_1067_ = v_currNamespace_1082_;
v___y_1068_ = v_fileMap_1080_;
v___y_1069_ = v_fileName_1079_;
v___y_1070_ = v___y_1075_;
v___y_1071_ = v_suppressElabErrors_1078_;
v___y_1072_ = v_ref_1077_;
v___y_1073_ = v___x_1090_;
goto v___jp_1064_;
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_msgData_966_);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_ref_1095_, lean_object* v_msgData_1096_, lean_object* v_severity_1097_, lean_object* v_isSilent_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_severity_boxed_1104_; uint8_t v_isSilent_boxed_1105_; lean_object* v_res_1106_; 
v_severity_boxed_1104_ = lean_unbox(v_severity_1097_);
v_isSilent_boxed_1105_ = lean_unbox(v_isSilent_1098_);
v_res_1106_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1095_, v_msgData_1096_, v_severity_boxed_1104_, v_isSilent_boxed_1105_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v_ref_1095_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(lean_object* v_msgData_1107_, uint8_t v_severity_1108_, uint8_t v_isSilent_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; 
v_ref_1117_ = lean_ctor_get(v___y_1114_, 2);
v___x_1118_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1117_, v_msgData_1107_, v_severity_1108_, v_isSilent_1109_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(lean_object* v_msgData_1119_, lean_object* v_severity_1120_, lean_object* v_isSilent_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v_severity_boxed_1129_; uint8_t v_isSilent_boxed_1130_; lean_object* v_res_1131_; 
v_severity_boxed_1129_ = lean_unbox(v_severity_1120_);
v_isSilent_boxed_1130_ = lean_unbox(v_isSilent_1121_);
v_res_1131_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1119_, v_severity_boxed_1129_, v_isSilent_boxed_1130_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(lean_object* v_msgData_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = 2;
v___x_1141_ = 0;
v___x_1142_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_1132_, v___x_1140_, v___x_1141_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(lean_object* v_msgData_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v_msgData_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(lean_object* v_as_1155_, size_t v_sz_1156_, size_t v_i_1157_, lean_object* v_b_1158_){
_start:
{
lean_object* v_a_1160_; uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_lt(v_i_1157_, v_sz_1156_);
if (v___x_1164_ == 0)
{
lean_inc_ref(v_b_1158_);
return v_b_1158_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_a_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_a_1167_ = lean_array_uget_borrowed(v_as_1155_, v_i_1157_);
v___x_1168_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2));
lean_inc(v_a_1167_);
v___x_1169_ = l_Lean_Syntax_isOfKind(v_a_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
v_a_1160_ = v___x_1166_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = l_Lean_Syntax_getArg(v_a_1167_, v___x_1170_);
v___x_1172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4));
lean_inc(v___x_1171_);
v___x_1173_ = l_Lean_Syntax_isOfKind(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v___x_1171_);
v_a_1160_ = v___x_1166_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1174_ = l_Lean_TSyntax_getId(v___x_1171_);
lean_dec(v___x_1171_);
v___x_1175_ = l_Lean_extractMacroScopes(v___x_1174_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1165_);
return v___x_1178_;
}
}
}
v___jp_1159_:
{
size_t v___x_1161_; size_t v___x_1162_; 
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_add(v_i_1157_, v___x_1161_);
v_i_1157_ = v___x_1162_;
v_b_1158_ = v_a_1160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___boxed(lean_object* v_as_1179_, lean_object* v_sz_1180_, lean_object* v_i_1181_, lean_object* v_b_1182_){
_start:
{
size_t v_sz_boxed_1183_; size_t v_i_boxed_1184_; lean_object* v_res_1185_; 
v_sz_boxed_1183_ = lean_unbox_usize(v_sz_1180_);
lean_dec(v_sz_1180_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1181_);
lean_dec(v_i_1181_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_1179_, v_sz_boxed_1183_, v_i_boxed_1184_, v_b_1182_);
lean_dec_ref(v_b_1182_);
lean_dec_ref(v_as_1179_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
lean_object* v_ks_1190_; lean_object* v_vs_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1215_; 
v_ks_1190_ = lean_ctor_get(v_x_1186_, 0);
v_vs_1191_ = lean_ctor_get(v_x_1186_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1193_ = v_x_1186_;
v_isShared_1194_ = v_isSharedCheck_1215_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_vs_1191_);
lean_inc(v_ks_1190_);
lean_dec(v_x_1186_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1215_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_array_get_size(v_ks_1190_);
v___x_1196_ = lean_nat_dec_lt(v_x_1187_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_dec(v_x_1187_);
v___x_1197_ = lean_array_push(v_ks_1190_, v_x_1188_);
v___x_1198_ = lean_array_push(v_vs_1191_, v_x_1189_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1198_);
lean_ctor_set(v___x_1193_, 0, v___x_1197_);
v___x_1200_ = v___x_1193_;
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
else
{
lean_object* v_k_x27_1202_; uint8_t v___x_1203_; 
v_k_x27_1202_ = lean_array_fget_borrowed(v_ks_1190_, v_x_1187_);
v___x_1203_ = l_Lean_instBEqMVarId_beq(v_x_1188_, v_k_x27_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1205_; 
if (v_isShared_1194_ == 0)
{
v___x_1205_ = v___x_1193_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_ks_1190_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_vs_1191_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_x_1187_, v___x_1206_);
lean_dec(v_x_1187_);
v_x_1186_ = v___x_1205_;
v_x_1187_ = v___x_1207_;
goto _start;
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1210_ = lean_array_fset(v_ks_1190_, v_x_1187_, v_x_1188_);
v___x_1211_ = lean_array_fset(v_vs_1191_, v_x_1187_, v_x_1189_);
lean_dec(v_x_1187_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1211_);
lean_ctor_set(v___x_1193_, 0, v___x_1210_);
v___x_1213_ = v___x_1193_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(lean_object* v_n_1216_, lean_object* v_k_1217_, lean_object* v_v_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_n_1216_, v___x_1219_, v_k_1217_, v_v_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(lean_object* v_x_1222_, size_t v_x_1223_, size_t v_x_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
lean_object* v_es_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v_j_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_es_1227_ = lean_ctor_get(v_x_1222_, 0);
v___x_1228_ = ((size_t)31ULL);
v___x_1229_ = lean_usize_land(v_x_1223_, v___x_1228_);
v_j_1230_ = lean_usize_to_nat(v___x_1229_);
v___x_1231_ = lean_array_get_size(v_es_1227_);
v___x_1232_ = lean_nat_dec_lt(v_j_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v_j_1230_);
lean_dec(v_x_1226_);
lean_dec(v_x_1225_);
return v_x_1222_;
}
else
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1271_; 
lean_inc_ref(v_es_1227_);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_x_1222_, 0);
lean_dec(v_unused_1272_);
v___x_1234_ = v_x_1222_;
v_isShared_1235_ = v_isSharedCheck_1271_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v_x_1222_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1271_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_v_1236_; lean_object* v___x_1237_; lean_object* v_xs_x27_1238_; lean_object* v___y_1240_; 
v_v_1236_ = lean_array_fget(v_es_1227_, v_j_1230_);
v___x_1237_ = lean_box(0);
v_xs_x27_1238_ = lean_array_fset(v_es_1227_, v_j_1230_, v___x_1237_);
switch(lean_obj_tag(v_v_1236_))
{
case 0:
{
lean_object* v_key_1245_; lean_object* v_val_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1256_; 
v_key_1245_ = lean_ctor_get(v_v_1236_, 0);
v_val_1246_ = lean_ctor_get(v_v_1236_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_v_1236_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1248_ = v_v_1236_;
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_val_1246_);
lean_inc(v_key_1245_);
lean_dec(v_v_1236_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
uint8_t v___x_1250_; 
v___x_1250_ = l_Lean_instBEqMVarId_beq(v_x_1225_, v_key_1245_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1248_);
v___x_1251_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1245_, v_val_1246_, v_x_1225_, v_x_1226_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
v___y_1240_ = v___x_1252_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_val_1246_);
lean_dec(v_key_1245_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_x_1226_);
lean_ctor_set(v___x_1248_, 0, v_x_1225_);
v___x_1254_ = v___x_1248_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_x_1225_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_x_1226_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v___y_1240_ = v___x_1254_;
goto v___jp_1239_;
}
}
}
}
case 1:
{
lean_object* v_node_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_node_1257_ = lean_ctor_get(v_v_1236_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_v_1236_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v_v_1236_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_node_1257_);
lean_dec(v_v_1236_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1261_ = ((size_t)5ULL);
v___x_1262_ = lean_usize_shift_right(v_x_1223_, v___x_1261_);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_x_1224_, v___x_1263_);
v___x_1265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_node_1257_, v___x_1262_, v___x_1264_, v_x_1225_, v_x_1226_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1265_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v___y_1240_ = v___x_1267_;
goto v___jp_1239_;
}
}
}
default: 
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_x_1225_);
lean_ctor_set(v___x_1270_, 1, v_x_1226_);
v___y_1240_ = v___x_1270_;
goto v___jp_1239_;
}
}
v___jp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_array_fset(v_xs_x27_1238_, v_j_1230_, v___y_1240_);
lean_dec(v_j_1230_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1241_);
v___x_1243_ = v___x_1234_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
else
{
lean_object* v_ks_1273_; lean_object* v_vs_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1292_; 
v_ks_1273_ = lean_ctor_get(v_x_1222_, 0);
v_vs_1274_ = lean_ctor_get(v_x_1222_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1276_ = v_x_1222_;
v_isShared_1277_ = v_isSharedCheck_1292_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_vs_1274_);
lean_inc(v_ks_1273_);
lean_dec(v_x_1222_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1292_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_ks_1273_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_vs_1274_);
v___x_1279_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v_newNode_1280_; size_t v___x_1281_; uint8_t v___x_1282_; 
v_newNode_1280_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v___x_1279_, v_x_1225_, v_x_1226_);
v___x_1281_ = ((size_t)7ULL);
v___x_1282_ = lean_usize_dec_le(v___x_1281_, v_x_1224_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1283_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1280_);
v___x_1284_ = lean_unsigned_to_nat(4u);
v___x_1285_ = lean_nat_dec_lt(v___x_1283_, v___x_1284_);
lean_dec(v___x_1283_);
if (v___x_1285_ == 0)
{
lean_object* v_ks_1286_; lean_object* v_vs_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_ks_1286_ = lean_ctor_get(v_newNode_1280_, 0);
lean_inc_ref(v_ks_1286_);
v_vs_1287_ = lean_ctor_get(v_newNode_1280_, 1);
lean_inc_ref(v_vs_1287_);
lean_dec_ref(v_newNode_1280_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0);
v___x_1290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_x_1224_, v_ks_1286_, v_vs_1287_, v___x_1288_, v___x_1289_);
lean_dec_ref(v_vs_1287_);
lean_dec_ref(v_ks_1286_);
return v___x_1290_;
}
else
{
return v_newNode_1280_;
}
}
else
{
return v_newNode_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(size_t v_depth_1293_, lean_object* v_keys_1294_, lean_object* v_vals_1295_, lean_object* v_i_1296_, lean_object* v_entries_1297_){
_start:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_array_get_size(v_keys_1294_);
v___x_1299_ = lean_nat_dec_lt(v_i_1296_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec(v_i_1296_);
return v_entries_1297_;
}
else
{
lean_object* v_k_1300_; lean_object* v_v_1301_; uint64_t v___x_1302_; size_t v_h_1303_; size_t v___x_1304_; lean_object* v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v_h_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_k_1300_ = lean_array_fget_borrowed(v_keys_1294_, v_i_1296_);
v_v_1301_ = lean_array_fget_borrowed(v_vals_1295_, v_i_1296_);
v___x_1302_ = l_Lean_instHashableMVarId_hash(v_k_1300_);
v_h_1303_ = lean_uint64_to_usize(v___x_1302_);
v___x_1304_ = ((size_t)5ULL);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_sub(v_depth_1293_, v___x_1306_);
v___x_1308_ = lean_usize_mul(v___x_1304_, v___x_1307_);
v_h_1309_ = lean_usize_shift_right(v_h_1303_, v___x_1308_);
v___x_1310_ = lean_nat_add(v_i_1296_, v___x_1305_);
lean_dec(v_i_1296_);
lean_inc(v_v_1301_);
lean_inc(v_k_1300_);
v___x_1311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_entries_1297_, v_h_1309_, v_depth_1293_, v_k_1300_, v_v_1301_);
v_i_1296_ = v___x_1310_;
v_entries_1297_ = v___x_1311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_depth_1313_, lean_object* v_keys_1314_, lean_object* v_vals_1315_, lean_object* v_i_1316_, lean_object* v_entries_1317_){
_start:
{
size_t v_depth_boxed_1318_; lean_object* v_res_1319_; 
v_depth_boxed_1318_ = lean_unbox_usize(v_depth_1313_);
lean_dec(v_depth_1313_);
v_res_1319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_boxed_1318_, v_keys_1314_, v_vals_1315_, v_i_1316_, v_entries_1317_);
lean_dec_ref(v_vals_1315_);
lean_dec_ref(v_keys_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_x_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
size_t v_x_22123__boxed_1325_; size_t v_x_22124__boxed_1326_; lean_object* v_res_1327_; 
v_x_22123__boxed_1325_ = lean_unbox_usize(v_x_1321_);
lean_dec(v_x_1321_);
v_x_22124__boxed_1326_ = lean_unbox_usize(v_x_1322_);
lean_dec(v_x_1322_);
v_res_1327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1320_, v_x_22123__boxed_1325_, v_x_22124__boxed_1326_, v_x_1323_, v_x_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
uint64_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = l_Lean_instHashableMVarId_hash(v_x_1329_);
v___x_1332_ = lean_uint64_to_usize(v___x_1331_);
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1328_, v___x_1332_, v___x_1333_, v_x_1329_, v_x_1330_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(lean_object* v_mvarId_1335_, lean_object* v_val_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; lean_object* v_mctx_1340_; lean_object* v_cache_1341_; lean_object* v_zetaDeltaFVarIds_1342_; lean_object* v_postponed_1343_; lean_object* v_diag_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1373_; 
v___x_1339_ = lean_st_ref_take(v___y_1337_);
v_mctx_1340_ = lean_ctor_get(v___x_1339_, 0);
v_cache_1341_ = lean_ctor_get(v___x_1339_, 1);
v_zetaDeltaFVarIds_1342_ = lean_ctor_get(v___x_1339_, 2);
v_postponed_1343_ = lean_ctor_get(v___x_1339_, 3);
v_diag_1344_ = lean_ctor_get(v___x_1339_, 4);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1346_ = v___x_1339_;
v_isShared_1347_ = v_isSharedCheck_1373_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_diag_1344_);
lean_inc(v_postponed_1343_);
lean_inc(v_zetaDeltaFVarIds_1342_);
lean_inc(v_cache_1341_);
lean_inc(v_mctx_1340_);
lean_dec(v___x_1339_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1373_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_depth_1348_; lean_object* v_levelAssignDepth_1349_; lean_object* v_lmvarCounter_1350_; lean_object* v_mvarCounter_1351_; lean_object* v_lDecls_1352_; lean_object* v_decls_1353_; lean_object* v_userNames_1354_; lean_object* v_lAssignment_1355_; lean_object* v_eAssignment_1356_; lean_object* v_dAssignment_1357_; lean_object* v_instanceTypedMVars_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1372_; 
v_depth_1348_ = lean_ctor_get(v_mctx_1340_, 0);
v_levelAssignDepth_1349_ = lean_ctor_get(v_mctx_1340_, 1);
v_lmvarCounter_1350_ = lean_ctor_get(v_mctx_1340_, 2);
v_mvarCounter_1351_ = lean_ctor_get(v_mctx_1340_, 3);
v_lDecls_1352_ = lean_ctor_get(v_mctx_1340_, 4);
v_decls_1353_ = lean_ctor_get(v_mctx_1340_, 5);
v_userNames_1354_ = lean_ctor_get(v_mctx_1340_, 6);
v_lAssignment_1355_ = lean_ctor_get(v_mctx_1340_, 7);
v_eAssignment_1356_ = lean_ctor_get(v_mctx_1340_, 8);
v_dAssignment_1357_ = lean_ctor_get(v_mctx_1340_, 9);
v_instanceTypedMVars_1358_ = lean_ctor_get(v_mctx_1340_, 10);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_mctx_1340_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1360_ = v_mctx_1340_;
v_isShared_1361_ = v_isSharedCheck_1372_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_instanceTypedMVars_1358_);
lean_inc(v_dAssignment_1357_);
lean_inc(v_eAssignment_1356_);
lean_inc(v_lAssignment_1355_);
lean_inc(v_userNames_1354_);
lean_inc(v_decls_1353_);
lean_inc(v_lDecls_1352_);
lean_inc(v_mvarCounter_1351_);
lean_inc(v_lmvarCounter_1350_);
lean_inc(v_levelAssignDepth_1349_);
lean_inc(v_depth_1348_);
lean_dec(v_mctx_1340_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1372_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_eAssignment_1356_, v_mvarId_1335_, v_val_1336_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 8, v___x_1363_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_depth_1348_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_levelAssignDepth_1349_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_lmvarCounter_1350_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_mvarCounter_1351_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_lDecls_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 5, v_decls_1353_);
lean_ctor_set(v_reuseFailAlloc_1371_, 6, v_userNames_1354_);
lean_ctor_set(v_reuseFailAlloc_1371_, 7, v_lAssignment_1355_);
lean_ctor_set(v_reuseFailAlloc_1371_, 8, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1371_, 9, v_dAssignment_1357_);
lean_ctor_set(v_reuseFailAlloc_1371_, 10, v_instanceTypedMVars_1358_);
v___x_1365_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1365_);
v___x_1367_ = v___x_1346_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_cache_1341_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_zetaDeltaFVarIds_1342_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_postponed_1343_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_diag_1344_);
v___x_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_st_ref_put(v___y_1337_, v___x_1367_);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1362_);
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(lean_object* v_mvarId_1374_, lean_object* v_val_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1374_, v_val_1375_, v___y_1376_);
lean_dec(v___y_1376_);
return v_res_1378_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = l_Lean_NameSet_empty;
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__0));
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1381_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___closed__2));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles(lean_object* v_mvarId_1389_, lean_object* v_hs_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = lean_array_get_size(v_hs_1390_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_inc(v_mvarId_1389_);
v___x_1401_ = l_Lean_MVarId_getDecl(v_mvarId_1389_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1504_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1504_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1504_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; size_t v_sz_1408_; size_t v___x_1409_; lean_object* v___x_1410_; lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1502_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0));
v_sz_1408_ = lean_array_size(v_hs_1390_);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_hs_1390_, v_sz_1408_, v___x_1409_, v___x_1407_);
v_fst_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1410_, 1);
lean_dec(v_unused_1503_);
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1502_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fst_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1502_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
if (lean_obj_tag(v_fst_1411_) == 0)
{
lean_object* v___x_1416_; 
lean_del_object(v___x_1413_);
lean_dec(v_a_1402_);
lean_dec_ref(v_hs_1390_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_mvarId_1389_);
v___x_1416_ = v___x_1404_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_mvarId_1389_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
lean_object* v_val_1418_; 
v_val_1418_ = lean_ctor_get(v_fst_1411_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v_fst_1411_, 1);
if (lean_obj_tag(v_val_1418_) == 1)
{
lean_object* v_val_1419_; lean_object* v_userName_1420_; lean_object* v_lctx_1421_; lean_object* v_type_1422_; lean_object* v_localInstances_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_del_object(v___x_1404_);
v_val_1419_ = lean_ctor_get(v_val_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref_known(v_val_1418_, 1);
v_userName_1420_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_userName_1420_);
v_lctx_1421_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref_n(v_lctx_1421_, 2);
v_type_1422_ = lean_ctor_get(v_a_1402_, 2);
lean_inc_ref(v_type_1422_);
v_localInstances_1423_ = lean_ctor_get(v_a_1402_, 4);
lean_inc_ref(v_localInstances_1423_);
lean_dec(v_a_1402_);
v___x_1424_ = lean_local_ctx_num_indices(v_lctx_1421_);
v___x_1425_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__1, &l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1425_);
lean_ctor_set(v___x_1413_, 0, v_hs_1390_);
v___x_1427_ = v___x_1413_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_hs_1390_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_lctx_1421_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v___x_1424_, v___x_1424_, v_val_1419_, v___x_1399_, v___x_1428_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_val_1419_);
lean_dec(v___x_1424_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v_snd_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v_fst_1434_; lean_object* v_fst_1435_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v_snd_1431_ = lean_ctor_get(v_a_1430_, 1);
lean_inc(v_snd_1431_);
v_snd_1432_ = lean_ctor_get(v_snd_1431_, 1);
lean_inc(v_snd_1432_);
v_fst_1433_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_fst_1433_);
lean_dec(v_a_1430_);
v_fst_1434_ = lean_ctor_get(v_snd_1431_, 0);
lean_inc(v_fst_1434_);
lean_dec(v_snd_1431_);
v_fst_1435_ = lean_ctor_get(v_snd_1432_, 0);
lean_inc(v_fst_1435_);
lean_dec(v_snd_1432_);
v___x_1478_ = lean_array_get_size(v_fst_1434_);
lean_dec(v_fst_1434_);
v___x_1479_ = lean_nat_dec_eq(v___x_1478_, v___x_1399_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_renameInaccessibles___closed__3, &l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once, _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3);
v___x_1481_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(v___x_1480_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_dec_ref_known(v___x_1481_, 1);
v___y_1437_ = v_a_1391_;
v___y_1438_ = v_a_1392_;
v___y_1439_ = v_a_1393_;
v___y_1440_ = v_a_1394_;
v___y_1441_ = v_a_1395_;
v___y_1442_ = v_a_1396_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_fst_1435_);
lean_dec(v_fst_1433_);
lean_dec_ref(v_localInstances_1423_);
lean_dec_ref(v_type_1422_);
lean_dec(v_userName_1420_);
lean_dec(v_mvarId_1389_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
v___y_1437_ = v_a_1391_;
v___y_1438_ = v_a_1392_;
v___y_1439_ = v_a_1393_;
v___y_1440_ = v_a_1394_;
v___y_1441_ = v_a_1395_;
v___y_1442_ = v_a_1396_;
goto v___jp_1436_;
}
v___jp_1436_:
{
uint8_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = 2;
v___x_1444_ = l_Lean_Meta_mkFreshExprMVarAt(v_fst_1433_, v_localInstances_1423_, v_type_1422_, v___x_1443_, v_userName_1420_, v___x_1399_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; size_t v_sz_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lean_Expr_mvarId_x21(v_a_1445_);
v_sz_1447_ = lean_array_size(v_fst_1435_);
v___x_1448_ = lean_box_usize(v_sz_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1));
v___f_1450_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1450_, 0, v_fst_1435_);
lean_closure_set(v___f_1450_, 1, v___x_1448_);
lean_closure_set(v___f_1450_, 2, v___x_1449_);
lean_closure_set(v___f_1450_, 3, v___x_1406_);
lean_inc(v___x_1446_);
v___x_1451_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed), 10, 3);
lean_closure_set(v___x_1451_, 0, lean_box(0));
lean_closure_set(v___x_1451_, 1, v___x_1446_);
lean_closure_set(v___x_1451_, 2, v___f_1450_);
v___x_1452_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v___x_1451_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref_known(v___x_1452_, 1);
v___x_1453_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1389_, v_a_1445_, v___y_1440_);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v___x_1453_, 0);
lean_dec(v_unused_1461_);
v___x_1455_ = v___x_1453_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v___x_1453_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1446_);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1446_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v___x_1446_);
lean_dec(v_a_1445_);
lean_dec(v_mvarId_1389_);
v_a_1462_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1452_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1452_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_fst_1435_);
lean_dec(v_mvarId_1389_);
v_a_1470_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1444_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1444_);
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
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v_localInstances_1423_);
lean_dec_ref(v_type_1422_);
lean_dec(v_userName_1420_);
lean_dec(v_mvarId_1389_);
v_a_1490_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1429_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1429_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_val_1418_);
lean_del_object(v___x_1413_);
lean_dec(v_a_1402_);
lean_dec_ref(v_hs_1390_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_mvarId_1389_);
v___x_1500_ = v___x_1404_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_mvarId_1389_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v_hs_1390_);
lean_dec(v_mvarId_1389_);
v_a_1505_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1401_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1401_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec_ref(v_hs_1390_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_mvarId_1389_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_renameInaccessibles___boxed(lean_object* v_mvarId_1514_, lean_object* v_hs_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Elab_Tactic_renameInaccessibles(v_mvarId_1514_, v_hs_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(lean_object* v_00_u03b1_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(v_00_u03b1_1534_, v_x_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(lean_object* v_mvarId_1544_, lean_object* v_val_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_1544_, v_val_1545_, v___y_1549_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(lean_object* v_mvarId_1554_, lean_object* v_val_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(v_mvarId_1554_, v_val_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(lean_object* v_upperBound_1564_, lean_object* v___x_1565_, lean_object* v_val_1566_, lean_object* v_inst_1567_, lean_object* v_R_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_, lean_object* v_c_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_1564_, v___x_1565_, v_val_1566_, v_a_1569_, v_b_1570_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(lean_object* v_upperBound_1580_, lean_object* v___x_1581_, lean_object* v_val_1582_, lean_object* v_inst_1583_, lean_object* v_R_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v_c_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(v_upperBound_1580_, v___x_1581_, v_val_1582_, v_inst_1583_, v_R_1584_, v_a_1585_, v_b_1586_, v_c_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v_val_1582_);
lean_dec(v___x_1581_);
lean_dec(v_upperBound_1580_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_1599_, v___y_1600_, v___y_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(lean_object* v_00_u03b1_1628_, lean_object* v_x_1629_, lean_object* v_ctx_x3f_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_1629_, v_ctx_x3f_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_x_1640_, lean_object* v_ctx_x3f_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(v_00_u03b1_1639_, v_x_1640_, v_ctx_x3f_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(lean_object* v_00_u03b2_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_x_1651_, v_x_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, size_t v_x_1657_, size_t v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_1656_, v_x_1657_, v_x_1658_, v_x_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
size_t v_x_22737__boxed_1668_; size_t v_x_22738__boxed_1669_; lean_object* v_res_1670_; 
v_x_22737__boxed_1668_ = lean_unbox_usize(v_x_1664_);
lean_dec(v_x_1664_);
v_x_22738__boxed_1669_ = lean_unbox_usize(v_x_1665_);
lean_dec(v_x_1665_);
v_res_1670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(v_00_u03b2_1662_, v_x_1663_, v_x_22737__boxed_1668_, v_x_22738__boxed_1669_, v_x_1666_, v_x_1667_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(lean_object* v_ref_1671_, lean_object* v_msgData_1672_, uint8_t v_severity_1673_, uint8_t v_isSilent_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_1671_, v_msgData_1672_, v_severity_1673_, v_isSilent_1674_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(lean_object* v_ref_1683_, lean_object* v_msgData_1684_, lean_object* v_severity_1685_, lean_object* v_isSilent_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_severity_boxed_1694_; uint8_t v_isSilent_boxed_1695_; lean_object* v_res_1696_; 
v_severity_boxed_1694_ = lean_unbox(v_severity_1685_);
v_isSilent_boxed_1695_ = lean_unbox(v_isSilent_1686_);
v_res_1696_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_1683_, v_msgData_1684_, v_severity_boxed_1694_, v_isSilent_boxed_1695_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_ref_1683_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(lean_object* v_00_u03b2_1697_, lean_object* v_n_1698_, lean_object* v_k_1699_, lean_object* v_v_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v_n_1698_, v_k_1699_, v_v_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1702_, size_t v_depth_1703_, lean_object* v_keys_1704_, lean_object* v_vals_1705_, lean_object* v_heq_1706_, lean_object* v_i_1707_, lean_object* v_entries_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_1703_, v_keys_1704_, v_vals_1705_, v_i_1707_, v_entries_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1710_, lean_object* v_depth_1711_, lean_object* v_keys_1712_, lean_object* v_vals_1713_, lean_object* v_heq_1714_, lean_object* v_i_1715_, lean_object* v_entries_1716_){
_start:
{
size_t v_depth_boxed_1717_; lean_object* v_res_1718_; 
v_depth_boxed_1717_ = lean_unbox_usize(v_depth_1711_);
lean_dec(v_depth_1711_);
v_res_1718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(v_00_u03b2_1710_, v_depth_boxed_1717_, v_keys_1712_, v_vals_1713_, v_heq_1714_, v_i_1715_, v_entries_1716_);
lean_dec_ref(v_vals_1713_);
lean_dec_ref(v_keys_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_x_1720_, v_x_1721_, v_x_1722_, v_x_1723_);
return v___x_1724_;
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
