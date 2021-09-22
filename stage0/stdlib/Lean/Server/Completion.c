// Lean compiler output
// Module: Lean.Server.Completion
// Imports: Init Lean.Environment Lean.Parser.Term Lean.Data.Lsp.LanguageFeatures Lean.Meta.Tactic.Apply Lean.Meta.Match.MatcherInfo Lean.Server.InfoUtils Lean.Parser.Extension
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
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__38(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Elab_Info_occursBefore_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_isSmaller(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_State_itemsOther___default;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__30(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
extern lean_object* l_instInhabitedNat;
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3;
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__1;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__7;
lean_object* l_Lean_getOptionDecls(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedCompletionItem;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt;
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__1;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_aliasExtension;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2___boxed(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1;
extern lean_object* l_Lean_Parser_instInhabitedParserCategory;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Parser_isParserCategory___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1;
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_isCompletion(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f_choose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__5;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__5;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__6;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___at_Lean_getAliasState___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f_choose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__34(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static uint32_t l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1;
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAllParentStructures(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_State_itemsMain___default;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1;
lean_object* l_Lean_Name_getString_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__6;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_data_value_to_string(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__29(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1(lean_object*);
LEAN_EXPORT lean_object* lean_completion_add_to_black_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__2;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3;
static lean_object* l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
static lean_object* l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg(lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4;
static lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__7;
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__2;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6_(lean_object*);
static lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__1;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("blackListCompletion");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static uint32_t _init_l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__1;
x_3 = l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Server_Completion_completionBlackListExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Server_Completion_completionBlackListExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Server_Completion_completionBlackListExt___closed__3;
x_4 = l_Lean_Server_Completion_completionBlackListExt___closed__4;
x_5 = l_Lean_Server_Completion_completionBlackListExt___closed__5;
x_6 = l_Lean_Server_Completion_completionBlackListExt___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Completion_completionBlackListExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Completion_completionBlackListExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_completion_add_to_black_list(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Server_Completion_completionBlackListExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_isRecCore(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_isRecCore(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_is_matcher(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_is_matcher(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_41; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_41 = l_Lean_Name_isInternal(x_1);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_12 = x_42;
goto block_40;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_isPrivateName(x_1);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_box(0);
x_12 = x_47;
goto block_40;
}
}
block_40:
{
uint8_t x_13; 
lean_dec(x_12);
lean_inc(x_1);
lean_inc(x_11);
x_13 = lean_is_aux_recursor(x_11, x_1);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_noConfusionExt;
lean_inc(x_1);
lean_inc(x_11);
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_11, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
lean_inc(x_1);
x_16 = l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(x_1, x_2, x_3, x_4, x_5, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = l_Lean_Server_Completion_completionBlackListExt;
lean_inc(x_1);
x_23 = l_Lean_TagDeclarationExtension_isTagged(x_22, x_11, x_1);
if (x_23 == 0)
{
lean_object* x_24; 
lean_free_object(x_16);
x_24 = l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2(x_1, x_2, x_3, x_4, x_5, x_20);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_box(x_23);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lean_Server_Completion_completionBlackListExt;
lean_inc(x_1);
x_28 = l_Lean_TagDeclarationExtension_isTagged(x_27, x_11, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2(x_1, x_2, x_3, x_4, x_5, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_box(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_16, 0);
lean_dec(x_33);
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_1);
x_36 = lean_box(x_15);
if (lean_is_scalar(x_10)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_10;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = lean_box(x_13);
if (lean_is_scalar(x_10)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_10;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_11 = (uint8_t)((x_10 << 24) >> 61);
x_12 = 1;
x_13 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = 0;
lean_inc(x_2);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_15, x_16, x_7, x_2, x_3, x_4, x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_expr_instantiate1(x_9, x_18);
lean_dec(x_18);
lean_dec(x_9);
x_1 = x_20;
x_6 = x_19;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_isExprDefEq(x_2, x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = 1;
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_11, x_10, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 2;
lean_ctor_set_uint8(x_16, 5, x_22);
x_23 = l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__2(x_2, x_18, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get_uint8(x_16, 0);
x_38 = lean_ctor_get_uint8(x_16, 1);
x_39 = lean_ctor_get_uint8(x_16, 2);
x_40 = lean_ctor_get_uint8(x_16, 3);
x_41 = lean_ctor_get_uint8(x_16, 4);
x_42 = lean_ctor_get_uint8(x_16, 6);
x_43 = lean_ctor_get_uint8(x_16, 7);
x_44 = lean_ctor_get_uint8(x_16, 8);
x_45 = lean_ctor_get_uint8(x_16, 9);
x_46 = lean_ctor_get_uint8(x_16, 10);
x_47 = lean_ctor_get_uint8(x_16, 11);
x_48 = lean_ctor_get_uint8(x_16, 12);
lean_dec(x_16);
x_49 = 2;
x_50 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_50, 0, x_37);
lean_ctor_set_uint8(x_50, 1, x_38);
lean_ctor_set_uint8(x_50, 2, x_39);
lean_ctor_set_uint8(x_50, 3, x_40);
lean_ctor_set_uint8(x_50, 4, x_41);
lean_ctor_set_uint8(x_50, 5, x_49);
lean_ctor_set_uint8(x_50, 6, x_42);
lean_ctor_set_uint8(x_50, 7, x_43);
lean_ctor_set_uint8(x_50, 8, x_44);
lean_ctor_set_uint8(x_50, 9, x_45);
lean_ctor_set_uint8(x_50, 10, x_46);
lean_ctor_set_uint8(x_50, 11, x_47);
lean_ctor_set_uint8(x_50, 12, x_48);
lean_ctor_set(x_5, 0, x_50);
x_51 = l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__2(x_2, x_18, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_62 = lean_ctor_get(x_5, 1);
x_63 = lean_ctor_get(x_5, 2);
x_64 = lean_ctor_get(x_5, 3);
x_65 = lean_ctor_get(x_5, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_5);
x_66 = lean_ctor_get_uint8(x_16, 0);
x_67 = lean_ctor_get_uint8(x_16, 1);
x_68 = lean_ctor_get_uint8(x_16, 2);
x_69 = lean_ctor_get_uint8(x_16, 3);
x_70 = lean_ctor_get_uint8(x_16, 4);
x_71 = lean_ctor_get_uint8(x_16, 6);
x_72 = lean_ctor_get_uint8(x_16, 7);
x_73 = lean_ctor_get_uint8(x_16, 8);
x_74 = lean_ctor_get_uint8(x_16, 9);
x_75 = lean_ctor_get_uint8(x_16, 10);
x_76 = lean_ctor_get_uint8(x_16, 11);
x_77 = lean_ctor_get_uint8(x_16, 12);
if (lean_is_exclusive(x_16)) {
 x_78 = x_16;
} else {
 lean_dec_ref(x_16);
 x_78 = lean_box(0);
}
x_79 = 2;
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 0, 13);
} else {
 x_80 = x_78;
}
lean_ctor_set_uint8(x_80, 0, x_66);
lean_ctor_set_uint8(x_80, 1, x_67);
lean_ctor_set_uint8(x_80, 2, x_68);
lean_ctor_set_uint8(x_80, 3, x_69);
lean_ctor_set_uint8(x_80, 4, x_70);
lean_ctor_set_uint8(x_80, 5, x_79);
lean_ctor_set_uint8(x_80, 6, x_71);
lean_ctor_set_uint8(x_80, 7, x_72);
lean_ctor_set_uint8(x_80, 8, x_73);
lean_ctor_set_uint8(x_80, 9, x_74);
lean_ctor_set_uint8(x_80, 10, x_75);
lean_ctor_set_uint8(x_80, 11, x_76);
lean_ctor_set_uint8(x_80, 12, x_77);
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_62);
lean_ctor_set(x_81, 2, x_63);
lean_ctor_set(x_81, 3, x_64);
lean_ctor_set(x_81, 4, x_65);
x_82 = l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__2(x_2, x_18, x_81, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_13);
if (x_93 == 0)
{
return x_13;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_13, 0);
x_95 = lean_ctor_get(x_13, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_13);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Meta_getExpectedNumArgsAux(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_18 = l_Lean_Meta_getExpectedNumArgs(x_11, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_sub(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1(x_1, x_11, x_21, x_22, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = lean_box(x_33);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
lean_dec(x_40);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_box(0);
x_50 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1(x_1, x_11, x_48, x_49, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
lean_dec(x_59);
x_60 = 0;
x_61 = lean_box(x_60);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_61);
return x_50;
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_dec(x_50);
x_63 = 0;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_12);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_12, 0);
lean_dec(x_67);
x_68 = 0;
x_69 = lean_box(x_68);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_69);
return x_12;
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_dec(x_12);
x_71 = 0;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Lsp_instInhabitedCompletionItem;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_dec_lt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_46 = l_Lean_Lsp_instInhabitedCompletionItem;
x_47 = lean_array_get(x_46, x_1, x_16);
x_48 = lean_array_get(x_46, x_1, x_2);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_string_dec_lt(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
x_17 = x_1;
goto block_45;
}
else
{
lean_object* x_52; 
x_52 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_52;
goto block_45;
}
block_45:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l_Lean_Lsp_instInhabitedCompletionItem;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_string_dec_lt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get(x_18, x_17, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_string_dec_lt(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_28 = l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_27, x_3, x_19, x_17, x_2, x_2);
x_4 = x_28;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
x_29 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_30 = lean_array_get(x_18, x_29, x_3);
x_31 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_32 = l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_31, x_3, x_30, x_29, x_2, x_2);
x_4 = x_32;
goto block_12;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_19);
x_33 = lean_array_swap(x_17, x_2, x_3);
x_34 = lean_array_get(x_18, x_33, x_16);
x_35 = lean_array_get(x_18, x_33, x_3);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_string_dec_lt(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_16);
x_39 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_40 = l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_39, x_3, x_35, x_33, x_2, x_2);
x_4 = x_40;
goto block_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_41 = lean_array_swap(x_33, x_16, x_3);
lean_dec(x_16);
x_42 = lean_array_get(x_18, x_41, x_3);
x_43 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_44 = l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_43, x_3, x_42, x_41, x_2, x_2);
x_4 = x_44;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(x_1, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_ppExpr(x_9, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Name_getString_x21(x_1);
x_15 = l_Std_Format_defWidth;
x_16 = lean_format_pretty(x_13, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = l_Lean_Name_getString_x21(x_1);
x_23 = l_Std_Format_defWidth;
x_24 = lean_format_pretty(x_20, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_Completion_State_itemsMain___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_State_itemsOther___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_2);
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable(x_2, x_3, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_get(x_8, x_16);
lean_dec(x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_push(x_23, x_11);
lean_ctor_set(x_20, 1, x_24);
x_25 = lean_st_ref_set(x_4, x_20, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_array_push(x_33, x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_st_ref_set(x_4, x_35, x_21);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_st_ref_get(x_8, x_41);
lean_dec(x_8);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_st_ref_take(x_4, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_array_push(x_48, x_11);
lean_ctor_set(x_45, 0, x_49);
x_50 = lean_st_ref_set(x_4, x_45, x_46);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_array_push(x_57, x_11);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_st_ref_set(x_4, x_60, x_46);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_10);
if (x_66 == 0)
{
return x_10;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_10, 0);
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_10);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_environment_find(x_14, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_ConstantInfo_type(x_17);
lean_dec(x_17);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_environment_find(x_22, x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_11);
x_13 = lean_apply_6(x_2, x_11, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_11, x_17);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_31);
x_33 = l_Array_append___rarg(x_30, x_32);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
lean_ctor_set(x_14, 0, x_35);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_38);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_40);
x_42 = l_Array_append___rarg(x_39, x_41);
x_43 = 1;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
lean_ctor_set(x_14, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_14);
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_48 = x_18;
} else {
 lean_dec_ref(x_18);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_49);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_51);
x_53 = l_Array_append___rarg(x_50, x_52);
x_54 = 1;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_48)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_48;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
return x_13;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1;
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___lambda__1), 7, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_String_isPrefixOf(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_9);
x_14 = l_Lean_mkPrivateName(x_13, x_9);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_9);
x_19 = l_Lean_mkPrivateName(x_18, x_9);
x_20 = lean_name_eq(x_19, x_1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lean_Name_isPrefixOf(x_1, x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_38; 
x_17 = lean_box(0);
x_18 = l_Lean_Name_replacePrefix(x_11, x_1, x_17);
x_38 = l_Lean_Name_isPrefixOf(x_2, x_18);
if (x_38 == 0)
{
if (x_3 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_19 = x_39;
goto block_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_18);
lean_dec(x_13);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_19 = x_42;
goto block_37;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_13);
x_43 = l_Lean_Name_replacePrefix(x_18, x_2, x_17);
x_44 = l_Lean_Name_isAtomic(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = l_Lean_Name_isAnonymous(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_12);
return x_51;
}
}
}
}
block_37:
{
lean_dec(x_19);
if (lean_obj_tag(x_2) == 1)
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_name_eq(x_20, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
x_25 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_13;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_String_isPrefixOf(x_21, x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_28 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_13;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_name_mk_string(x_17, x_23);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (lean_is_scalar(x_13)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_13;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_12);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
x_33 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_12);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_18);
x_35 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_13;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_11);
lean_dec(x_19);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_2 = x_9;
x_8 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_2 = x_9;
x_8 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_32 = x_10;
} else {
 lean_dec_ref(x_10);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_27);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
x_52 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_4, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_inc(x_4);
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_50, x_3, x_1, x_4, x_10, x_11, x_12, x_13, x_14);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1;
x_36 = x_56;
x_37 = x_55;
goto block_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
lean_dec(x_54);
x_59 = l_Lean_ConstantInfo_type(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_60 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_58, x_59, x_2, x_9, x_10, x_11, x_12, x_13, x_57);
lean_dec(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(0);
x_36 = x_63;
x_37 = x_62;
goto block_49;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4;
x_36 = x_65;
x_37 = x_64;
goto block_49;
}
}
else
{
uint8_t x_66; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_inc(x_6);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_6);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_19 = x_71;
x_20 = x_14;
goto block_35;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_inc(x_6);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_6);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_19 = x_73;
x_20 = x_14;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; 
lean_free_object(x_19);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_7 = x_18;
x_8 = x_27;
x_14 = x_20;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_7 = x_18;
x_8 = x_33;
x_14 = x_20;
goto _start;
}
}
}
}
block_49:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_19 = x_38;
x_20 = x_37;
goto block_35;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_6);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_36, 0, x_42);
x_19 = x_36;
x_20 = x_37;
goto block_35;
}
else
{
lean_object* x_43; 
lean_free_object(x_36);
x_43 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3;
x_19 = x_43;
x_20 = x_37;
goto block_35;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_6);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_6);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_19 = x_47;
x_20 = x_37;
goto block_35;
}
else
{
lean_object* x_48; 
x_48 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3;
x_19 = x_48;
x_20 = x_37;
goto block_35;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_8(x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_2 = x_13;
x_8 = x_22;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_8(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = x_3 + x_44;
x_3 = x_45;
x_5 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
size_t x_51; size_t x_52; 
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_5, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_2, x_5);
x_18 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = lean_apply_9(x_1, x_6, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_30;
x_6 = x_28;
x_12 = x_27;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_24, x_22, x_23, lean_box(0), x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_8(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = x_3 + x_44;
x_3 = x_45;
x_5 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
size_t x_51; size_t x_52; 
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_24, x_22, x_23, lean_box(0), x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Std_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__3(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = 1;
x_25 = x_3 + x_24;
x_3 = x_25;
x_5 = x_23;
x_11 = x_22;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_8(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = x_3 + x_44;
x_3 = x_45;
x_5 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
size_t x_51; size_t x_52; 
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_24, x_22, x_23, lean_box(0), x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15(x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_instBEqName;
x_16 = l_Lean_instHashableName;
x_17 = lean_box(0);
x_18 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(x_2, x_15, x_16, x_14, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_11, x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Name_instBEqName;
x_22 = l_Lean_instHashableName;
x_23 = lean_box(0);
x_24 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(x_2, x_21, x_22, x_20, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_27 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13(x_2, x_10, x_25, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Name_instBEqName;
x_39 = l_Lean_instHashableName;
x_40 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15(x_2, x_38, x_39, x_37, x_27, x_3, x_4, x_5, x_6, x_7, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; 
lean_dec(x_13);
x_23 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_15 = x_23;
x_16 = x_10;
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
lean_inc(x_25);
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_25, x_6, x_7, x_8, x_9, x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_24);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_24);
x_31 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_15 = x_31;
x_16 = x_29;
goto block_22;
}
else
{
lean_object* x_32; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_24, x_25, x_1, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_15 = x_35;
x_16 = x_34;
goto block_22;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_15 = x_37;
x_16 = x_36;
goto block_22;
}
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
lean_dec(x_24);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_15 = x_43;
x_16 = x_42;
goto block_22;
}
}
block_22:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_3 = x_14;
x_4 = x_20;
x_10 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_12);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_12, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_2, x_12, x_1, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_3 = x_13;
x_9 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_12);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_dec(x_14);
x_3 = x_13;
x_9 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_8(x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_2 = x_13;
x_8 = x_22;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_8(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = x_3 + x_44;
x_3 = x_45;
x_5 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
size_t x_51; size_t x_52; 
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_24, x_22, x_23, lean_box(0), x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__29(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_8(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = x_3 + x_44;
x_3 = x_45;
x_5 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
size_t x_51; size_t x_52; 
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__29(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_24, x_22, x_23, lean_box(0), x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__30(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Std_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__21(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = 1;
x_25 = x_3 + x_24;
x_3 = x_25;
x_5 = x_23;
x_11 = x_22;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__34(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_8(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__33(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = x_3 + x_44;
x_3 = x_45;
x_5 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
default: 
{
size_t x_51; size_t x_52; 
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__34(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_24, x_22, x_23, lean_box(0), x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__33(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__32(x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Name_instBEqName;
x_16 = l_Lean_instHashableName;
x_17 = lean_box(0);
x_18 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(x_2, x_15, x_16, x_14, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_11, x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Name_instBEqName;
x_22 = l_Lean_instHashableName;
x_23 = lean_box(0);
x_24 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(x_2, x_21, x_22, x_20, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_27 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__30(x_2, x_10, x_25, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Name_instBEqName;
x_39 = l_Lean_instHashableName;
x_40 = l_Std_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__32(x_2, x_38, x_39, x_37, x_27, x_3, x_4, x_5, x_6, x_7, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_7 < x_6;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_40; 
x_18 = lean_array_uget(x_5, x_7);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_8, 1);
x_42 = lean_ctor_get(x_8, 0);
lean_dec(x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36(x_1, x_2, x_3, x_18, x_41, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_8);
lean_dec(x_41);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_19 = x_46;
x_20 = x_45;
goto block_39;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_44, 0);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
lean_ctor_set(x_8, 0, x_44);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_8);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_19 = x_51;
x_20 = x_49;
goto block_39;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_41);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_54);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_48, 0, x_8);
x_19 = x_44;
x_20 = x_52;
goto block_39;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_55);
lean_ctor_set(x_8, 0, x_4);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_8);
lean_ctor_set(x_44, 0, x_56);
x_19 = x_44;
x_20 = x_52;
goto block_39;
}
}
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
lean_dec(x_44);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_8, 0, x_59);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_8);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_19 = x_61;
x_20 = x_58;
goto block_39;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_63);
lean_ctor_set(x_8, 0, x_4);
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_8);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_19 = x_66;
x_20 = x_62;
goto block_39;
}
}
}
}
else
{
uint8_t x_67; 
lean_free_object(x_8);
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
return x_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_43, 0);
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_43);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_dec(x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_71);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_72 = l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36(x_1, x_2, x_3, x_18, x_71, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_box(0);
x_19 = x_75;
x_20 = x_74;
goto block_39;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_71);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_19 = x_82;
x_20 = x_78;
goto block_39;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_71);
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
lean_inc(x_4);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_4);
lean_ctor_set(x_86, 1, x_84);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
x_19 = x_88;
x_20 = x_83;
goto block_39;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_71);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_91 = x_72;
} else {
 lean_dec_ref(x_72);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
block_39:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; 
lean_free_object(x_19);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = 1;
x_29 = x_7 + x_28;
x_7 = x_29;
x_8 = x_27;
x_14 = x_20;
goto _start;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
return x_34;
}
else
{
lean_object* x_35; size_t x_36; size_t x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 1;
x_37 = x_7 + x_36;
x_7 = x_37;
x_8 = x_35;
x_14 = x_20;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_17 = lean_array_uget(x_4, x_6);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_40 = x_7;
} else {
 lean_dec_ref(x_7);
 x_40 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_inc(x_39);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_39);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_41 = x_67;
x_42 = x_13;
goto block_65;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
lean_dec(x_17);
x_69 = l_Lean_LocalDecl_userName(x_68);
x_70 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
lean_dec(x_68);
x_71 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_41 = x_71;
x_42 = x_13;
goto block_65;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_LocalDecl_type(x_68);
lean_dec(x_68);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_73 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_69, x_72, x_1, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_3);
x_41 = x_3;
x_42 = x_75;
goto block_65;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_41 = x_77;
x_42 = x_76;
goto block_65;
}
}
else
{
uint8_t x_78; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
block_38:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_18, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; 
lean_free_object(x_18);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = 1;
x_28 = x_6 + x_27;
x_6 = x_28;
x_7 = x_26;
x_13 = x_19;
goto _start;
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_19);
return x_33;
}
else
{
lean_object* x_34; size_t x_35; size_t x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = 1;
x_36 = x_6 + x_35;
x_6 = x_36;
x_7 = x_34;
x_13 = x_19;
goto _start;
}
}
}
}
block_65:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_39);
x_43 = lean_box(0);
x_18 = x_43;
x_19 = x_42;
goto block_38;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_39);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_18 = x_48;
x_19 = x_42;
goto block_38;
}
else
{
uint8_t x_49; 
lean_dec(x_39);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_3);
if (lean_is_scalar(x_40)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_40;
}
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_45, 0, x_51);
x_18 = x_41;
x_19 = x_42;
goto block_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
lean_inc(x_3);
if (lean_is_scalar(x_40)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_40;
}
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_41, 0, x_54);
x_18 = x_41;
x_19 = x_42;
goto block_38;
}
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
lean_dec(x_41);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_40)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_40;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_39);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_18 = x_59;
x_19 = x_42;
goto block_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
lean_inc(x_3);
if (lean_is_scalar(x_40)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_40;
}
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_60);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_18 = x_64;
x_19 = x_42;
goto block_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__37(x_1, x_2, x_3, x_13, x_12, x_16, x_17, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1(x_27, x_28, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_18, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_18, 0, x_34);
return x_18;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_37 = x_25;
} else {
 lean_dec_ref(x_25);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
lean_dec(x_3);
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_get_size(x_44);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_50 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__38(x_1, x_2, x_45, x_44, x_48, x_49, x_46, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_44);
lean_dec(x_2);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
lean_ctor_set(x_50, 0, x_45);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_box(0);
x_61 = l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1(x_59, x_60, x_6, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_50, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_50, 0, x_66);
return x_50;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_69 = x_57;
} else {
 lean_dec_ref(x_57);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_50);
if (x_72 == 0)
{
return x_50;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_50, 0);
x_74 = lean_ctor_get(x_50, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_50);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_29 = x_7;
} else {
 lean_dec_ref(x_7);
 x_29 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_28);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_30 = x_49;
x_31 = x_13;
goto block_47;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_28);
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
lean_dec(x_17);
x_51 = l_Lean_LocalDecl_userName(x_50);
x_52 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_51);
lean_dec(x_50);
x_53 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_30 = x_53;
x_31 = x_13;
goto block_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_LocalDecl_type(x_50);
lean_dec(x_50);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_55 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_51, x_54, x_1, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_box(0);
x_30 = x_58;
x_31 = x_57;
goto block_47;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2;
x_30 = x_60;
x_31 = x_59;
goto block_47;
}
}
else
{
uint8_t x_61; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_55, 0);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_55);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_27:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 1;
x_25 = x_6 + x_24;
x_6 = x_25;
x_7 = x_23;
x_13 = x_19;
goto _start;
}
}
block_47:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
x_32 = lean_box(0);
x_18 = x_32;
x_19 = x_31;
goto block_27;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_3);
if (lean_is_scalar(x_29)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_29;
}
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_34, 0, x_37);
x_18 = x_30;
x_19 = x_31;
goto block_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_3);
if (lean_is_scalar(x_29)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_29;
}
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_30, 0, x_40);
x_18 = x_30;
x_19 = x_31;
goto block_27;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
lean_inc(x_3);
if (lean_is_scalar(x_29)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_29;
}
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_18 = x_46;
x_19 = x_31;
goto block_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36(x_1, x_2, x_4, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_13, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
lean_ctor_set(x_13, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_13);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_array_get_size(x_30);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39(x_1, x_2, x_31, x_30, x_34, x_35, x_32, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_30);
lean_dec(x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
lean_ctor_set(x_36, 0, x_31);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_box(0);
x_47 = l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1(x_45, x_46, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_36, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_ctor_set(x_36, 0, x_43);
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_36, 0, x_52);
return x_36;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_55 = x_43;
} else {
 lean_dec_ref(x_43);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_36);
if (x_58 == 0)
{
return x_36;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_13, 0);
lean_inc(x_62);
lean_dec(x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_64 = x_12;
} else {
 lean_dec_ref(x_12);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_dec(x_12);
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
lean_dec(x_62);
x_70 = lean_ctor_get(x_3, 1);
lean_inc(x_70);
lean_dec(x_3);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_array_get_size(x_70);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39(x_1, x_2, x_71, x_70, x_74, x_75, x_72, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_70);
lean_dec(x_2);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_box(0);
x_86 = l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1(x_84, x_85, x_5, x_6, x_7, x_8, x_9, x_83);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_81);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_ctor_get(x_76, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_95 = x_76;
} else {
 lean_dec_ref(x_76);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_12);
if (x_97 == 0)
{
return x_12;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_12, 0);
x_99 = lean_ctor_get(x_12, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_12);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_6, x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_ConstantInfo_type(x_4);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_22, x_23, x_5, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_25);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4;
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
x_36 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_box(0);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1;
x_17 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_16, x_14, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 0);
lean_dec(x_26);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_17, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_17, 0, x_35);
return x_17;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_38 = x_24;
} else {
 lean_dec_ref(x_24);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(x_2, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(x_1, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_16, 0, x_31);
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_33 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_5);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_5, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = lean_box(x_2);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed), 12, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_6);
lean_closure_set(x_19, 4, x_3);
x_31 = lean_box(0);
lean_inc(x_5);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_31, x_1, x_2, x_5, x_8, x_9, x_10, x_11, x_16);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1;
x_20 = x_35;
x_21 = x_34;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lean_ConstantInfo_type(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_37, x_38, x_3, x_7, x_8, x_9, x_10, x_11, x_36);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_20 = x_42;
x_21 = x_41;
goto block_30;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4;
x_20 = x_44;
x_21 = x_43;
goto block_30;
}
}
else
{
uint8_t x_45; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_30:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(x_4, x_19, x_2, x_3, x_1, x_5, x_6, x_26, x_7, x_8, x_9, x_10, x_11, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
if (lean_is_scalar(x_17)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_17;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_13, 0);
lean_dec(x_50);
x_51 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_13, 0, x_51);
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_dec(x_13);
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_1, x_3);
lean_dec(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_box(x_2);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed), 12, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(x_16, x_18, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_4, 5);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_30 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(x_3, x_1, x_28, x_29, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_aliasExtension;
x_40 = l_Lean_SimplePersistentEnvExtension_getState___at_Lean_getAliasState___spec__1(x_39, x_15);
lean_dec(x_15);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5), 10, 2);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_3);
x_42 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(x_40, x_41, x_6, x_7, x_8, x_9, x_10, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_erase_macro_scopes(x_2);
x_12 = l_Lean_Name_isAtomic(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(x_11, x_3, x_4, x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
lean_inc(x_4);
x_18 = l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35(x_4, x_11, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(x_11, x_3, x_4, x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__29(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__30(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__34(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__37(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__38(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__36___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__39(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__35___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(x_4);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___boxed), 10, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_2, x_8, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
lean_dec(x_14);
lean_inc(x_7);
x_16 = l_Lean_Meta_getLocalDecl(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_LocalDecl_type(x_18);
lean_dec(x_18);
x_21 = l_Lean_Expr_consumeMData(x_20);
lean_dec(x_20);
x_22 = l_Lean_Expr_getAppFn(x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_isConstOf(x_22, x_1);
lean_dec(x_22);
if (x_23 == 0)
{
size_t x_24; size_t x_25; 
lean_free_object(x_16);
x_24 = 1;
x_25 = x_5 + x_24;
lean_inc(x_2);
{
size_t _tmp_4 = x_25;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_19;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_2);
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = l_Lean_LocalDecl_type(x_28);
lean_dec(x_28);
x_31 = l_Lean_Expr_consumeMData(x_30);
lean_dec(x_30);
x_32 = l_Lean_Expr_getAppFn(x_31);
lean_dec(x_31);
x_33 = l_Lean_Expr_isConstOf(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
size_t x_34; size_t x_35; 
x_34 = 1;
x_35 = x_5 + x_34;
lean_inc(x_2);
{
size_t _tmp_4 = x_35;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_29;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_2);
x_37 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1;
lean_inc(x_4);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(x_1, x_12, x_2, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1;
x_18 = lean_box(0);
x_19 = lean_apply_6(x_17, x_18, x_4, x_5, x_6, x_7, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_ConstantInfo_type(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 < x_2;
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_st_ref_get(x_9, x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_17, x_13, x_19);
x_21 = lean_st_ref_set(x_5, x_20, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = x_3 + x_23;
x_3 = x_24;
x_4 = x_19;
x_10 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_7(x_9, x_11, x_3, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_apply_7(x_9, x_15, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_9);
x_16 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_13, x_9, x_15);
x_17 = lean_st_ref_set(x_2, x_16, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
x_23 = l_Lean_isStructure(x_22, x_9);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_9);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_st_ref_get(x_6, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_getAllParentStructures(x_28, x_9);
x_30 = lean_array_get_size(x_29);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_29, x_31, x_32, x_15, x_2, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_NameSet_empty;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_11);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_1, x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_5, x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName(x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Name_getPrefix(x_13);
lean_dec(x_13);
x_16 = l_Lean_NameSet_contains(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_11);
x_18 = l_Lean_ConstantInfo_name(x_4);
lean_inc(x_18);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_18, x_6, x_7, x_8, x_9, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(x_15, x_4, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Name_getString_x21(x_18);
lean_dec(x_18);
x_34 = lean_box(0);
x_35 = lean_name_mk_string(x_34, x_33);
x_36 = l_Lean_ConstantInfo_type(x_4);
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_35, x_36, x_2, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_19, 0);
lean_dec(x_43);
x_44 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_46 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_11);
x_50 = l_Lean_Name_getPrefix(x_48);
lean_dec(x_48);
x_51 = l_Lean_NameSet_contains(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_52 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_Lean_ConstantInfo_name(x_4);
lean_inc(x_54);
x_55 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_54, x_6, x_7, x_8, x_9, x_49);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_59 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(x_50, x_4, x_6, x_7, x_8, x_9, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = l_Lean_Name_getString_x21(x_54);
lean_dec(x_54);
x_68 = lean_box(0);
x_69 = lean_name_mk_string(x_68, x_67);
x_70 = l_Lean_ConstantInfo_type(x_4);
x_71 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_69, x_70, x_2, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_74 = x_59;
} else {
 lean_dec_ref(x_59);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = lean_ctor_get(x_55, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_77 = x_55;
} else {
 lean_dec_ref(x_55);
 x_77 = lean_box(0);
}
x_78 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1;
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("completion");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__6;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Syntax_isIdent(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_12);
x_14 = l_Lean_Syntax_getKind(x_12);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__8;
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_12, x_19);
lean_dec(x_12);
x_21 = l_Lean_Syntax_isIdent(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Lean_Syntax_getId(x_20);
lean_dec(x_20);
x_25 = 1;
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(x_2, x_24, x_25, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_28 = 0;
x_29 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(x_2, x_27, x_28, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_st_ref_get(x_9, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1___boxed), 10, 2);
lean_closure_set(x_35, 0, x_4);
lean_closure_set(x_35, 1, x_3);
x_36 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(x_34, x_35, x_5, x_6, x_7, x_8, x_9, x_32);
return x_36;
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_instantiateMVars(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_dec(x_29);
x_30 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_8, 0);
lean_dec(x_35);
x_36 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_36);
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
x_38 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_7(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2), 10, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___boxed), 7, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__4), 8, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___rarg), 8, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_5, x_10, x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("), ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; uint8_t x_72; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_72 = l_Lean_Name_isPrefixOf(x_1, x_13);
if (x_72 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_ctor_get(x_1, 1);
x_75 = lean_ctor_get(x_13, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
x_77 = lean_name_eq(x_73, x_75);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_19);
x_21 = x_78;
x_22 = x_18;
goto block_25;
}
else
{
uint8_t x_79; 
x_79 = l_String_isPrefixOf(x_74, x_76);
lean_dec(x_76);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_19);
x_21 = x_80;
x_22 = x_18;
goto block_25;
}
else
{
lean_object* x_81; 
x_81 = lean_box(0);
x_26 = x_81;
goto block_71;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_19);
x_21 = x_82;
x_22 = x_18;
goto block_25;
}
}
else
{
lean_object* x_83; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_19);
x_21 = x_83;
x_22 = x_18;
goto block_25;
}
}
else
{
lean_object* x_84; 
x_84 = lean_box(0);
x_26 = x_84;
goto block_71;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_3 = x_15;
x_4 = x_23;
x_9 = x_22;
goto _start;
}
block_71:
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
x_27 = 1;
lean_inc(x_13);
x_28 = l_Lean_Name_toString(x_13, x_27);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = l_Lean_KVMap_findCore(x_2, x_13);
lean_dec(x_13);
x_31 = lean_ctor_get(x_14, 2);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_data_value_to_string(x_29);
x_34 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_31);
lean_dec(x_31);
x_39 = l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_32);
x_43 = lean_array_push(x_19, x_42);
if (lean_is_scalar(x_20)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_20;
}
lean_ctor_set(x_44, 0, x_43);
x_21 = x_44;
x_22 = x_18;
goto block_25;
}
else
{
uint8_t x_45; 
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_data_value_to_string(x_46);
x_48 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_31);
lean_dec(x_31);
x_53 = l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2;
x_54 = lean_string_append(x_52, x_53);
lean_ctor_set(x_30, 0, x_54);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_28);
lean_ctor_set(x_55, 1, x_30);
lean_ctor_set(x_55, 2, x_32);
x_56 = lean_array_push(x_19, x_55);
if (lean_is_scalar(x_20)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_20;
}
lean_ctor_set(x_57, 0, x_56);
x_21 = x_57;
x_22 = x_18;
goto block_25;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
lean_dec(x_30);
x_59 = lean_data_value_to_string(x_58);
x_60 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_31);
lean_dec(x_31);
x_65 = l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_28);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_32);
x_69 = lean_array_push(x_19, x_68);
if (lean_is_scalar(x_20)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_20;
}
lean_ctor_set(x_70, 0, x_69);
x_21 = x_70;
x_22 = x_18;
goto block_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_getOptionDecls(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_4, 0);
x_13 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_14 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(x_1, x_12, x_10, x_13, x_2, x_3, x_4, x_5, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_17);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5;
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
x_9 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_8, x_7, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_1, x_3);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_4, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_array_push(x_6, x_10);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Option.BasicAux");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option.get!");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value is none");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Parser_parserExtension;
x_11 = l_Lean_ScopedEnvExtension_getState___at_Lean_Parser_isParserCategory___spec__1(x_10, x_9);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Name_instBEqName;
x_14 = l_Lean_instHashableName;
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2;
x_16 = l_Std_PersistentHashMap_find_x3f___rarg(x_13, x_14, x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_17 = l_Lean_Parser_instInhabitedParserCategory;
x_18 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
x_19 = lean_panic_fn(x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_23 = l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_22, x_21);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_23);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_33 = l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_32, x_31);
x_34 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_33);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
lean_ctor_set(x_16, 0, x_36);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_41 = l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_40, x_39);
x_42 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_41);
x_43 = 1;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_6, 0, x_45);
return x_6;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Parser_parserExtension;
x_50 = l_Lean_ScopedEnvExtension_getState___at_Lean_Parser_isParserCategory___spec__1(x_49, x_48);
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_Name_instBEqName;
x_53 = l_Lean_instHashableName;
x_54 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2;
x_55 = l_Std_PersistentHashMap_find_x3f___rarg(x_52, x_53, x_51, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = l_Lean_Parser_instInhabitedParserCategory;
x_57 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
x_58 = lean_panic_fn(x_56, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_62 = l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_61, x_60);
x_63 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_62);
x_64 = 1;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_47);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1;
x_73 = l_Std_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_72, x_71);
x_74 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_73);
x_75 = 1;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
if (lean_is_scalar(x_69)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_69;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_47);
return x_78;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
x_4 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1;
x_5 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f_choose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Elab_Info_isCompletion(x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Info_occursBefore_x3f(x_5, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_66; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_66 = l_Lean_Elab_Info_tailPos_x3f(x_5);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = l_instInhabitedNat;
x_68 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
x_69 = lean_panic_fn(x_67, x_68);
x_70 = l_Lean_FileMap_toPosition(x_2, x_69);
lean_dec(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_nat_dec_eq(x_71, x_3);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_73; 
x_73 = lean_box(0);
x_11 = x_73;
goto block_65;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l_Lean_FileMap_toPosition(x_2, x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_nat_dec_eq(x_76, x_3);
lean_dec(x_76);
if (x_77 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_78; 
x_78 = lean_box(0);
x_11 = x_78;
goto block_65;
}
}
block_65:
{
lean_dec(x_11);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
if (lean_is_scalar(x_10)) {
 x_13 = lean_alloc_ctor(1, 1, 0);
} else {
 x_13 = x_10;
}
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_Elab_Info_occursBefore_x3f(x_16, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_instInhabitedNat;
x_20 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
x_21 = lean_panic_fn(x_19, x_20);
x_22 = lean_nat_dec_lt(x_9, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_9, x_21);
lean_dec(x_21);
lean_dec(x_9);
if (x_23 == 0)
{
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_24; 
x_24 = l_Lean_Elab_Info_isSmaller(x_5, x_16);
lean_dec(x_16);
if (x_24 == 0)
{
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
return x_6;
}
else
{
lean_object* x_27; 
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_14);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_6, 0);
lean_dec(x_29);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
return x_6;
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_14);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_nat_dec_lt(x_9, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_9, x_32);
lean_dec(x_32);
lean_dec(x_9);
if (x_34 == 0)
{
lean_free_object(x_18);
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_Elab_Info_isSmaller(x_5, x_16);
lean_dec(x_16);
if (x_35 == 0)
{
lean_free_object(x_18);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_nat_dec_lt(x_9, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_nat_dec_eq(x_9, x_36);
lean_dec(x_36);
lean_dec(x_9);
if (x_38 == 0)
{
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_39; 
x_39 = l_Lean_Elab_Info_isSmaller(x_5, x_16);
lean_dec(x_16);
if (x_39 == 0)
{
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_40; 
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_14);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_14);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_dec(x_14);
x_43 = l_Lean_Elab_Info_occursBefore_x3f(x_42, x_1);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_instInhabitedNat;
x_45 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
x_46 = lean_panic_fn(x_44, x_45);
x_47 = lean_nat_dec_lt(x_9, x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = lean_nat_dec_eq(x_9, x_46);
lean_dec(x_46);
lean_dec(x_9);
if (x_48 == 0)
{
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_49; 
x_49 = l_Lean_Elab_Info_isSmaller(x_5, x_42);
lean_dec(x_42);
if (x_49 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_50 = x_6;
} else {
 lean_dec_ref(x_6);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_5);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_53 = x_6;
} else {
 lean_dec_ref(x_6);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_5);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
x_58 = lean_nat_dec_lt(x_9, x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_nat_dec_eq(x_9, x_56);
lean_dec(x_56);
lean_dec(x_9);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_60; 
x_60 = l_Lean_Elab_Info_isSmaller(x_5, x_42);
lean_dec(x_42);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_5);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_56);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_6);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_5);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f_choose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Completion_find_x3f_choose(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_FileMap_toPosition(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_choose___boxed), 6, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Elab_InfoTree_foldInfo___rarg(x_7, x_8, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion(x_14, x_15, x_16, x_4);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 3);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(x_18, x_21, x_19, x_20, x_22, x_4);
return x_23;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(x_24, x_25, x_4);
lean_dec(x_25);
lean_dec(x_24);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion(x_27, x_4);
lean_dec(x_27);
return x_28;
}
default: 
{
lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(lean_object*);
lean_object* initialize_Lean_Server_InfoUtils(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__1 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__1);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__2 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6____closed__2);
l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1 = _init_l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___elambda__2___closed__1);
l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__1 = _init_l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__1();
l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2 = _init_l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__2);
l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__3 = _init_l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__3();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg___closed__3);
l_Lean_Server_Completion_completionBlackListExt___closed__1 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__1);
l_Lean_Server_Completion_completionBlackListExt___closed__2 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__2();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__2);
l_Lean_Server_Completion_completionBlackListExt___closed__3 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__3();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__3);
l_Lean_Server_Completion_completionBlackListExt___closed__4 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__4();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__4);
l_Lean_Server_Completion_completionBlackListExt___closed__5 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__5();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__5);
l_Lean_Server_Completion_completionBlackListExt___closed__6 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__6();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__6);
l_Lean_Server_Completion_completionBlackListExt___closed__7 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__7();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__7);
res = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Completion_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt);
lean_dec_ref(res);
l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1 = _init_l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1);
l_Lean_Server_Completion_State_itemsMain___default = _init_l_Lean_Server_Completion_State_itemsMain___default();
lean_mark_persistent(l_Lean_Server_Completion_State_itemsMain___default);
l_Lean_Server_Completion_State_itemsOther___default = _init_l_Lean_Server_Completion_State_itemsOther___default();
lean_mark_persistent(l_Lean_Server_Completion_State_itemsOther___default);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces___closed__1);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__1);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__2);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__3);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___closed__4);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__1);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__2___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__5 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__5);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__6 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__6);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__7 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__7);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__8 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__8);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1);
l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1 = _init_l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1);
l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2 = _init_l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
