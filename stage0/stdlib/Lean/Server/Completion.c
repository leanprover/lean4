// Lean compiler output
// Module: Lean.Server.Completion
// Imports: Init Lean.Environment Lean.Parser.Term Lean.Data.FuzzyMatching Lean.Data.Lsp.LanguageFeatures Lean.Data.Lsp.Capabilities Lean.Data.Lsp.Utf16 Lean.Meta.Tactic.Apply Lean.Meta.Match.MatcherInfo Lean.Server.InfoUtils Lean.Parser.Extension
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
lean_object* l_Lean_Name_getNumParts(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___closed__1;
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_instInhabitedParserCategory;
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at_Lean_Server_Completion_completeNamespaces___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f_choose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_occursInside_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___closed__1;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__5;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_matchNamespace___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__3;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4;
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_NameSSet_instInhabitedNameSSet;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
lean_object* l_Lean_Elab_InfoTree_foldInfo___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_State_itemsMain___default;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_State_itemsOther___default;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAliasState(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_occursBefore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__5;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_addToBlackList___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_findPrefix_go___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_completion_add_to_black_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_ConstantInfo_isCtor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3;
lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__4;
lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
static lean_object* l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3;
lean_object* l_String_csize(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__4;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
lean_object* l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__3;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1;
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__1;
uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isInductive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_State_itemsMain___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4;
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__3;
static double l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_getAllParentStructures(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completionBlackListExt;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_isCompletion(lean_object*);
extern lean_object* l_Lean_namespacesExt;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__2;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__4;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__6;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2;
uint8_t l_Lean_Elab_Info_isSmaller(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completeNamespaces___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1(lean_object*);
lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f_choose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8_(lean_object*);
lean_object* l_Lean_Meta_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6;
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__2;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__1;
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_data_value_to_string(lean_object*);
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Server", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Completion", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("completionBlackListExt", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1;
x_2 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__2;
x_3 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__3;
x_4 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__5;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Completion_addToBlackList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Completion_completionBlackListExt;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_completion_add_to_black_list(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Server_Completion_addToBlackList___closed__1;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
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
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___closed__1;
lean_inc(x_1);
lean_inc(x_11);
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_11, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
lean_inc(x_1);
x_16 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_9);
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
x_22 = l_Lean_Server_Completion_addToBlackList___closed__1;
lean_inc(x_1);
x_23 = l_Lean_TagDeclarationExtension_isTagged(x_22, x_11, x_1);
if (x_23 == 0)
{
lean_object* x_24; 
lean_free_object(x_16);
x_24 = l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(x_1, x_2, x_3, x_4, x_5, x_20);
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
x_27 = l_Lean_Server_Completion_addToBlackList___closed__1;
lean_inc(x_1);
x_28 = l_Lean_TagDeclarationExtension_isTagged(x_27, x_11, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(x_1, x_2, x_3, x_4, x_5, x_26);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isMatcher___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_12 = 1;
x_13 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg___lambda__1), 8, 2);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
x_16 = 0;
x_17 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_8, x_11, x_9, x_15, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg), 7, 0);
return x_2;
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
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_2);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 2;
lean_ctor_set_uint8(x_20, 9, x_22);
x_23 = l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1(x_18, x_5, x_6, x_7, x_8, x_16);
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
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get_uint8(x_20, 0);
x_38 = lean_ctor_get_uint8(x_20, 1);
x_39 = lean_ctor_get_uint8(x_20, 2);
x_40 = lean_ctor_get_uint8(x_20, 3);
x_41 = lean_ctor_get_uint8(x_20, 4);
x_42 = lean_ctor_get_uint8(x_20, 5);
x_43 = lean_ctor_get_uint8(x_20, 6);
x_44 = lean_ctor_get_uint8(x_20, 7);
x_45 = lean_ctor_get_uint8(x_20, 8);
x_46 = lean_ctor_get_uint8(x_20, 10);
x_47 = lean_ctor_get_uint8(x_20, 11);
lean_dec(x_20);
x_48 = 2;
x_49 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_49, 0, x_37);
lean_ctor_set_uint8(x_49, 1, x_38);
lean_ctor_set_uint8(x_49, 2, x_39);
lean_ctor_set_uint8(x_49, 3, x_40);
lean_ctor_set_uint8(x_49, 4, x_41);
lean_ctor_set_uint8(x_49, 5, x_42);
lean_ctor_set_uint8(x_49, 6, x_43);
lean_ctor_set_uint8(x_49, 7, x_44);
lean_ctor_set_uint8(x_49, 8, x_45);
lean_ctor_set_uint8(x_49, 9, x_48);
lean_ctor_set_uint8(x_49, 10, x_46);
lean_ctor_set_uint8(x_49, 11, x_47);
lean_ctor_set(x_5, 0, x_49);
x_50 = l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1(x_18, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_61 = lean_ctor_get(x_5, 0);
x_62 = lean_ctor_get(x_5, 1);
x_63 = lean_ctor_get(x_5, 2);
x_64 = lean_ctor_get(x_5, 3);
x_65 = lean_ctor_get(x_5, 4);
x_66 = lean_ctor_get(x_5, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_5);
x_67 = lean_ctor_get_uint8(x_61, 0);
x_68 = lean_ctor_get_uint8(x_61, 1);
x_69 = lean_ctor_get_uint8(x_61, 2);
x_70 = lean_ctor_get_uint8(x_61, 3);
x_71 = lean_ctor_get_uint8(x_61, 4);
x_72 = lean_ctor_get_uint8(x_61, 5);
x_73 = lean_ctor_get_uint8(x_61, 6);
x_74 = lean_ctor_get_uint8(x_61, 7);
x_75 = lean_ctor_get_uint8(x_61, 8);
x_76 = lean_ctor_get_uint8(x_61, 10);
x_77 = lean_ctor_get_uint8(x_61, 11);
if (lean_is_exclusive(x_61)) {
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
x_79 = 2;
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 0, 12);
} else {
 x_80 = x_78;
}
lean_ctor_set_uint8(x_80, 0, x_67);
lean_ctor_set_uint8(x_80, 1, x_68);
lean_ctor_set_uint8(x_80, 2, x_69);
lean_ctor_set_uint8(x_80, 3, x_70);
lean_ctor_set_uint8(x_80, 4, x_71);
lean_ctor_set_uint8(x_80, 5, x_72);
lean_ctor_set_uint8(x_80, 6, x_73);
lean_ctor_set_uint8(x_80, 7, x_74);
lean_ctor_set_uint8(x_80, 8, x_75);
lean_ctor_set_uint8(x_80, 9, x_79);
lean_ctor_set_uint8(x_80, 10, x_76);
lean_ctor_set_uint8(x_80, 11, x_77);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_62);
lean_ctor_set(x_81, 2, x_63);
lean_ctor_set(x_81, 3, x_64);
lean_ctor_set(x_81, 4, x_65);
lean_ctor_set(x_81, 5, x_66);
x_82 = l_Lean_withoutModifyingState___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable___spec__1(x_18, x_81, x_6, x_7, x_8, x_16);
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
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; double x_7; double x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_float(x_4);
x_8 = lean_unbox_float(x_6);
x_9 = lean_float_beq(x_7, x_8);
if (x_9 == 0)
{
double x_10; double x_11; uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_unbox_float(x_6);
lean_dec(x_6);
x_11 = lean_unbox_float(x_4);
lean_dec(x_4);
x_12 = lean_float_decLt(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_string_dec_lt(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
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
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1(x_1, x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_8, x_9, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___lambda__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Format_defWidth;
x_11 = lean_format_pretty(x_9, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Std_Format_defWidth;
x_15 = lean_format_pretty(x_12, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___closed__1;
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_consumeImplicitPrefix___rarg(x_2, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = 1;
x_16 = l_Lean_Name_toString(x_1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_13);
x_18 = lean_box(x_4);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_14);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_box(0);
x_24 = 1;
x_25 = l_Lean_Name_toString(x_1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_27 = lean_box(x_4);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_11, 0);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_ctor_set(x_3, 0, x_40);
x_41 = 1;
x_42 = l_Lean_Name_toString(x_1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_44 = lean_box(x_4);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_11, 0, x_47);
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
lean_ctor_set(x_3, 0, x_52);
x_53 = 1;
x_54 = l_Lean_Name_toString(x_1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_56 = lean_box(x_4);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_3);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set(x_59, 4, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_ctor_get(x_11, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_64 = x_11;
} else {
 lean_dec_ref(x_11);
 x_64 = lean_box(0);
}
x_65 = 1;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = 1;
x_69 = l_Lean_Name_toString(x_1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_62);
x_71 = lean_box(x_4);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_67);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
if (lean_is_scalar(x_64)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_64;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_63);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
return x_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Server_Completion_State_itemsMain___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_State_itemsMain___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_State_itemsOther___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, double x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem(x_1, x_2, x_6, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isTypeApplicable(x_2, x_4, x_8, x_9, x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_st_ref_take(x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box_float(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_array_push(x_24, x_26);
lean_ctor_set(x_21, 1, x_27);
x_28 = lean_st_ref_set(x_7, x_21, x_22);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_box_float(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_push(x_36, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_st_ref_set(x_7, x_40, x_22);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
x_47 = lean_st_ref_take(x_7, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_box_float(x_5);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_push(x_51, x_53);
lean_ctor_set(x_48, 0, x_54);
x_55 = lean_st_ref_set(x_7, x_48, x_49);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_box_float(x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_14);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_62, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
x_68 = lean_st_ref_set(x_7, x_67, x_49);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_13);
if (x_73 == 0)
{
return x_13;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, double x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1(x_1, x_2, x_5, x_3, x_6, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_st_ref_get(x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = l_Lean_findDocString_x3f(x_19, x_15, x_20, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1(x_1, x_2, x_5, x_3, x_6, x_22, x_7, x_8, x_9, x_10, x_11, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; double x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_float(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1(x_1, x_2, x_13, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; double x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox_float(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
static lean_object* _init_l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_instInhabitedProjectionFunctionInfo;
x_13 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1;
x_14 = l_Lean_MapDeclarationExtension_contains___rarg(x_12, x_13, x_11, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instInhabitedProjectionFunctionInfo;
x_21 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1;
x_22 = l_Lean_MapDeclarationExtension_contains___rarg(x_20, x_21, x_19, x_1);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(x_20, x_2, x_3, x_4, x_5, x_6, x_11);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = lean_environment_find(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_1, x_29);
x_31 = l_Lean_MessageData_ofExpr(x_30);
x_32 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(x_35, x_2, x_3, x_4, x_5, x_6, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_38 = x_28;
} else {
 lean_dec_ref(x_28);
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
lean_ctor_set(x_40, 1, x_26);
return x_40;
}
}
}
}
static lean_object* _init_l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1() {
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
static lean_object* _init_l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2() {
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
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_20 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_23) == 6)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
x_29 = lean_box(x_28);
lean_ctor_set(x_21, 0, x_29);
x_12 = x_21;
x_13 = x_24;
goto block_19;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_21);
lean_dec(x_23);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_12 = x_31;
x_13 = x_30;
goto block_19;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
if (lean_obj_tag(x_32) == 6)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_12 = x_39;
x_13 = x_33;
goto block_19;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_41 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_12 = x_41;
x_13 = x_40;
goto block_19;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_16 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
x_1 = x_11;
x_7 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 5)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Expr_isProp(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_14, 3);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_lengthTRAux___rarg(x_18, x_19);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_24, x_19);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_14);
x_26 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_26);
return x_8;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
x_28 = lean_nat_dec_eq(x_27, x_19);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_14);
x_29 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_29);
return x_8;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_14, 4);
lean_inc(x_30);
x_31 = l_List_isEmpty___rarg(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_14, sizeof(void*)*5 + 3);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*5 + 1);
lean_dec(x_14);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_8);
x_35 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(x_30, x_2, x_3, x_4, x_5, x_6, x_12);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_30);
x_36 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_36);
return x_8;
}
}
else
{
lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_14);
x_37 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_37);
return x_8;
}
}
else
{
lean_object* x_38; 
lean_dec(x_30);
lean_dec(x_14);
x_38 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
}
else
{
lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_14);
x_39 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_39);
return x_8;
}
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_14);
x_40 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_40);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Expr_isProp(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_List_lengthTRAux___rarg(x_46, x_47);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
x_51 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
return x_52;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_42, 2);
lean_inc(x_53);
x_54 = lean_nat_dec_eq(x_53, x_47);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_42);
x_55 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_41);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
x_58 = lean_nat_dec_eq(x_57, x_47);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
x_59 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_41);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_42, 4);
lean_inc(x_61);
x_62 = l_List_isEmpty___rarg(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_42, sizeof(void*)*5);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = lean_ctor_get_uint8(x_42, sizeof(void*)*5 + 3);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = lean_ctor_get_uint8(x_42, sizeof(void*)*5 + 1);
lean_dec(x_42);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(x_61, x_2, x_3, x_4, x_5, x_6, x_41);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
x_67 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_41);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_42);
x_69 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_41);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
lean_dec(x_42);
x_71 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_41);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
lean_dec(x_42);
x_73 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_41);
return x_74;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_42);
x_75 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_41);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_10);
x_77 = !lean_is_exclusive(x_8);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_8, 0);
lean_dec(x_78);
x_79 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_8, 0, x_79);
return x_8;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_8, 1);
lean_inc(x_80);
lean_dec(x_8);
x_81 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_8);
if (x_83 == 0)
{
return x_8;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_8, 0);
x_85 = lean_ctor_get(x_8, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_8);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 20;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 21;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 12;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 6;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_isCtor(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_ConstantInfo_isInductive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
lean_free_object(x_8);
x_15 = l_Lean_ConstantInfo_name(x_1);
x_16 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_ConstantInfo_type(x_1);
x_22 = lean_whnf(x_21, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Expr_isForall(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1;
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; 
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2;
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l_Lean_Expr_isForall(x_28);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_16, 0);
lean_dec(x_40);
x_41 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3;
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_45);
x_46 = lean_is_class(x_12, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_free_object(x_8);
x_47 = l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(x_45, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4;
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_47, 0);
lean_dec(x_58);
x_59 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5;
lean_ctor_set(x_47, 0, x_59);
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_dec(x_47);
x_61 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_47);
if (x_63 == 0)
{
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_47, 0);
x_65 = lean_ctor_get(x_47, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_47);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6;
lean_ctor_set(x_8, 0, x_67);
return x_8;
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7;
lean_ctor_set(x_8, 0, x_68);
return x_8;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_8, 0);
x_70 = lean_ctor_get(x_8, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_8);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_ConstantInfo_isCtor(x_1);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_ConstantInfo_isInductive(x_1);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_71);
x_74 = l_Lean_ConstantInfo_name(x_1);
x_75 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(x_74, x_2, x_3, x_4, x_5, x_6, x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = l_Lean_ConstantInfo_type(x_1);
x_81 = lean_whnf(x_80, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = l_Lean_Expr_isForall(x_82);
lean_dec(x_82);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1;
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2;
if (lean_is_scalar(x_84)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_84;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_92 = x_81;
} else {
 lean_dec_ref(x_81);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_75, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_95 = x_75;
} else {
 lean_dec_ref(x_75);
 x_95 = lean_box(0);
}
x_96 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_98);
x_99 = lean_is_class(x_71, x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(x_98, x_2, x_3, x_4, x_5, x_6, x_70);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
x_106 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4;
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_100, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_109 = x_100;
} else {
 lean_dec_ref(x_100);
 x_109 = lean_box(0);
}
x_110 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5;
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_114 = x_100;
} else {
 lean_dec_ref(x_100);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_70);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_70);
return x_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isEnumType___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, double x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_2);
x_16 = lean_environment_find(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_18, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_ConstantInfo_type(x_18);
lean_dec(x_18);
lean_ctor_set(x_20, 0, x_2);
x_31 = lean_unbox(x_29);
lean_dec(x_29);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_30, x_3, x_20, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_ConstantInfo_type(x_18);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = lean_unbox(x_33);
lean_dec(x_33);
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_34, x_3, x_35, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_37;
}
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_2);
x_45 = lean_environment_find(x_44, x_2);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_48, x_5, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
x_58 = l_Lean_ConstantInfo_type(x_48);
lean_dec(x_48);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_2);
x_60 = lean_unbox(x_56);
lean_dec(x_56);
x_61 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_1, x_58, x_3, x_59, x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_64 = x_49;
} else {
 lean_dec_ref(x_49);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("keyword", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 13;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static double _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_2 = lean_box_float(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2;
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_st_ref_take(x_2, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_push(x_16, x_18);
lean_ctor_set(x_13, 0, x_19);
x_20 = lean_st_ref_set(x_2, x_13, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_27, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_st_ref_set(x_2, x_32, x_14);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namespace", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 8;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object* x_1, double x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9);
x_11 = lean_box(0);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2;
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3;
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_st_ref_take(x_3, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_box_float(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_push(x_19, x_21);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_st_ref_set(x_3, x_16, x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_box_float(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_push(x_30, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_st_ref_set(x_3, x_35, x_17);
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
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
double x_9; lean_object* x_10; 
x_9 = lean_unbox_float(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_mk_ref(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_27);
x_29 = l_Array_append___rarg(x_26, x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
lean_ctor_set(x_12, 0, x_31);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_34);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_36);
x_38 = l_Array_append___rarg(x_35, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_ctor_set(x_12, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_44 = x_14;
} else {
 lean_dec_ref(x_14);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_45);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_47);
x_49 = l_Array_append___rarg(x_46, x_48);
x_50 = 1;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
if (lean_is_scalar(x_44)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_44;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_11;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
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
static double _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; double x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
x_8 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_11);
x_16 = l_Lean_mkPrivateName(x_15, x_11);
x_17 = lean_name_eq(x_16, x_1);
lean_dec(x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_7);
lean_dec(x_11);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_11);
x_22 = l_Lean_mkPrivateName(x_21, x_11);
x_23 = lean_name_eq(x_22, x_1);
lean_dec(x_1);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_7);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_st_ref_get(x_5, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_27);
x_33 = l_Lean_mkPrivateName(x_32, x_27);
x_34 = lean_name_eq(x_33, x_1);
lean_dec(x_1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_35 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_27);
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_31;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_2 = lean_box_float(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_Name_replacePrefix(x_1, x_2, x_11);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1;
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 1)
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_name_eq(x_14, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Name_isAnonymous(x_14);
lean_dec(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_apply_6(x_13, x_20, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
double x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
x_23 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_15, x_17, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; double x_33; double x_34; double x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = l_Lean_Name_getNumParts(x_16);
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
x_31 = 0;
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Float_ofScientific(x_30, x_31, x_32);
lean_dec(x_30);
x_34 = lean_unbox_float(x_27);
lean_dec(x_27);
x_35 = lean_float_div(x_34, x_33);
x_36 = lean_box_float(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_23, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; double x_45; double x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
lean_dec(x_23);
x_40 = l_Lean_Name_getNumParts(x_16);
lean_dec(x_16);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_40);
x_43 = 0;
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Float_ofScientific(x_42, x_43, x_44);
lean_dec(x_42);
x_46 = lean_unbox_float(x_39);
lean_dec(x_39);
x_47 = lean_float_div(x_46, x_45);
x_48 = lean_box_float(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_10);
return x_51;
}
}
}
}
else
{
double x_52; lean_object* x_53; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
lean_inc(x_17);
x_53 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_15, x_17, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_17);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = l_Lean_Name_str___override(x_11, x_17);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_53, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_10);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
x_62 = l_Lean_Name_str___override(x_11, x_17);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_10);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_12);
lean_dec(x_4);
x_66 = lean_box(0);
x_67 = lean_apply_6(x_13, x_66, x_6, x_7, x_8, x_9, x_10);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_12);
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = lean_apply_6(x_13, x_68, x_6, x_7, x_8, x_9, x_10);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = l_Lean_Name_isPrefixOf(x_4, x_12);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_12);
lean_dec(x_4);
x_71 = lean_box(0);
x_72 = lean_apply_6(x_13, x_71, x_6, x_7, x_8, x_9, x_10);
return x_72;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_Name_replacePrefix(x_12, x_4, x_11);
lean_dec(x_4);
x_74 = l_Lean_Name_isAtomic(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = lean_apply_6(x_13, x_75, x_6, x_7, x_8, x_9, x_10);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l_Lean_Name_isAnonymous(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_78 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_73);
x_82 = lean_box(0);
x_83 = lean_apply_6(x_13, x_82, x_6, x_7, x_8, x_9, x_10);
return x_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Name_isPrefixOf(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
x_24 = lean_box(0);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(x_21, x_1, x_3, x_2, x_24, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_1);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = l_Lean_Name_isPrefixOf(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(x_27, x_1, x_3, x_2, x_31, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_1);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_instInhabitedNat;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Server.Completion", 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Server.Completion.0.Lean.Server.Completion.truncate.go", 68);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__1;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__2;
x_3 = lean_unsigned_to_nat(177u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go(x_1, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
x_13 = lean_nat_dec_le(x_1, x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = l_Lean_Name_isAnonymous(x_5);
x_15 = lean_string_length(x_6);
if (x_14 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_add(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
x_17 = lean_nat_dec_le(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_2);
x_18 = lean_nat_sub(x_1, x_11);
x_19 = lean_nat_sub(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_extract(x_6, x_20, x_19);
lean_dec(x_19);
lean_dec(x_6);
x_22 = l_Lean_Name_str___override(x_5, x_21);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_12);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_add(x_10, x_23);
x_25 = lean_nat_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_nat_dec_le(x_25, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_2);
x_27 = lean_nat_sub(x_1, x_23);
x_28 = lean_nat_sub(x_27, x_10);
lean_dec(x_10);
lean_dec(x_27);
x_29 = lean_string_utf8_extract(x_6, x_23, x_28);
lean_dec(x_28);
lean_dec(x_6);
x_30 = l_Lean_Name_str___override(x_5, x_29);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_30);
return x_7;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_32, x_33);
x_35 = lean_nat_dec_le(x_1, x_34);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_31);
x_36 = l_Lean_Name_isAnonymous(x_5);
x_37 = lean_string_length(x_6);
if (x_36 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_nat_add(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
x_39 = lean_nat_dec_le(x_38, x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_38);
lean_dec(x_2);
x_40 = lean_nat_sub(x_1, x_33);
x_41 = lean_nat_sub(x_40, x_32);
lean_dec(x_32);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_string_utf8_extract(x_6, x_42, x_41);
lean_dec(x_41);
lean_dec(x_6);
x_44 = l_Lean_Name_str___override(x_5, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_1);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_34);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_add(x_32, x_47);
x_49 = lean_nat_add(x_48, x_37);
lean_dec(x_37);
lean_dec(x_48);
x_50 = lean_nat_dec_le(x_49, x_1);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
lean_dec(x_2);
x_51 = lean_nat_sub(x_1, x_47);
x_52 = lean_nat_sub(x_51, x_32);
lean_dec(x_32);
lean_dec(x_51);
x_53 = lean_string_utf8_extract(x_6, x_47, x_52);
lean_dec(x_52);
lean_dec(x_6);
x_54 = l_Lean_Name_str___override(x_5, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_1);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_32);
return x_57;
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
lean_dec(x_1);
x_58 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__4;
x_59 = l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1(x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_matchNamespace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_name_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
double x_10; lean_object* x_11; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
x_11 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_7, x_5, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = lean_name_eq(x_2, x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Name_isPrefixOf(x_2, x_1);
lean_dec(x_1);
lean_dec(x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Server_Completion_matchNamespace___closed__1;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_Completion_matchNamespace(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
lean_inc(x_5);
x_12 = l_Lean_Name_append(x_5, x_1);
lean_inc(x_4);
x_13 = l_Lean_Server_Completion_matchNamespace(x_4, x_12, x_2);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_apply_9(x_3, x_4, x_5, x_18, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Server_Completion_completeNamespaces_visitNamespaces(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
lean_inc(x_1);
lean_inc(x_32);
x_33 = l_Lean_Name_append(x_32, x_1);
lean_inc(x_33);
lean_inc(x_3);
x_34 = l_Lean_Server_Completion_matchNamespace(x_3, x_33, x_2);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_32);
lean_inc(x_4);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_4);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_17 = x_36;
x_18 = x_12;
goto block_31;
}
else
{
if (x_2 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; double x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
lean_inc(x_3);
x_39 = l_Lean_Name_replacePrefix(x_3, x_32, x_38);
lean_dec(x_32);
x_40 = lean_unbox_float(x_37);
lean_dec(x_37);
x_41 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(x_39, x_40, x_7, x_8, x_9, x_10, x_11, x_12);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3;
x_17 = x_43;
x_18 = x_42;
goto block_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_32);
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_box(0);
lean_inc(x_3);
x_46 = l_Lean_Name_replacePrefix(x_3, x_33, x_45);
lean_dec(x_33);
x_47 = lean_unbox_float(x_44);
lean_dec(x_44);
x_48 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(x_46, x_47, x_7, x_8, x_9, x_10, x_11, x_12);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3;
x_17 = x_50;
x_18 = x_49;
goto block_31;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_15);
lean_inc(x_4);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_4);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_17 = x_52;
x_18 = x_12;
goto block_31;
}
block_31:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; 
lean_free_object(x_17);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_5 = x_16;
x_6 = x_23;
x_12 = x_18;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_5 = x_16;
x_6 = x_29;
x_12 = x_18;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at_Lean_Server_Completion_completeNamespaces___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_16 = lean_apply_9(x_1, x_5, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_27 = lean_usize_add(x_3, x_26);
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
x_34 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_45 = lean_usize_add(x_3, x_44);
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
x_52 = lean_usize_add(x_3, x_51);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg___boxed), 11, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(x_1, x_22, x_23, lean_box(0), x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg), 9, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 10, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(0);
x_11 = l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5(x_1, x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
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
x_14 = l_Lean_AssocList_forM___at_Lean_Server_Completion_completeNamespaces___spec__3(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_25 = lean_usize_add(x_3, x_24);
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
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(x_2, x_10, x_19, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, double x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = l_Lean_Name_replacePrefix(x_3, x_4, x_12);
lean_dec(x_4);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Name_append(x_4, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_Name_replacePrefix(x_3, x_15, x_16);
lean_dec(x_15);
x_18 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Server_Completion_completeNamespaces_visitNamespaces(x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l_Lean_Name_isInternal(x_6);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_6);
x_15 = l_Lean_Environment_contains(x_1, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
x_17 = l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
lean_inc(x_6);
lean_inc(x_3);
x_18 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(x_3, x_4, x_6, x_17, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = l_Lean_Server_Completion_completeNamespaces___lambda__2(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9, x_10, x_11, x_12, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_32 = x_21;
} else {
 lean_dec_ref(x_21);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_13);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_13);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Server_Completion_completeNamespaces___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_namespacesExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completeNamespaces___lambda__1___boxed), 11, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
x_16 = l_Lean_NameSSet_instInhabitedNameSSet;
x_17 = l_Lean_Server_Completion_completeNamespaces___closed__1;
x_18 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_16, x_17, x_13);
x_19 = lean_box(x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completeNamespaces___lambda__3___boxed), 13, 5);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_15);
x_21 = l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(x_18, x_20, x_4, x_5, x_6, x_7, x_8, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; double x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_float(x_5);
lean_dec(x_5);
x_14 = l_Lean_Server_Completion_completeNamespaces___lambda__1(x_12, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Server_Completion_completeNamespaces___lambda__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Server_Completion_completeNamespaces___lambda__3(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Server_Completion_completeNamespaces(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
x_12 = lean_apply_2(x_1, x_5, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_apply_9(x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
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
x_39 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_dec(x_3);
lean_dec(x_1);
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
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_dec(x_17);
x_52 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_4, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_3);
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_50, x_3, x_2, x_4, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_36 = x_56;
x_37 = x_55;
goto block_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_61 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_5, x_9, x_10, x_11, x_12, x_13, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_59);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_box(0);
x_36 = x_64;
x_37 = x_63;
goto block_49;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; double x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = l_Lean_ConstantInfo_type(x_5);
lean_inc(x_4);
lean_ctor_set(x_62, 0, x_4);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_70 = lean_unbox_float(x_60);
lean_dec(x_60);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_71 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_59, x_68, x_1, x_62, x_69, x_70, x_9, x_10, x_11, x_12, x_13, x_65);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(0);
x_36 = x_74;
x_37 = x_73;
goto block_49;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
x_36 = x_76;
x_37 = x_75;
goto block_49;
}
}
else
{
uint8_t x_77; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
return x_71;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 0);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_71);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; double x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_62, 0);
lean_inc(x_81);
lean_dec(x_62);
x_82 = l_Lean_ConstantInfo_type(x_5);
lean_inc(x_4);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_4);
x_84 = lean_unbox(x_81);
lean_dec(x_81);
x_85 = lean_unbox_float(x_60);
lean_dec(x_60);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_86 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_59, x_82, x_1, x_83, x_84, x_85, x_9, x_10, x_11, x_12, x_13, x_65);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
x_36 = x_89;
x_37 = x_88;
goto block_49;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_87);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
x_36 = x_91;
x_37 = x_90;
goto block_49;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_94 = x_86;
} else {
 lean_dec_ref(x_86);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_61);
if (x_96 == 0)
{
return x_61;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_61, 0);
x_98 = lean_ctor_get(x_61, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_61);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_53);
if (x_100 == 0)
{
return x_53;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_53, 0);
x_102 = lean_ctor_get(x_53, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_53);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_50);
lean_inc(x_6);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_6);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_19 = x_105;
x_20 = x_14;
goto block_35;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_17);
lean_inc(x_6);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_6);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_19 = x_107;
x_20 = x_14;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_43 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3;
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
x_48 = l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 10, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(0);
x_11 = l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__5(x_1, x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
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
x_14 = l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__3(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_25 = lean_usize_add(x_3, x_24);
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(x_2, x_10, x_19, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__4(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(lean_object* x_1, lean_object* x_2, double x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_13);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_13, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_2);
x_19 = l_Lean_Name_getString_x21(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_21, x_13, x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_4 = x_14;
x_10 = x_30;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_4 = x_14;
x_10 = x_36;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8(lean_object* x_1, lean_object* x_2, double x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_13);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_13, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_2);
x_19 = l_Lean_Name_getString_x21(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_21, x_13, x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_4 = x_14;
x_10 = x_30;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_4 = x_14;
x_10 = x_36;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_16 = lean_apply_9(x_1, x_5, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_27 = lean_usize_add(x_3, x_26);
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
x_34 = l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_45 = lean_usize_add(x_3, x_44);
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
x_52 = lean_usize_add(x_3, x_51);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg___boxed), 11, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(x_1, x_10, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(x_1, x_22, x_23, lean_box(0), x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
lean_dec(x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg), 9, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 10, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(0);
x_11 = l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__12(x_1, x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
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
x_14 = l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__10(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_25 = lean_usize_add(x_3, x_24);
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
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(x_2, x_10, x_19, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__11(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Name_isPrefixOf(x_1, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
lean_inc(x_4);
x_16 = l_Lean_Name_replacePrefix(x_4, x_1, x_15);
lean_dec(x_1);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; double x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_unbox_float(x_20);
lean_dec(x_20);
x_22 = l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8(x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_22;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_getAliasState(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_26 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1), 11, 3);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__9(x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_16 = x_30;
x_17 = x_29;
goto block_23;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_32;
x_17 = x_31;
goto block_23;
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
lean_inc(x_38);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_38, x_7, x_8, x_9, x_10, x_11);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_inc(x_37);
lean_inc(x_2);
x_43 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec(x_38);
lean_dec(x_37);
x_44 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_44;
x_17 = x_42;
goto block_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; double x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Name_getString_x21(x_37);
x_47 = lean_box(0);
x_48 = l_Lean_Name_str___override(x_47, x_46);
x_49 = lean_unbox_float(x_45);
lean_dec(x_45);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_50 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItemForDecl(x_48, x_38, x_1, x_49, x_6, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_16 = x_53;
x_17 = x_52;
goto block_23;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_55;
x_17 = x_54;
goto block_23;
}
}
else
{
uint8_t x_56; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_38);
lean_dec(x_37);
x_60 = lean_ctor_get(x_39, 1);
lean_inc(x_60);
lean_dec(x_39);
x_61 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_61;
x_17 = x_60;
goto block_23;
}
}
block_23:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_4 = x_15;
x_5 = x_21;
x_11 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 10, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(0);
x_11 = l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__21(x_1, x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
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
x_14 = l_Lean_AssocList_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__19(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_25 = lean_usize_add(x_3, x_24);
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
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22(x_2, x_10, x_19, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__20(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem(x_14, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_10 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
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
x_43 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_3, x_18, x_41, x_9, x_10, x_11, x_12, x_13, x_14);
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
x_72 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_3, x_18, x_71, x_9, x_10, x_11, x_12, x_13, x_14);
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
x_29 = lean_usize_add(x_7, x_28);
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
x_37 = lean_usize_add(x_7, x_36);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
lean_dec(x_17);
x_69 = l_Lean_LocalDecl_userName(x_68);
lean_inc(x_69);
lean_inc(x_2);
x_70 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec(x_69);
lean_dec(x_68);
x_71 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_41 = x_71;
x_42 = x_13;
goto block_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; double x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_LocalDecl_type(x_68);
lean_dec(x_68);
x_74 = lean_box(0);
x_75 = 5;
x_76 = lean_unbox_float(x_72);
lean_dec(x_72);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_77 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_69, x_73, x_1, x_74, x_75, x_76, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_3);
x_41 = x_3;
x_42 = x_79;
goto block_65;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_41 = x_81;
x_42 = x_80;
goto block_65;
}
}
else
{
uint8_t x_82; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_28 = lean_usize_add(x_6, x_27);
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
lean_dec(x_2);
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
x_36 = lean_usize_add(x_6, x_35);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26(x_1, x_2, x_3, x_13, x_12, x_16, x_17, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_29 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(x_27, x_28, x_6, x_7, x_8, x_9, x_10, x_26);
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
x_50 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(x_1, x_2, x_45, x_44, x_48, x_49, x_46, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_44);
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
x_61 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(x_59, x_60, x_6, x_7, x_8, x_9, x_10, x_58);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_28);
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
lean_dec(x_17);
x_51 = l_Lean_LocalDecl_userName(x_50);
lean_inc(x_51);
lean_inc(x_2);
x_52 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_2, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec(x_51);
lean_dec(x_50);
x_53 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_30 = x_53;
x_31 = x_13;
goto block_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; double x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_LocalDecl_type(x_50);
lean_dec(x_50);
x_56 = lean_box(0);
x_57 = 5;
x_58 = lean_unbox_float(x_54);
lean_dec(x_54);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_59 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_51, x_55, x_1, x_56, x_57, x_58, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_30 = x_56;
x_31 = x_61;
goto block_47;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_30 = x_63;
x_31 = x_62;
goto block_47;
}
}
else
{
uint8_t x_64; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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
lean_dec(x_2);
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
x_25 = lean_usize_add(x_6, x_24);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_12 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_4, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_36 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(x_1, x_2, x_31, x_30, x_34, x_35, x_32, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_30);
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
x_47 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(x_45, x_46, x_5, x_6, x_7, x_8, x_9, x_44);
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
x_76 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(x_1, x_2, x_71, x_70, x_74, x_75, x_72, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_70);
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
x_86 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(x_84, x_85, x_5, x_6, x_7, x_8, x_9, x_83);
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
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_6, x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
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
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_4, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; double x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = l_Lean_ConstantInfo_type(x_4);
lean_ctor_set(x_26, 0, x_3);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = lean_unbox_float(x_24);
lean_dec(x_24);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_23, x_36, x_5, x_26, x_37, x_38, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_40);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 0);
lean_dec(x_48);
x_49 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
lean_ctor_set(x_39, 0, x_49);
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_dec(x_39);
x_51 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
return x_39;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_39, 0);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_39);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; double x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_26, 0);
lean_inc(x_57);
lean_dec(x_26);
x_58 = l_Lean_ConstantInfo_type(x_4);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_3);
x_60 = lean_unbox(x_57);
lean_dec(x_57);
x_61 = lean_unbox_float(x_24);
lean_dec(x_24);
x_62 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_23, x_58, x_5, x_59, x_60, x_61, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_63);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
x_70 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
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
}
}
else
{
uint8_t x_76; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_25);
if (x_76 == 0)
{
return x_25;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_25, 0);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_25);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_13);
if (x_80 == 0)
{
return x_13;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_13, 0);
x_82 = lean_ctor_get(x_13, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_13);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_21, x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2;
x_14 = x_25;
x_15 = x_24;
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_4, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_14 = x_5;
x_15 = x_32;
goto block_20;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; double x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = l_Lean_ConstantInfo_type(x_4);
lean_ctor_set(x_31, 0, x_3);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = lean_unbox_float(x_29);
lean_dec(x_29);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_28, x_36, x_6, x_31, x_37, x_38, x_8, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_14 = x_5;
x_15 = x_41;
goto block_20;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_5);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
x_14 = x_43;
x_15 = x_42;
goto block_20;
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; double x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = l_Lean_ConstantInfo_type(x_4);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_3);
x_51 = lean_unbox(x_48);
lean_dec(x_48);
x_52 = lean_unbox_float(x_29);
lean_dec(x_29);
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_28, x_49, x_6, x_50, x_51, x_52, x_8, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_14 = x_5;
x_15 = x_55;
goto block_20;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_5);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
x_14 = x_57;
x_15 = x_56;
goto block_20;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
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
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_30);
if (x_62 == 0)
{
return x_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_30, 0);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_30);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_22);
if (x_66 == 0)
{
return x_22;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_22, 0);
x_68 = lean_ctor_get(x_22, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_22);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
block_20:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_17 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_16, x_14, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__2(x_4, x_3, x_5, x_6, x_15, x_2, x_26, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_6);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_17, 0, x_32);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_35 = x_24;
} else {
 lean_dec_ref(x_24);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(x_2);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed), 12, 5);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_5);
lean_closure_set(x_18, 3, x_6);
lean_closure_set(x_18, 4, x_3);
x_19 = lean_ctor_get(x_4, 4);
lean_inc(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
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
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_box(0);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(x_4, x_3, x_2, x_1, x_5, x_6, x_31, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_7);
return x_32;
}
else
{
uint8_t x_33; 
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
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_20, 0);
lean_dec(x_34);
x_35 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
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
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
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
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_13, 0);
lean_dec(x_44);
x_45 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_45);
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_isPrefixOf(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Lean_Name_replacePrefix(x_3, x_2, x_6);
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic(x_1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, double x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore_searchAlias(x_2, x_3, x_4, x_5, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_Completion_completeNamespaces(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5___boxed), 3, 1);
lean_closure_set(x_28, 0, x_1);
lean_inc(x_3);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed), 10, 1);
lean_closure_set(x_29, 0, x_3);
x_30 = lean_ctor_get(x_4, 5);
lean_inc(x_30);
x_31 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_32 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(x_3, x_1, x_15, x_30, x_31, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_33);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_Lean_getAliasState(x_15);
lean_inc(x_4);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__7), 11, 3);
lean_closure_set(x_42, 0, x_4);
lean_closure_set(x_42, 1, x_28);
lean_closure_set(x_42, 2, x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__18(x_41, x_42, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_dec(x_44);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = l_Lean_Parser_getTokenTable(x_15);
lean_dec(x_15);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Data_Trie_findPrefix_go___rarg(x_53, x_54, x_55);
lean_dec(x_53);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
x_60 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(x_56, x_58, x_59, x_31, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_56);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Server_Completion_completeNamespaces(x_4, x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_51);
lean_dec(x_15);
x_63 = lean_ctor_get(x_43, 1);
lean_inc(x_63);
lean_dec(x_43);
x_64 = l_Lean_Server_Completion_completeNamespaces(x_4, x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_15);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_dec(x_43);
x_66 = l_Lean_Server_Completion_completeNamespaces(x_4, x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
}
else
{
uint8_t x_71; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_32, 0);
x_73 = lean_ctor_get(x_32, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_32);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_19);
if (x_75 == 0)
{
return x_19;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_19, 0);
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_19);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = l_Lean_Name_isAtomic(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9(x_4, x_3, x_1, x_2, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24(x_1, x_4, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_dec(x_4);
lean_dec(x_2);
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
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9(x_4, x_3, x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_erase_macro_scopes(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10(x_5, x_1, x_4, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate(x_12, x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10(x_5, x_1, x_17, x_16, x_18, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__6(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_3);
lean_dec(x_3);
x_12 = l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__7(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_3);
lean_dec(x_3);
x_12 = l_List_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__8(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__16(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__22(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__23(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__26(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__27(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__28(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_dec(x_4);
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
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_15;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__6(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__8(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__9(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___lambda__10(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_5);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___boxed), 11, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_6);
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_2, x_9, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf(x_20, x_2, x_4, x_5, x_6, x_7, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_getAppFn(x_1);
x_9 = l_Lean_Expr_isConstOf(x_8, x_2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1;
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
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_inc(x_7);
x_16 = l_Lean_FVarId_getDecl(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
x_20 = l_Lean_Expr_consumeMData(x_19);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDefEqToAppOf(x_20, x_1, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
lean_inc(x_2);
{
size_t _tmp_4 = x_26;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_24;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
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
x_12 = l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
x_11 = lean_usize_dec_lt(x_3, x_2);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_st_ref_take(x_5, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_15, x_13, x_17);
x_19 = lean_st_ref_set(x_5, x_18, x_16);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_17;
x_10 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_18, x_3, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
lean_inc(x_9);
x_14 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_11, x_9, x_13);
x_15 = lean_st_ref_set(x_2, x_14, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
x_21 = l_Lean_isStructure(x_20, x_9);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_st_ref_get(x_6, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_getAllParentStructures(x_26, x_9);
x_28 = lean_array_get_size(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_27, x_29, x_30, x_13, x_2, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_NameSet_empty;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_st_ref_get(x_4, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVarsCore(x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_4, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_17);
x_23 = lean_st_ref_set(x_4, x_19, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 2);
x_32 = lean_ctor_get(x_19, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_16);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_normPrivateName_x3f(x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = l_Lean_Name_getPrefix(x_22);
lean_dec(x_22);
x_24 = l_Lean_NameSet_contains(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_11);
x_26 = l_Lean_ConstantInfo_name(x_4);
lean_inc(x_26);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_26, x_6, x_7, x_8, x_9, x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(x_23, x_4, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; double x_56; uint8_t x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_26);
x_52 = l_Lean_Name_getString_x21(x_26);
x_53 = lean_box(0);
x_54 = l_Lean_Name_str___override(x_53, x_52);
x_55 = l_Lean_ConstantInfo_type(x_4);
lean_ctor_set(x_42, 0, x_26);
x_56 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_57 = lean_unbox(x_51);
lean_dec(x_51);
x_58 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_54, x_55, x_2, x_42, x_57, x_56, x_5, x_6, x_7, x_8, x_9, x_49);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; double x_65; uint8_t x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
lean_inc(x_26);
x_60 = l_Lean_Name_getString_x21(x_26);
x_61 = lean_box(0);
x_62 = l_Lean_Name_str___override(x_61, x_60);
x_63 = l_Lean_ConstantInfo_type(x_4);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_26);
x_65 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_66 = lean_unbox(x_59);
lean_dec(x_59);
x_67 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_62, x_63, x_2, x_64, x_66, x_65, x_5, x_6, x_7, x_8, x_9, x_49);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_41);
if (x_68 == 0)
{
return x_41;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_41, 0);
x_70 = lean_ctor_get(x_41, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_41);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_31);
if (x_72 == 0)
{
return x_31;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_31, 0);
x_74 = lean_ctor_get(x_31, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_31);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_27);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_27, 0);
lean_dec(x_77);
x_78 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_27, 0, x_78);
return x_27;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
lean_dec(x_27);
x_80 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_11, 1);
lean_inc(x_82);
lean_dec(x_11);
x_83 = lean_ctor_get(x_12, 0);
lean_inc(x_83);
lean_dec(x_12);
x_84 = l_Lean_Name_getPrefix(x_83);
lean_dec(x_83);
x_85 = l_Lean_NameSet_contains(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_86 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = l_Lean_ConstantInfo_name(x_4);
lean_inc(x_88);
x_89 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_88, x_6, x_7, x_8, x_9, x_82);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod(x_84, x_4, x_6, x_7, x_8, x_9, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_101 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_4, x_5, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; double x_115; uint8_t x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
lean_inc(x_88);
x_110 = l_Lean_Name_getString_x21(x_88);
x_111 = lean_box(0);
x_112 = l_Lean_Name_str___override(x_111, x_110);
x_113 = l_Lean_ConstantInfo_type(x_4);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_88);
x_115 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_116 = lean_unbox(x_108);
lean_dec(x_108);
x_117 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_112, x_113, x_2, x_114, x_116, x_115, x_5, x_6, x_7, x_8, x_9, x_107);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_118 = lean_ctor_get(x_101, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_101, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_120 = x_101;
} else {
 lean_dec_ref(x_101);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_122 = lean_ctor_get(x_93, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_93, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_124 = x_93;
} else {
 lean_dec_ref(x_93);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_126 = lean_ctor_get(x_89, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_127 = x_89;
} else {
 lean_dec_ref(x_89);
 x_127 = lean_box(0);
}
x_128 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("completion", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1;
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2;
x_4 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Syntax_isIdent(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_4);
lean_inc(x_13);
x_15 = l_Lean_Syntax_getKind(x_13);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4;
x_17 = lean_name_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_13, x_20);
lean_dec(x_13);
x_22 = l_Lean_Syntax_isIdent(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = 1;
x_28 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(x_2, x_25, x_26, x_27, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
x_30 = 0;
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore(x_2, x_29, x_4, x_30, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_st_ref_get(x_10, x_11);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__1___boxed), 10, 2);
lean_closure_set(x_37, 0, x_5);
lean_closure_set(x_37, 1, x_3);
x_38 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(x_36, x_37, x_6, x_7, x_8, x_9, x_10, x_34);
return x_38;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(x_15, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_12, 0, x_18);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_12);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
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
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getDotCompletionTypeNames(x_28, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_41);
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_dec(x_8);
x_43 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2), 11, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___boxed), 7, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__4), 8, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg), 8, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_6, x_11, x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f(x_1, x_2, x_12, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl(x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; double x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = l_Lean_ConstantInfo_type(x_5);
lean_ctor_set(x_26, 0, x_4);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = lean_unbox_float(x_24);
lean_dec(x_24);
x_39 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_23, x_36, x_3, x_26, x_37, x_38, x_6, x_7, x_8, x_9, x_10, x_33);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; double x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_26, 0);
lean_inc(x_40);
lean_dec(x_26);
x_41 = l_Lean_ConstantInfo_type(x_5);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_4);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
x_44 = lean_unbox_float(x_24);
lean_dec(x_24);
x_45 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem(x_23, x_41, x_3, x_42, x_43, x_44, x_6, x_7, x_8, x_9, x_10, x_33);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_Expr_cleanupAnnotations(x_12);
x_14 = l_Lean_Expr_getAppFn(x_13);
lean_dec(x_13);
x_15 = l_Lean_Expr_cleanupAnnotations(x_14);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__1___boxed), 11, 3);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
x_23 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__2(x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_7 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_2, x_7, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__2), 9, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg), 8, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_2, x_12, x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_pure___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("field", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_24; double x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
lean_inc(x_24);
lean_inc(x_1);
x_26 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_24);
x_27 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_27;
x_17 = x_11;
goto block_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2;
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3;
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_29);
x_33 = lean_st_ref_take(x_6, x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_28);
x_38 = lean_array_push(x_36, x_37);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_st_ref_set(x_6, x_40, x_35);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_43;
x_17 = x_42;
goto block_23;
}
}
else
{
lean_object* x_44; 
lean_dec(x_15);
x_44 = l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2;
x_16 = x_44;
x_17 = x_11;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
x_11 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = 0;
x_14 = l_Lean_getStructureFieldsFlattened(x_12, x_1, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1(x_2, x_14, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__1;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__2;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = 1;
x_7 = l_Lean_Name_toString(x_3, x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__3___boxed), 9, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_7);
x_9 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__4;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___spec__2___rarg), 8, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM(x_1, x_2, x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("), ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_String_csize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_32; lean_object* x_33; double x_34; lean_object* x_35; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 3);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_32 = 1;
lean_inc(x_17);
x_33 = l_Lean_Name_toString(x_17, x_32);
x_34 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1;
lean_inc(x_33);
lean_inc(x_4);
x_35 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_4, x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_17);
if (lean_is_scalar(x_25)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_25;
}
lean_ctor_set(x_36, 0, x_24);
if (lean_is_scalar(x_23)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_23;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_22);
x_26 = x_37;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_94; lean_object* x_111; lean_object* x_112; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
x_42 = l_Lean_KVMap_findCore(x_6, x_17);
lean_dec(x_17);
x_43 = lean_ctor_get(x_18, 3);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_box(0);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_129; 
x_129 = lean_box(0);
x_45 = x_129;
goto block_93;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_40, 0);
x_131 = lean_ctor_get(x_130, 0);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
x_45 = x_132;
goto block_93;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_45 = x_134;
goto block_93;
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_133, 0);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_45 = x_136;
goto block_93;
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_unbox(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_45 = x_139;
goto block_93;
}
else
{
uint8_t x_140; lean_object* x_141; 
lean_dec(x_39);
lean_dec(x_25);
lean_dec(x_23);
x_140 = 0;
lean_inc(x_3);
x_141 = l_Lean_Syntax_getRange_x3f(x_3, x_140);
if (lean_obj_tag(x_141) == 0)
{
if (lean_obj_tag(x_42) == 0)
{
x_94 = x_44;
goto block_110;
}
else
{
lean_object* x_142; 
lean_dec(x_41);
x_142 = lean_ctor_get(x_42, 0);
lean_inc(x_142);
lean_dec(x_42);
x_111 = x_44;
x_112 = x_142;
goto block_128;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_141, 0);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_1, 1);
x_148 = l_Lean_FileMap_utf8PosToLspPos(x_147, x_145);
lean_dec(x_145);
if (x_5 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = l_Lean_FileMap_utf8PosToLspPos(x_147, x_146);
lean_dec(x_146);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_150);
lean_inc(x_33);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_33);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_141, 0, x_151);
if (lean_obj_tag(x_42) == 0)
{
x_94 = x_141;
goto block_110;
}
else
{
lean_object* x_152; 
lean_dec(x_41);
x_152 = lean_ctor_get(x_42, 0);
lean_inc(x_152);
lean_dec(x_42);
x_111 = x_141;
x_112 = x_152;
goto block_128;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5;
x_154 = lean_nat_add(x_146, x_153);
lean_dec(x_146);
x_155 = l_Lean_FileMap_utf8PosToLspPos(x_147, x_154);
lean_dec(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_148);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_156);
lean_inc(x_33);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_33);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_141, 0, x_157);
if (lean_obj_tag(x_42) == 0)
{
x_94 = x_141;
goto block_110;
}
else
{
lean_object* x_158; 
lean_dec(x_41);
x_158 = lean_ctor_get(x_42, 0);
lean_inc(x_158);
lean_dec(x_42);
x_111 = x_141;
x_112 = x_158;
goto block_128;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_141, 0);
lean_inc(x_159);
lean_dec(x_141);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_1, 1);
x_163 = l_Lean_FileMap_utf8PosToLspPos(x_162, x_160);
lean_dec(x_160);
if (x_5 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = l_Lean_FileMap_utf8PosToLspPos(x_162, x_161);
lean_dec(x_161);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
lean_inc(x_165);
lean_inc(x_33);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_33);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_165);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
if (lean_obj_tag(x_42) == 0)
{
x_94 = x_167;
goto block_110;
}
else
{
lean_object* x_168; 
lean_dec(x_41);
x_168 = lean_ctor_get(x_42, 0);
lean_inc(x_168);
lean_dec(x_42);
x_111 = x_167;
x_112 = x_168;
goto block_128;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5;
x_170 = lean_nat_add(x_161, x_169);
lean_dec(x_161);
x_171 = l_Lean_FileMap_utf8PosToLspPos(x_162, x_170);
lean_dec(x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_171);
lean_inc(x_172);
lean_inc(x_33);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_33);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
if (lean_obj_tag(x_42) == 0)
{
x_94 = x_174;
goto block_110;
}
else
{
lean_object* x_175; 
lean_dec(x_41);
x_175 = lean_ctor_get(x_42, 0);
lean_inc(x_175);
lean_dec(x_42);
x_111 = x_174;
x_112 = x_175;
goto block_128;
}
}
}
}
}
}
}
}
}
block_93:
{
lean_dec(x_45);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_46 = lean_data_value_to_string(x_41);
x_47 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_50, x_43);
lean_dec(x_43);
x_52 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_53 = lean_string_append(x_51, x_52);
if (lean_is_scalar(x_39)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_39;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_44);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_44);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
x_58 = lean_array_push(x_24, x_57);
if (lean_is_scalar(x_25)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_25;
}
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_23)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_23;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_22);
x_26 = x_60;
goto block_31;
}
else
{
uint8_t x_61; 
lean_dec(x_41);
lean_dec(x_39);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_data_value_to_string(x_62);
x_64 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_43);
lean_dec(x_43);
x_69 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_70 = lean_string_append(x_68, x_69);
lean_ctor_set(x_42, 0, x_70);
x_71 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_33);
lean_ctor_set(x_72, 1, x_42);
lean_ctor_set(x_72, 2, x_44);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_44);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_38);
x_74 = lean_array_push(x_24, x_73);
if (lean_is_scalar(x_25)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_25;
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_23)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_23;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_22);
x_26 = x_76;
goto block_31;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_data_value_to_string(x_77);
x_79 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_string_append(x_82, x_43);
lean_dec(x_43);
x_84 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_88 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_88, 0, x_33);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_44);
lean_ctor_set(x_88, 3, x_87);
lean_ctor_set(x_88, 4, x_44);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_38);
x_90 = lean_array_push(x_24, x_89);
if (lean_is_scalar(x_25)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_25;
}
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_23)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_23;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_22);
x_26 = x_92;
goto block_31;
}
}
}
block_110:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_95 = lean_data_value_to_string(x_41);
x_96 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_97 = lean_string_append(x_96, x_95);
lean_dec(x_95);
x_98 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_string_append(x_99, x_43);
lean_dec(x_43);
x_101 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_33);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_44);
lean_ctor_set(x_105, 3, x_104);
lean_ctor_set(x_105, 4, x_94);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_38);
x_107 = lean_array_push(x_24, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_22);
x_26 = x_109;
goto block_31;
}
block_128:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_113 = lean_data_value_to_string(x_112);
x_114 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_115 = lean_string_append(x_114, x_113);
lean_dec(x_113);
x_116 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_string_append(x_117, x_43);
lean_dec(x_43);
x_119 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_33);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_44);
lean_ctor_set(x_123, 3, x_122);
lean_ctor_set(x_123, 4, x_111);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_38);
x_125 = lean_array_push(x_24, x_124);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_22);
x_26 = x_127;
goto block_31;
}
}
block_31:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_7 = x_19;
x_8 = x_29;
x_13 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_getOptionDecls(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 2);
x_15 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
x_16 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_12, x_15, x_6, x_7, x_8, x_9, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_19);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_26);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = 0;
x_8 = l_Lean_Syntax_getSubstring_x3f(x_6, x_7, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_10 = lean_box(x_7);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_10);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
x_13 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_12, x_11, x_4);
lean_dec(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = lean_string_utf8_at_end(x_15, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_string_utf8_get(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_19 = 46;
x_20 = lean_uint32_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_string_utf8_extract(x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_box(x_7);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed), 10, 5);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_6);
lean_closure_set(x_26, 3, x_24);
lean_closure_set(x_26, 4, x_25);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
x_28 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_27, x_26, x_4);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 2);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_string_utf8_extract(x_29, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_33 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__8;
x_34 = lean_string_append(x_32, x_33);
x_35 = 1;
x_36 = lean_box(x_35);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed), 10, 5);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_3);
lean_closure_set(x_37, 2, x_6);
lean_closure_set(x_37, 3, x_34);
lean_closure_set(x_37, 4, x_36);
x_38 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
x_39 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_38, x_37, x_4);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
lean_dec(x_15);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 2);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_string_utf8_extract(x_40, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_44 = lean_box(x_7);
lean_inc(x_1);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed), 10, 5);
lean_closure_set(x_45, 0, x_1);
lean_closure_set(x_45, 1, x_3);
lean_closure_set(x_45, 2, x_6);
lean_closure_set(x_45, 3, x_43);
lean_closure_set(x_45, 4, x_44);
x_46 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__7;
x_47 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_46, x_45, x_4);
lean_dec(x_1);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___lambda__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_instInhabitedParserCategory;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4;
x_2 = lean_box_float(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(x_1, x_3);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_4, x_7);
x_9 = lean_box(0);
x_10 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_9);
x_12 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2___boxed__const__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_push(x_6, x_13);
x_1 = x_14;
x_2 = x_5;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_parserExtension;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tactic", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__4;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__5;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__6;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_11 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1;
x_12 = l_Lean_ScopedEnvExtension_getState___rarg(x_10, x_11, x_9);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3;
x_15 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_16 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_17 = l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
x_21 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(x_20, x_19);
x_22 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_21);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
x_31 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(x_30, x_29);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
lean_ctor_set(x_15, 0, x_34);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
x_39 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(x_38, x_37);
x_40 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_39);
x_41 = 1;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_6, 0, x_43);
return x_6;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_6);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_48 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__1;
x_49 = l_Lean_ScopedEnvExtension_getState___rarg(x_47, x_48, x_46);
lean_dec(x_46);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__3;
x_52 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Parser_getCategory___spec__1(x_50, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_54 = l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__1(x_53);
x_55 = lean_ctor_get(x_54, 2);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
x_58 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(x_57, x_56);
x_59 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_58);
x_60 = 1;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_45);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_65 = x_52;
} else {
 lean_dec_ref(x_52);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_64, 2);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Server_Completion_State_itemsMain___default___closed__1;
x_69 = l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2(x_68, x_67);
x_70 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems(x_69);
x_71 = 1;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_45);
return x_74;
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
lean_object* x_7; uint8_t x_92; 
x_92 = l_Lean_Elab_Info_isCompletion(x_5);
if (x_92 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_93; 
x_93 = l_Lean_Elab_Info_occursInside_x3f(x_5, x_1);
if (lean_obj_tag(x_93) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_94; 
x_94 = l_Lean_Elab_Info_occursBefore_x3f(x_5, x_1);
if (lean_obj_tag(x_94) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = l_Lean_Elab_Info_tailPos_x3f(x_5);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_99 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_98);
x_100 = l_Lean_FileMap_toPosition(x_2, x_99);
lean_dec(x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_nat_dec_eq(x_101, x_3);
lean_dec(x_101);
if (x_102 == 0)
{
lean_free_object(x_94);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_4);
lean_ctor_set(x_103, 1, x_5);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_94, 0, x_105);
return x_94;
}
}
else
{
uint8_t x_106; 
lean_free_object(x_94);
x_106 = !lean_is_exclusive(x_97);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_97, 0);
x_108 = l_Lean_FileMap_toPosition(x_2, x_107);
lean_dec(x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_nat_dec_eq(x_109, x_3);
lean_dec(x_109);
if (x_110 == 0)
{
lean_free_object(x_97);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_4);
lean_ctor_set(x_111, 1, x_5);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_97, 0, x_113);
return x_97;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_97, 0);
lean_inc(x_114);
lean_dec(x_97);
x_115 = l_Lean_FileMap_toPosition(x_2, x_114);
lean_dec(x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_nat_dec_eq(x_116, x_3);
lean_dec(x_116);
if (x_117 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_4);
lean_ctor_set(x_118, 1, x_5);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_94);
x_122 = l_Lean_Elab_Info_tailPos_x3f(x_5);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_124 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_123);
x_125 = l_Lean_FileMap_toPosition(x_2, x_124);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_nat_dec_eq(x_126, x_3);
lean_dec(x_126);
if (x_127 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_4);
lean_ctor_set(x_128, 1, x_5);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_122, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_133 = x_122;
} else {
 lean_dec_ref(x_122);
 x_133 = lean_box(0);
}
x_134 = l_Lean_FileMap_toPosition(x_2, x_132);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_nat_dec_eq(x_135, x_3);
lean_dec(x_135);
if (x_136 == 0)
{
lean_dec(x_133);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_4);
lean_ctor_set(x_137, 1, x_5);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
if (lean_is_scalar(x_133)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_133;
}
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_6, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Elab_Info_occursBefore_x3f(x_5, x_1);
if (lean_obj_tag(x_145) == 0)
{
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_212; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_212 = l_Lean_Elab_Info_tailPos_x3f(x_5);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_213 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_214 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_213);
x_215 = l_Lean_FileMap_toPosition(x_2, x_214);
lean_dec(x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_nat_dec_eq(x_216, x_3);
lean_dec(x_216);
if (x_217 == 0)
{
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_218; 
x_218 = lean_box(0);
x_148 = x_218;
goto block_211;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_212, 0);
lean_inc(x_219);
lean_dec(x_212);
x_220 = l_Lean_FileMap_toPosition(x_2, x_219);
lean_dec(x_219);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_nat_dec_eq(x_221, x_3);
lean_dec(x_221);
if (x_222 == 0)
{
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_223; 
x_223 = lean_box(0);
x_148 = x_223;
goto block_211;
}
}
block_211:
{
uint8_t x_149; 
lean_dec(x_148);
x_149 = !lean_is_exclusive(x_143);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_143, 1);
x_151 = lean_ctor_get(x_143, 0);
lean_dec(x_151);
x_152 = l_Lean_Elab_Info_occursBefore_x3f(x_150, x_1);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_154 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_153);
x_155 = lean_nat_dec_lt(x_146, x_154);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = lean_nat_dec_eq(x_146, x_154);
lean_dec(x_154);
lean_dec(x_146);
if (x_156 == 0)
{
lean_free_object(x_143);
lean_dec(x_150);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_157; 
x_157 = l_Lean_Elab_Info_isSmaller(x_5, x_150);
lean_dec(x_150);
if (x_157 == 0)
{
lean_free_object(x_143);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_6);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 0, x_4);
x_158 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_144;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_143);
if (lean_is_scalar(x_147)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_147;
}
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_146);
lean_dec(x_6);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 0, x_4);
x_161 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_144;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_143);
if (lean_is_scalar(x_147)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_147;
}
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
else
{
uint8_t x_164; 
lean_dec(x_147);
x_164 = !lean_is_exclusive(x_152);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_152, 0);
x_166 = lean_nat_dec_lt(x_146, x_165);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = lean_nat_dec_eq(x_146, x_165);
lean_dec(x_165);
lean_dec(x_146);
if (x_167 == 0)
{
lean_free_object(x_152);
lean_free_object(x_143);
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_168; 
x_168 = l_Lean_Elab_Info_isSmaller(x_5, x_150);
lean_dec(x_150);
if (x_168 == 0)
{
lean_free_object(x_152);
lean_free_object(x_143);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_6);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 0, x_4);
x_169 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_144;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_143);
lean_ctor_set(x_152, 0, x_170);
return x_152;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_146);
lean_dec(x_6);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 0, x_4);
x_171 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_144;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_143);
lean_ctor_set(x_152, 0, x_172);
return x_152;
}
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_152, 0);
lean_inc(x_173);
lean_dec(x_152);
x_174 = lean_nat_dec_lt(x_146, x_173);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = lean_nat_dec_eq(x_146, x_173);
lean_dec(x_173);
lean_dec(x_146);
if (x_175 == 0)
{
lean_free_object(x_143);
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_176; 
x_176 = l_Lean_Elab_Info_isSmaller(x_5, x_150);
lean_dec(x_150);
if (x_176 == 0)
{
lean_free_object(x_143);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_6);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 0, x_4);
x_177 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_144;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_143);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
lean_dec(x_150);
lean_dec(x_146);
lean_dec(x_6);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 0, x_4);
x_180 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_144;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_143);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_143, 1);
lean_inc(x_183);
lean_dec(x_143);
x_184 = l_Lean_Elab_Info_occursBefore_x3f(x_183, x_1);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_186 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_185);
x_187 = lean_nat_dec_lt(x_146, x_186);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = lean_nat_dec_eq(x_146, x_186);
lean_dec(x_186);
lean_dec(x_146);
if (x_188 == 0)
{
lean_dec(x_183);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_189; 
x_189 = l_Lean_Elab_Info_isSmaller(x_5, x_183);
lean_dec(x_183);
if (x_189 == 0)
{
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_6);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_4);
lean_ctor_set(x_190, 1, x_5);
x_191 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_144;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
if (lean_is_scalar(x_147)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_147;
}
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_186);
lean_dec(x_183);
lean_dec(x_146);
lean_dec(x_6);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_4);
lean_ctor_set(x_194, 1, x_5);
x_195 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_144;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
if (lean_is_scalar(x_147)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_147;
}
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_147);
x_198 = lean_ctor_get(x_184, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_199 = x_184;
} else {
 lean_dec_ref(x_184);
 x_199 = lean_box(0);
}
x_200 = lean_nat_dec_lt(x_146, x_198);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = lean_nat_dec_eq(x_146, x_198);
lean_dec(x_198);
lean_dec(x_146);
if (x_201 == 0)
{
lean_dec(x_199);
lean_dec(x_183);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_202; 
x_202 = l_Lean_Elab_Info_isSmaller(x_5, x_183);
lean_dec(x_183);
if (x_202 == 0)
{
lean_dec(x_199);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_6);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_4);
lean_ctor_set(x_203, 1, x_5);
x_204 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_144;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
if (lean_is_scalar(x_199)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_199;
}
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_198);
lean_dec(x_183);
lean_dec(x_146);
lean_dec(x_6);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_4);
lean_ctor_set(x_207, 1, x_5);
x_208 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_144;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
if (lean_is_scalar(x_199)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_199;
}
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
}
}
}
else
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
}
else
{
lean_object* x_224; 
lean_dec(x_93);
x_224 = l_Lean_Elab_Info_pos_x3f(x_5);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_226 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_225);
x_7 = x_226;
goto block_91;
}
else
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
lean_dec(x_224);
x_7 = x_227;
goto block_91;
}
}
}
block_91:
{
lean_object* x_8; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Lean_FileMap_toPosition(x_2, x_7);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Elab_Info_tailPos_x3f(x_5);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7;
x_79 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_78);
x_80 = l_Lean_FileMap_toPosition(x_2, x_79);
lean_dec(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_nat_dec_eq(x_76, x_3);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_eq(x_76, x_81);
lean_dec(x_81);
lean_dec(x_76);
if (x_83 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_84; 
x_84 = lean_box(0);
x_8 = x_84;
goto block_74;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
lean_dec(x_77);
x_86 = l_Lean_FileMap_toPosition(x_2, x_85);
lean_dec(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_nat_dec_eq(x_76, x_3);
if (x_88 == 0)
{
lean_dec(x_87);
lean_dec(x_76);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_eq(x_76, x_87);
lean_dec(x_87);
lean_dec(x_76);
if (x_89 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_8 = x_90;
goto block_74;
}
}
}
block_74:
{
lean_dec(x_8);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_24 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_15, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_14, 1);
x_38 = lean_ctor_get(x_14, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = l_Lean_Elab_Info_isSmaller(x_5, x_40);
lean_dec(x_40);
if (x_42 == 0)
{
lean_free_object(x_37);
lean_free_object(x_14);
lean_free_object(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_15, 0, x_45);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 0, x_4);
return x_6;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
x_46 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_15, 0, x_46);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 0, x_4);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_14);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = l_Lean_Elab_Info_isSmaller(x_5, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_free_object(x_14);
lean_free_object(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_50 = x_6;
} else {
 lean_dec_ref(x_6);
 x_50 = lean_box(0);
}
x_51 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_15, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_5);
lean_ctor_set(x_14, 1, x_52);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_14);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Elab_Info_isSmaller(x_5, x_55);
lean_dec(x_55);
if (x_57 == 0)
{
lean_dec(x_56);
lean_free_object(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_58 = x_6;
} else {
 lean_dec_ref(x_6);
 x_58 = lean_box(0);
}
x_59 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_15, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_15);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_15);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_64 = x_14;
} else {
 lean_dec_ref(x_14);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l_Lean_Elab_Info_isSmaller(x_5, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_68 = x_6;
} else {
 lean_dec_ref(x_6);
 x_68 = lean_box(0);
}
x_69 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_5);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
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
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_FileMap_toPosition(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_choose___boxed), 6, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Elab_InfoTree_foldInfo___rarg(x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 6)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion(x_17, x_18, x_16, x_19, x_5);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
x_25 = lean_ctor_get(x_15, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 3);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletion(x_22, x_25, x_23, x_21, x_24, x_26, x_5);
return x_27;
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_4);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_15, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 3);
lean_inc(x_31);
lean_dec(x_15);
x_32 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotIdCompletion(x_28, x_30, x_29, x_31, x_5);
lean_dec(x_28);
return x_32;
}
case 3:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_4);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_15, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_15, 3);
lean_inc(x_36);
lean_dec(x_15);
x_37 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion(x_33, x_35, x_34, x_36, x_5);
lean_dec(x_33);
return x_37;
}
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion(x_38, x_39, x_4, x_5);
lean_dec(x_39);
return x_40;
}
case 7:
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_4);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
x_42 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion(x_41, x_5);
lean_dec(x_41);
return x_42;
}
default: 
{
lean_object* x_43; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_5);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_5);
return x_44;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_FuzzyMatching(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_FuzzyMatching(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Capabilities(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__1);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__2 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__2();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__2);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__3 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__3();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__3);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__4 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__4();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__4);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__5 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__5();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8____closed__5);
if (builtin) {res = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_8_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Completion_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt);
lean_dec_ref(res);
}l_Lean_Server_Completion_addToBlackList___closed__1 = _init_l_Lean_Server_Completion_addToBlackList___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_addToBlackList___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___closed__1);
l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1 = _init_l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at___private_Lean_Server_Completion_0__Lean_Server_Completion_sortCompletionItems___spec__1___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_mkCompletionItem___closed__1);
l_Lean_Server_Completion_State_itemsMain___default___closed__1 = _init_l_Lean_Server_Completion_State_itemsMain___default___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_State_itemsMain___default___closed__1);
l_Lean_Server_Completion_State_itemsMain___default = _init_l_Lean_Server_Completion_State_itemsMain___default();
lean_mark_persistent(l_Lean_Server_Completion_State_itemsMain___default);
l_Lean_Server_Completion_State_itemsOther___default = _init_l_Lean_Server_Completion_State_itemsOther___default();
lean_mark_persistent(l_Lean_Server_Completion_State_itemsOther___default);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addCompletionItem___lambda__1___closed__1);
l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1 = _init_l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1();
lean_mark_persistent(l_Lean_isProjectionFn___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4);
l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1 = _init_l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1();
lean_mark_persistent(l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__1);
l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2 = _init_l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2();
lean_mark_persistent(l_List_allM___at___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__4);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__5);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__6);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_getCompletionKindForDecl___closed__7);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___closed__4();
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addKeywordCompletionItem___boxed__const__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_runM___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchAtomic___closed__1();
l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1);
l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1___closed__1 = _init_l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___spec__1___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_truncate_go___closed__4);
l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1 = _init_l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1);
l_Lean_Server_Completion_matchNamespace___closed__1 = _init_l_Lean_Server_Completion_matchNamespace___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_matchNamespace___closed__1);
l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1);
l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2 = _init_l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2);
l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3 = _init_l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__3);
l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1 = _init_l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1);
l_Lean_Server_Completion_completeNamespaces___closed__1 = _init_l_Lean_Server_Completion_completeNamespaces___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completeNamespaces___closed__1);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__1);
l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_idCompletionCore___spec__17___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__2___closed__4);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_dotCompletion___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__3);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__4 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_fieldIdCompletion___closed__4);
l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__1);
l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__2);
l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__3);
l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__4);
l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___spec__1___closed__5);
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
l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__8 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__8();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_optionCompletion___closed__8);
l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2___boxed__const__1 = _init_l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2___boxed__const__1();
lean_mark_persistent(l_Lean_RBNode_fold___at___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___spec__2___boxed__const__1);
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
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___lambda__1___closed__7);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_tacticCompletion___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
