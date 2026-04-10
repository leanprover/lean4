// Lean compiler output
// Module: Lean.Server.Completion.CompletionCollectors
// Imports: public import Lean.Data.FuzzyMatching public import Lean.Elab.Tactic.Doc public import Lean.Server.Completion.CompletionResolution public import Lean.Server.Completion.EligibleHeaderDecls public import Lean.Server.RequestCancellation
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_String_charactersIn(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Server_Completion_allowCompletion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Server_Completion_getCompletionKindForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_isPrivatePrefix(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_RequestCancellation_requestCancelled;
uint8_t l_Lean_Name_isInternal(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_Zipper_prependNode___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* lean_data_value_to_string(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCoreUnfoldingAnnotations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_getAliasState(lean_object*);
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
lean_object* l_Lean_Server_Completion_getEligibleHeaderDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionTagsForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaces(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getDotIdCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_takeWhile___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_forEligibleDeclsM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
static const lean_ctor_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "keyword"};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Server.Completion.CompletionCollectors"};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "_private.Lean.Server.Completion.CompletionCollectors.0.Lean.Server.Completion.truncate.go"};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "field"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Completion_fieldIdCompletion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_Completion_fieldIdCompletion___closed__0 = (const lean_object*)&l_Lean_Server_Completion_fieldIdCompletion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Completion_optionCompletion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_Completion_optionCompletion___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_Completion_optionCompletion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "), "};
static const lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_Completion_optionCompletion___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Server_Completion_optionCompletion___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___closed__2 = (const lean_object*)&l_Lean_Server_Completion_optionCompletion___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_Completion_optionCompletion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__0;
static lean_once_cell_t l_Lean_Server_Completion_optionCompletion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__1;
static lean_once_cell_t l_Lean_Server_Completion_optionCompletion___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__2;
static lean_once_cell_t l_Lean_Server_Completion_optionCompletion___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__3;
static lean_once_cell_t l_Lean_Server_Completion_optionCompletion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "error name"};
static const lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1_value;
static const lean_array_object l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__2 = (const lean_object*)&l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3 = (const lean_object*)&l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_Completion_endSectionCompletion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_Completion_endSectionCompletion___closed__0 = (const lean_object*)&l_Lean_Server_Completion_endSectionCompletion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(lean_object* v_item_3_, lean_object* v_id_x3f_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; lean_object* v_uri_9_; lean_object* v_pos_10_; lean_object* v_completionInfoPos_11_; lean_object* v_label_12_; lean_object* v_detail_x3f_13_; lean_object* v_documentation_x3f_14_; lean_object* v_kind_x3f_15_; lean_object* v_textEdit_x3f_16_; lean_object* v_sortText_x3f_17_; lean_object* v_tags_x3f_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_32_; 
v___x_8_ = lean_st_ref_take(v_a_6_);
v_uri_9_ = lean_ctor_get(v_a_5_, 0);
v_pos_10_ = lean_ctor_get(v_a_5_, 1);
v_completionInfoPos_11_ = lean_ctor_get(v_a_5_, 2);
v_label_12_ = lean_ctor_get(v_item_3_, 0);
v_detail_x3f_13_ = lean_ctor_get(v_item_3_, 1);
v_documentation_x3f_14_ = lean_ctor_get(v_item_3_, 2);
v_kind_x3f_15_ = lean_ctor_get(v_item_3_, 3);
v_textEdit_x3f_16_ = lean_ctor_get(v_item_3_, 4);
v_sortText_x3f_17_ = lean_ctor_get(v_item_3_, 5);
v_tags_x3f_18_ = lean_ctor_get(v_item_3_, 7);
v_isSharedCheck_32_ = !lean_is_exclusive(v_item_3_);
if (v_isSharedCheck_32_ == 0)
{
lean_object* v_unused_33_; 
v_unused_33_ = lean_ctor_get(v_item_3_, 6);
lean_dec(v_unused_33_);
v___x_20_ = v_item_3_;
v_isShared_21_ = v_isSharedCheck_32_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tags_x3f_18_);
lean_inc(v_sortText_x3f_17_);
lean_inc(v_textEdit_x3f_16_);
lean_inc(v_kind_x3f_15_);
lean_inc(v_documentation_x3f_14_);
lean_inc(v_detail_x3f_13_);
lean_inc(v_label_12_);
lean_dec(v_item_3_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_32_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
lean_inc(v_completionInfoPos_11_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v_completionInfoPos_11_);
lean_inc_ref(v_pos_10_);
lean_inc_ref(v_uri_9_);
v___x_23_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_23_, 0, v_uri_9_);
lean_ctor_set(v___x_23_, 1, v_pos_10_);
lean_ctor_set(v___x_23_, 2, v___x_22_);
lean_ctor_set(v___x_23_, 3, v_id_x3f_4_);
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 6, v___x_24_);
v___x_26_ = v___x_20_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_label_12_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_detail_x3f_13_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_documentation_x3f_14_);
lean_ctor_set(v_reuseFailAlloc_31_, 3, v_kind_x3f_15_);
lean_ctor_set(v_reuseFailAlloc_31_, 4, v_textEdit_x3f_16_);
lean_ctor_set(v_reuseFailAlloc_31_, 5, v_sortText_x3f_17_);
lean_ctor_set(v_reuseFailAlloc_31_, 6, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_31_, 7, v_tags_x3f_18_);
v___x_26_ = v_reuseFailAlloc_31_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_27_ = lean_array_push(v___x_8_, v___x_26_);
v___x_28_ = lean_st_ref_set(v_a_6_, v___x_27_);
v___x_29_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___boxed(lean_object* v_item_34_, lean_object* v_id_x3f_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_34_, v_id_x3f_35_, v_a_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(lean_object* v_item_40_, lean_object* v_id_x3f_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_40_, v_id_x3f_41_, v_a_42_, v_a_43_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___boxed(lean_object* v_item_51_, lean_object* v_id_x3f_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(v_item_51_, v_id_x3f_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(lean_object* v_label_62_, lean_object* v_id_63_, uint8_t v_kind_64_, lean_object* v_tags_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_item_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_69_ = 1;
v___x_70_ = l_Lean_Name_toString(v_label_62_, v___x_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_box(v_kind_64_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v_tags_65_);
v_item_75_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_item_75_, 0, v___x_70_);
lean_ctor_set(v_item_75_, 1, v___x_71_);
lean_ctor_set(v_item_75_, 2, v___x_71_);
lean_ctor_set(v_item_75_, 3, v___x_73_);
lean_ctor_set(v_item_75_, 4, v___x_71_);
lean_ctor_set(v_item_75_, 5, v___x_71_);
lean_ctor_set(v_item_75_, 6, v___x_71_);
lean_ctor_set(v_item_75_, 7, v___x_74_);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_id_63_);
v___x_77_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_75_, v___x_76_, v_a_66_, v_a_67_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg___boxed(lean_object* v_label_78_, lean_object* v_id_79_, lean_object* v_kind_80_, lean_object* v_tags_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
uint8_t v_kind_boxed_85_; lean_object* v_res_86_; 
v_kind_boxed_85_ = lean_unbox(v_kind_80_);
v_res_86_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_78_, v_id_79_, v_kind_boxed_85_, v_tags_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(lean_object* v_label_87_, lean_object* v_id_88_, uint8_t v_kind_89_, lean_object* v_tags_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_87_, v_id_88_, v_kind_89_, v_tags_90_, v_a_91_, v_a_92_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___boxed(lean_object* v_label_100_, lean_object* v_id_101_, lean_object* v_kind_102_, lean_object* v_tags_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
uint8_t v_kind_boxed_112_; lean_object* v_res_113_; 
v_kind_boxed_112_ = lean_unbox(v_kind_102_);
v_res_113_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(v_label_100_, v_id_101_, v_kind_boxed_112_, v_tags_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(lean_object* v_label_114_, lean_object* v_declName_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; lean_object* v_env_124_; uint8_t v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_st_ref_get(v_a_121_);
v_env_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc_ref(v_env_124_);
lean_dec(v___x_123_);
v___x_125_ = 0;
lean_inc(v_declName_115_);
v___x_126_ = l_Lean_Environment_find_x3f(v_env_124_, v_declName_115_, v___x_125_);
if (lean_obj_tag(v___x_126_) == 1)
{
lean_object* v_val_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_156_; 
v_val_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_156_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_156_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_val_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_156_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Server_Completion_getCompletionKindForDecl(v_val_127_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_val_127_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
lean_inc(v_declName_115_);
v___x_133_ = l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(v_declName_115_, v_a_121_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref(v___x_133_);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 0);
lean_ctor_set(v___x_129_, 0, v_declName_115_);
v___x_136_ = v___x_129_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_declName_115_);
v___x_136_ = v_reuseFailAlloc_139_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
uint8_t v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unbox(v_a_132_);
lean_dec(v_a_132_);
v___x_138_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_label_114_, v___x_136_, v___x_137_, v_a_134_, v_a_116_, v_a_117_);
return v___x_138_;
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_a_132_);
lean_del_object(v___x_129_);
lean_dec(v_declName_115_);
lean_dec(v_label_114_);
v_a_140_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_133_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_133_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_del_object(v___x_129_);
lean_dec(v_declName_115_);
lean_dec(v_label_114_);
v_a_148_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_131_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_131_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_126_);
lean_dec(v_declName_115_);
lean_dec(v_label_114_);
v___x_157_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg___boxed(lean_object* v_label_159_, lean_object* v_declName_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v_label_159_, v_declName_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(lean_object* v_label_169_, lean_object* v_declName_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v_label_169_, v_declName_170_, v_a_171_, v_a_172_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___boxed(lean_object* v_label_180_, lean_object* v_declName_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(v_label_180_, v_declName_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(lean_object* v_keyword_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_item_204_; lean_object* v___x_205_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__1));
v___x_202_ = lean_box(0);
v___x_203_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
v_item_204_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_item_204_, 0, v_keyword_197_);
lean_ctor_set(v_item_204_, 1, v___x_201_);
lean_ctor_set(v_item_204_, 2, v___x_202_);
lean_ctor_set(v_item_204_, 3, v___x_203_);
lean_ctor_set(v_item_204_, 4, v___x_202_);
lean_ctor_set(v_item_204_, 5, v___x_202_);
lean_ctor_set(v_item_204_, 6, v___x_202_);
lean_ctor_set(v_item_204_, 7, v___x_202_);
v___x_205_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_204_, v___x_202_, v_a_198_, v_a_199_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___boxed(lean_object* v_keyword_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_keyword_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object* v_keyword_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_keyword_211_, v_a_212_, v_a_213_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object* v_keyword_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(v_keyword_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(lean_object* v_ns_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_item_246_; lean_object* v___x_247_; 
v___x_241_ = 1;
v___x_242_ = l_Lean_Name_toString(v_ns_237_, v___x_241_);
v___x_243_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__1));
v___x_244_ = lean_box(0);
v___x_245_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
v_item_246_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_item_246_, 0, v___x_242_);
lean_ctor_set(v_item_246_, 1, v___x_243_);
lean_ctor_set(v_item_246_, 2, v___x_244_);
lean_ctor_set(v_item_246_, 3, v___x_245_);
lean_ctor_set(v_item_246_, 4, v___x_244_);
lean_ctor_set(v_item_246_, 5, v___x_244_);
lean_ctor_set(v_item_246_, 6, v___x_244_);
lean_ctor_set(v_item_246_, 7, v___x_244_);
v___x_247_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v_item_246_, v___x_244_, v_a_238_, v_a_239_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___boxed(lean_object* v_ns_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_ns_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object* v_ns_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_ns_253_, v_a_254_, v_a_255_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object* v_ns_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(v_ns_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0(lean_object* v___x_273_, lean_object* v_x_274_, lean_object* v___x_275_, lean_object* v_a_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_st_mk_ref(v___x_273_);
lean_inc_ref(v_a_276_);
lean_inc(v___x_282_);
v___x_283_ = lean_apply_8(v_x_274_, v___x_275_, v___x_282_, v_a_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, lean_box(0));
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_312_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_312_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_312_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_312_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
if (lean_obj_tag(v_a_284_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_298_; 
lean_dec(v___x_282_);
v_a_288_ = lean_ctor_get(v_a_284_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_284_);
if (v_isSharedCheck_298_ == 0)
{
v___x_290_ = v_a_284_;
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v_a_284_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_293_);
v___x_295_ = v___x_286_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_311_; 
v_a_299_ = lean_ctor_get(v_a_284_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_284_);
if (v_isSharedCheck_311_ == 0)
{
v___x_301_ = v_a_284_;
v_isShared_302_ = v_isSharedCheck_311_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v_a_284_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_311_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_303_ = lean_st_ref_get(v___x_282_);
lean_dec(v___x_282_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_a_299_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_304_);
v___x_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_306_);
v___x_308_ = v___x_286_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
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
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v___x_282_);
v_a_313_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_283_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_283_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0___boxed(lean_object* v___x_321_, lean_object* v_x_322_, lean_object* v___x_323_, lean_object* v_a_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0(v___x_321_, v_x_322_, v___x_323_, v_a_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec_ref(v_a_324_);
return v_res_330_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = l_Lean_Server_RequestCancellation_requestCancelled;
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(lean_object* v_uri_335_, lean_object* v_pos_336_, lean_object* v_completionInfoPos_337_, lean_object* v_ctx_338_, lean_object* v_lctx_339_, lean_object* v_x_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; 
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_uri_335_);
lean_ctor_set(v___x_343_, 1, v_pos_336_);
lean_ctor_set(v___x_343_, 2, v_completionInfoPos_337_);
v___x_344_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
lean_inc_ref(v_a_341_);
v___f_345_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lam__0___boxed), 9, 4);
lean_closure_set(v___f_345_, 0, v___x_344_);
lean_closure_set(v___f_345_, 1, v_x_340_);
lean_closure_set(v___f_345_, 2, v___x_343_);
lean_closure_set(v___f_345_, 3, v_a_341_);
v___x_346_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_338_, v_lctx_339_, v___f_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_367_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_367_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_367_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_367_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
if (lean_obj_tag(v_a_347_) == 0)
{
lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec_ref(v_a_347_);
v___x_351_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_366_; 
v_a_355_ = lean_ctor_get(v_a_347_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_a_347_);
if (v_isSharedCheck_366_ == 0)
{
v___x_357_ = v_a_347_;
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v_a_347_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_snd_359_; lean_object* v___x_361_; 
v_snd_359_ = lean_ctor_get(v_a_355_, 1);
lean_inc(v_snd_359_);
lean_dec(v_a_355_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_snd_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_snd_359_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_361_);
v___x_363_ = v___x_349_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_a_368_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_346_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_346_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___boxed(lean_object* v_uri_376_, lean_object* v_pos_377_, lean_object* v_completionInfoPos_378_, lean_object* v_ctx_379_, lean_object* v_lctx_380_, lean_object* v_x_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_376_, v_pos_377_, v_completionInfoPos_378_, v_ctx_379_, v_lctx_380_, v_x_381_, v_a_382_);
lean_dec_ref(v_a_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(lean_object* v_declName_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; 
lean_inc(v_declName_385_);
v___x_388_ = lean_private_to_user_name(v_declName_385_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_declName_385_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v_val_391_; lean_object* v___x_392_; lean_object* v_env_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_val_391_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_val_391_);
v___x_392_ = lean_st_ref_get(v_a_386_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_392_);
v___x_394_ = l_Lean_mkPrivateName(v_env_393_, v_val_391_);
lean_dec_ref(v_env_393_);
v___x_395_ = lean_name_eq(v___x_394_, v_declName_385_);
lean_dec(v_declName_385_);
lean_dec(v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_388_, 0);
lean_dec(v_unused_404_);
v___x_397_ = v___x_388_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_dec(v___x_388_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 0);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
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
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_388_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg___boxed(lean_object* v_declName_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_406_, v_a_407_);
lean_dec(v_a_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(lean_object* v_declName_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_410_, v_a_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object* v_declName_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(v_declName_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(lean_object* v_ns_424_, lean_object* v_id_425_, uint8_t v_danglingDot_426_, lean_object* v_declName_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_433_; lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_495_; 
v___x_433_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_427_, v_a_428_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_495_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_495_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_495_;
goto v_resetjp_435_;
}
v___jp_430_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
v_resetjp_435_:
{
if (lean_obj_tag(v_a_434_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_490_; 
v_val_438_ = lean_ctor_get(v_a_434_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_490_ == 0)
{
v___x_440_ = v_a_434_;
v_isShared_441_ = v_isSharedCheck_490_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_val_438_);
lean_dec(v_a_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_490_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_Name_isPrefixOf(v_ns_424_, v_val_438_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_del_object(v___x_440_);
lean_dec(v_val_438_);
v___x_443_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_443_);
v___x_445_ = v___x_436_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_box(0);
v___x_448_ = l_Lean_Name_replacePrefix(v_val_438_, v_ns_424_, v___x_447_);
if (v_danglingDot_426_ == 0)
{
if (lean_obj_tag(v_id_425_) == 1)
{
if (lean_obj_tag(v___x_448_) == 1)
{
lean_object* v_pre_449_; lean_object* v_str_450_; lean_object* v_pre_451_; lean_object* v_str_452_; uint8_t v___x_453_; 
v_pre_449_ = lean_ctor_get(v_id_425_, 0);
v_str_450_ = lean_ctor_get(v_id_425_, 1);
v_pre_451_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_pre_451_);
v_str_452_ = lean_ctor_get(v___x_448_, 1);
lean_inc_ref(v_str_452_);
v___x_453_ = lean_name_eq(v_pre_449_, v_pre_451_);
lean_dec(v_pre_451_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_Name_isAnonymous(v_pre_449_);
if (v___x_454_ == 0)
{
lean_dec_ref(v_str_452_);
lean_dec_ref(v___x_448_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = l_String_charactersIn(v_str_450_, v_str_452_);
lean_dec_ref(v_str_452_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec_ref(v___x_448_);
lean_del_object(v___x_440_);
v___x_456_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_456_);
v___x_458_ = v___x_436_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v___x_461_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_448_);
v___x_461_ = v___x_440_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_448_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_461_);
v___x_463_ = v___x_436_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
else
{
uint8_t v___x_466_; 
lean_dec_ref(v___x_448_);
v___x_466_ = l_String_charactersIn(v_str_450_, v_str_452_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec_ref(v_str_452_);
lean_del_object(v___x_440_);
v___x_467_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_467_);
v___x_469_ = v___x_436_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = l_Lean_Name_str___override(v___x_447_, v_str_452_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_471_);
v___x_473_ = v___x_440_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_477_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_473_);
v___x_475_ = v___x_436_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
else
{
lean_dec(v___x_448_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
}
else
{
lean_dec(v___x_448_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
}
else
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_Name_isPrefixOf(v_id_425_, v___x_448_);
if (v___x_478_ == 0)
{
lean_dec(v___x_448_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
lean_object* v___x_479_; uint8_t v___y_481_; uint8_t v___x_488_; 
v___x_479_ = l_Lean_Name_replacePrefix(v___x_448_, v_id_425_, v___x_447_);
v___x_488_ = l_Lean_Name_isAtomic(v___x_479_);
if (v___x_488_ == 0)
{
v___y_481_ = v___x_488_;
goto v___jp_480_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = l_Lean_Name_isAnonymous(v___x_479_);
if (v___x_489_ == 0)
{
v___y_481_ = v___x_488_;
goto v___jp_480_;
}
else
{
lean_dec(v___x_479_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
}
v___jp_480_:
{
if (v___y_481_ == 0)
{
lean_dec(v___x_479_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
lean_object* v___x_483_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_479_);
v___x_483_ = v___x_440_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_479_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_483_);
v___x_485_ = v___x_436_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_a_434_);
v___x_491_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_491_);
v___x_493_ = v___x_436_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg___boxed(lean_object* v_ns_496_, lean_object* v_id_497_, lean_object* v_danglingDot_498_, lean_object* v_declName_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_danglingDot_boxed_502_; lean_object* v_res_503_; 
v_danglingDot_boxed_502_ = lean_unbox(v_danglingDot_498_);
v_res_503_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_496_, v_id_497_, v_danglingDot_boxed_502_, v_declName_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec(v_id_497_);
lean_dec(v_ns_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object* v_ns_504_, lean_object* v_id_505_, uint8_t v_danglingDot_506_, lean_object* v_declName_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_504_, v_id_505_, v_danglingDot_506_, v_declName_507_, v_a_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* v_ns_514_, lean_object* v_id_515_, lean_object* v_danglingDot_516_, lean_object* v_declName_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
uint8_t v_danglingDot_boxed_523_; lean_object* v_res_524_; 
v_danglingDot_boxed_523_ = lean_unbox(v_danglingDot_516_);
v_res_524_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(v_ns_514_, v_id_515_, v_danglingDot_boxed_523_, v_declName_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_id_515_);
lean_dec(v_ns_514_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0(lean_object* v___y_525_, lean_object* v_toPure_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_a_527_);
lean_ctor_set(v___x_528_, 1, v___y_525_);
v___x_529_ = lean_apply_2(v_toPure_526_, lean_box(0), v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1(lean_object* v_f_530_, lean_object* v_decl_531_, lean_object* v_ci_532_, lean_object* v_toPure_533_, lean_object* v_toBind_534_, lean_object* v_____r_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___f_538_; lean_object* v___x_539_; 
v___x_537_ = lean_apply_2(v_f_530_, v_decl_531_, v_ci_532_);
v___f_538_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_538_, 0, v___y_536_);
lean_closure_set(v___f_538_, 1, v_toPure_533_);
v___x_539_ = lean_apply_4(v_toBind_534_, lean_box(0), lean_box(0), v___x_537_, v___f_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2(lean_object* v___f_540_, lean_object* v_____x_541_){
_start:
{
lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; 
v_fst_542_ = lean_ctor_get(v_____x_541_, 0);
lean_inc(v_fst_542_);
v_snd_543_ = lean_ctor_get(v_____x_541_, 1);
lean_inc(v_snd_543_);
lean_dec_ref(v_____x_541_);
v___x_544_ = lean_apply_2(v___f_540_, v_fst_542_, v_snd_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(lean_object* v_toPure_548_, lean_object* v_toBind_549_, lean_object* v___f_550_, lean_object* v_____x_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0));
v___x_553_ = lean_apply_2(v_toPure_548_, lean_box(0), v___x_552_);
v___x_554_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v___x_553_, v___f_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed(lean_object* v_toPure_555_, lean_object* v_toBind_556_, lean_object* v___f_557_, lean_object* v_____x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(v_toPure_555_, v_toBind_556_, v___f_557_, v_____x_558_);
lean_dec_ref(v_____x_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4(lean_object* v_snd_560_, lean_object* v_toPure_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_a_562_);
lean_ctor_set(v___x_563_, 1, v_snd_560_);
v___x_564_ = lean_apply_2(v_toPure_561_, lean_box(0), v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5(lean_object* v___f_565_, lean_object* v_toPure_566_, lean_object* v_toBind_567_, lean_object* v_inst_568_, lean_object* v___f_569_, lean_object* v_____x_570_){
_start:
{
lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_fst_571_ = lean_ctor_get(v_____x_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v_____x_570_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v_____x_570_);
v___x_573_ = lean_unsigned_to_nat(10000u);
v___x_574_ = lean_nat_dec_le(v___x_573_, v_fst_571_);
lean_dec(v_fst_571_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v___f_569_);
lean_dec(v_inst_568_);
lean_dec(v_toBind_567_);
lean_dec(v_toPure_566_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_apply_2(v___f_565_, v___x_575_, v_snd_572_);
return v___x_576_;
}
else
{
lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___f_565_);
v___f_577_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_577_, 0, v_snd_572_);
lean_closure_set(v___f_577_, 1, v_toPure_566_);
lean_inc(v_toBind_567_);
v___x_578_ = lean_apply_4(v_toBind_567_, lean_box(0), lean_box(0), v_inst_568_, v___f_577_);
v___x_579_ = lean_apply_4(v_toBind_567_, lean_box(0), lean_box(0), v___x_578_, v___f_569_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6(lean_object* v_toPure_580_, lean_object* v_toBind_581_, lean_object* v___f_582_, lean_object* v_____x_583_){
_start:
{
lean_object* v_snd_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_593_; 
v_snd_584_ = lean_ctor_get(v_____x_583_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_____x_583_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v_____x_583_, 0);
lean_dec(v_unused_594_);
v___x_586_ = v_____x_583_;
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_584_);
lean_dec(v_____x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
lean_inc(v_snd_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_snd_584_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_snd_584_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_snd_584_);
v___x_589_ = v_reuseFailAlloc_592_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_apply_2(v_toPure_580_, lean_box(0), v___x_589_);
v___x_591_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v___x_590_, v___f_582_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(lean_object* v_f_595_, lean_object* v_toPure_596_, lean_object* v_toBind_597_, lean_object* v_inst_598_, lean_object* v_decl_599_, lean_object* v_ci_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_inc_n(v_toBind_597_, 4);
lean_inc_n(v_toPure_596_, 4);
v___f_602_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1), 7, 5);
lean_closure_set(v___f_602_, 0, v_f_595_);
lean_closure_set(v___f_602_, 1, v_decl_599_);
lean_closure_set(v___f_602_, 2, v_ci_600_);
lean_closure_set(v___f_602_, 3, v_toPure_596_);
lean_closure_set(v___f_602_, 4, v_toBind_597_);
lean_inc_ref(v___f_602_);
v___f_603_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_603_, 0, v___f_602_);
v___f_604_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_604_, 0, v_toPure_596_);
lean_closure_set(v___f_604_, 1, v_toBind_597_);
lean_closure_set(v___f_604_, 2, v___f_603_);
v___f_605_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_605_, 0, v___f_602_);
lean_closure_set(v___f_605_, 1, v_toPure_596_);
lean_closure_set(v___f_605_, 2, v_toBind_597_);
lean_closure_set(v___f_605_, 3, v_inst_598_);
lean_closure_set(v___f_605_, 4, v___f_604_);
v___f_606_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_606_, 0, v_toPure_596_);
lean_closure_set(v___f_606_, 1, v_toBind_597_);
lean_closure_set(v___f_606_, 2, v___f_605_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v___y_601_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_apply_2(v_toPure_596_, lean_box(0), v___x_610_);
v___x_612_ = lean_apply_4(v_toBind_597_, lean_box(0), lean_box(0), v___x_611_, v___f_606_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed(lean_object* v_f_613_, lean_object* v_toPure_614_, lean_object* v_toBind_615_, lean_object* v_inst_616_, lean_object* v_decl_617_, lean_object* v_ci_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(v_f_613_, v_toPure_614_, v_toBind_615_, v_inst_616_, v_decl_617_, v_ci_618_, v___y_619_);
lean_dec(v___y_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(lean_object* v_toPure_621_, lean_object* v_____x_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_apply_2(v_toPure_621_, lean_box(0), v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed(lean_object* v_toPure_625_, lean_object* v_____x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(v_toPure_625_, v_____x_626_);
lean_dec_ref(v_____x_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_f_632_){
_start:
{
lean_object* v_toApplicative_633_; lean_object* v_toBind_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_getEnv_645_; lean_object* v_modifyEnv_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_664_; 
v_toApplicative_633_ = lean_ctor_get(v_inst_628_, 0);
lean_inc_ref(v_toApplicative_633_);
v_toBind_634_ = lean_ctor_get(v_inst_628_, 1);
lean_inc(v_toBind_634_);
lean_inc_ref_n(v_inst_628_, 7);
v___f_635_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_635_, 0, v_inst_628_);
v___f_636_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_636_, 0, v_inst_628_);
v___f_637_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_637_, 0, v_inst_628_);
v___f_638_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_638_, 0, v_inst_628_);
v___x_639_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_639_, 0, lean_box(0));
lean_closure_set(v___x_639_, 1, lean_box(0));
lean_closure_set(v___x_639_, 2, v_inst_628_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___f_635_);
v___x_641_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v_inst_628_);
v___x_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_ctor_set(v___x_642_, 2, v___f_636_);
lean_ctor_set(v___x_642_, 3, v___f_637_);
lean_ctor_set(v___x_642_, 4, v___f_638_);
v___x_643_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_643_, 0, lean_box(0));
lean_closure_set(v___x_643_, 1, lean_box(0));
lean_closure_set(v___x_643_, 2, v_inst_628_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v_getEnv_645_ = lean_ctor_get(v_inst_629_, 0);
v_modifyEnv_646_ = lean_ctor_get(v_inst_629_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_inst_629_);
if (v_isSharedCheck_664_ == 0)
{
v___x_648_ = v_inst_629_;
v_isShared_649_ = v_isSharedCheck_664_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_modifyEnv_646_);
lean_inc(v_getEnv_645_);
lean_dec(v_inst_629_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_664_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
lean_inc_ref(v_inst_628_);
v___x_650_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, lean_box(0));
lean_closure_set(v___x_650_, 2, v_inst_628_);
lean_inc_ref(v___x_650_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_651_, 0, v_modifyEnv_646_);
lean_closure_set(v___f_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_652_, 0, lean_box(0));
lean_closure_set(v___x_652_, 1, lean_box(0));
lean_closure_set(v___x_652_, 2, v_inst_628_);
lean_closure_set(v___x_652_, 3, lean_box(0));
lean_closure_set(v___x_652_, 4, v_getEnv_645_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___f_651_);
lean_ctor_set(v___x_648_, 0, v___x_652_);
v___x_654_ = v___x_648_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___f_651_);
v___x_654_ = v_reuseFailAlloc_663_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_449__overap_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_toPure_655_ = lean_ctor_get(v_toApplicative_633_, 1);
lean_inc_n(v_toPure_655_, 2);
lean_dec_ref(v_toApplicative_633_);
lean_inc(v_toBind_634_);
v___f_656_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_656_, 0, v_f_632_);
lean_closure_set(v___f_656_, 1, v_toPure_655_);
lean_closure_set(v___f_656_, 2, v_toBind_634_);
lean_closure_set(v___f_656_, 3, v_inst_631_);
v___f_657_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_657_, 0, v_inst_630_);
lean_closure_set(v___f_657_, 1, v___x_650_);
v___f_658_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_658_, 0, v_toPure_655_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_449__overap_660_ = l_Lean_Server_Completion_forEligibleDeclsM___redArg(v___x_644_, v___x_654_, v___f_657_, v___f_656_);
v___x_661_ = lean_apply_1(v___x_449__overap_660_, v___x_659_);
v___x_662_ = lean_apply_4(v_toBind_634_, lean_box(0), lean_box(0), v___x_661_, v___f_658_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM(lean_object* v_m_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_f_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(v_inst_666_, v_inst_667_, v_inst_668_, v_inst_669_, v_f_670_);
return v___x_671_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object* v_id_672_, lean_object* v_declName_673_, uint8_t v_danglingDot_674_){
_start:
{
if (v_danglingDot_674_ == 0)
{
if (lean_obj_tag(v_id_672_) == 1)
{
lean_object* v_pre_675_; 
v_pre_675_ = lean_ctor_get(v_id_672_, 0);
if (lean_obj_tag(v_pre_675_) == 0)
{
if (lean_obj_tag(v_declName_673_) == 1)
{
lean_object* v_pre_676_; 
v_pre_676_ = lean_ctor_get(v_declName_673_, 0);
if (lean_obj_tag(v_pre_676_) == 0)
{
lean_object* v_str_677_; lean_object* v_str_678_; uint8_t v___x_679_; 
v_str_677_ = lean_ctor_get(v_id_672_, 1);
v_str_678_ = lean_ctor_get(v_declName_673_, 1);
v___x_679_ = l_String_charactersIn(v_str_677_, v_str_678_);
return v___x_679_;
}
else
{
return v_danglingDot_674_;
}
}
else
{
return v_danglingDot_674_;
}
}
else
{
return v_danglingDot_674_;
}
}
else
{
return v_danglingDot_674_;
}
}
else
{
uint8_t v___x_680_; 
v___x_680_ = 0;
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object* v_id_681_, lean_object* v_declName_682_, lean_object* v_danglingDot_683_){
_start:
{
uint8_t v_danglingDot_boxed_684_; uint8_t v_res_685_; lean_object* v_r_686_; 
v_danglingDot_boxed_684_ = lean_unbox(v_danglingDot_683_);
v_res_685_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_681_, v_declName_682_, v_danglingDot_boxed_684_);
lean_dec(v_declName_682_);
lean_dec(v_id_681_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(lean_object* v_msg_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0));
v___x_692_ = lean_panic_fn_borrowed(v___x_691_, v_msg_690_);
return v___x_692_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2));
v___x_697_ = lean_unsigned_to_nat(26u);
v___x_698_ = lean_unsigned_to_nat(177u);
v___x_699_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1));
v___x_700_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0));
v___x_701_ = l_mkPanicMessageWithDecl(v___x_700_, v___x_699_, v___x_698_, v___x_697_, v___x_696_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object* v_newLen_702_, lean_object* v_id_703_){
_start:
{
switch(lean_obj_tag(v_id_703_))
{
case 0:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_newLen_702_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_id_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
return v___x_705_;
}
case 1:
{
lean_object* v_pre_706_; lean_object* v_str_707_; lean_object* v___x_708_; lean_object* v_snd_709_; lean_object* v___y_711_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_pre_706_ = lean_ctor_get(v_id_703_, 0);
v_str_707_ = lean_ctor_get(v_id_703_, 1);
lean_inc(v_pre_706_);
lean_inc(v_newLen_702_);
v___x_708_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_702_, v_pre_706_);
v_snd_709_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_snd_709_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_add(v_snd_709_, v___x_723_);
v___x_725_ = lean_nat_dec_le(v_newLen_702_, v___x_724_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; 
lean_dec_ref(v___x_708_);
v___x_726_ = l_Lean_Name_isAnonymous(v_pre_706_);
if (v___x_726_ == 0)
{
v___y_711_ = v___x_723_;
goto v___jp_710_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___y_711_ = v___x_727_;
goto v___jp_710_;
}
}
else
{
lean_dec(v_snd_709_);
lean_dec_ref(v_id_703_);
lean_dec(v_newLen_702_);
return v___x_708_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_len_x27_714_; uint8_t v___x_715_; 
v___x_712_ = lean_nat_add(v_snd_709_, v___y_711_);
v___x_713_ = lean_string_length(v_str_707_);
v_len_x27_714_ = lean_nat_add(v___x_712_, v___x_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_nat_dec_le(v_len_x27_714_, v_newLen_702_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_inc_ref(v_str_707_);
lean_inc(v_pre_706_);
lean_dec(v_len_x27_714_);
lean_dec_ref(v_id_703_);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_nat_sub(v_newLen_702_, v___y_711_);
v___x_718_ = lean_nat_sub(v___x_717_, v_snd_709_);
lean_dec(v_snd_709_);
lean_dec(v___x_717_);
v___x_719_ = lean_string_utf8_extract(v_str_707_, v___x_716_, v___x_718_);
lean_dec(v___x_718_);
lean_dec_ref(v_str_707_);
v___x_720_ = l_Lean_Name_str___override(v_pre_706_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_newLen_702_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
lean_dec(v_snd_709_);
lean_dec(v_newLen_702_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_id_703_);
lean_ctor_set(v___x_722_, 1, v_len_x27_714_);
return v___x_722_;
}
}
}
default: 
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_id_703_);
lean_dec(v_newLen_702_);
v___x_728_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3);
v___x_729_ = l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(v___x_728_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object* v_id_730_, lean_object* v_newLen_731_){
_start:
{
lean_object* v___x_732_; lean_object* v_fst_733_; 
v___x_732_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_731_, v_id_730_);
v_fst_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_fst_733_);
lean_dec_ref(v___x_732_);
return v_fst_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(lean_object* v_matchUsingNamespace_734_, lean_object* v_ns_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
if (lean_obj_tag(v_ns_735_) == 1)
{
lean_object* v_pre_745_; lean_object* v___x_746_; 
v_pre_745_ = lean_ctor_get(v_ns_735_, 0);
lean_inc(v_pre_745_);
lean_inc_ref(v_matchUsingNamespace_734_);
lean_inc(v_a_743_);
lean_inc_ref(v_a_742_);
lean_inc(v_a_741_);
lean_inc_ref(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
v___x_746_ = lean_apply_10(v_matchUsingNamespace_734_, v_ns_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, lean_box(0));
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
if (lean_obj_tag(v_a_747_) == 0)
{
lean_dec_ref(v_a_747_);
lean_dec(v_pre_745_);
lean_dec_ref(v_matchUsingNamespace_734_);
return v___x_746_;
}
else
{
lean_object* v_a_748_; lean_object* v_snd_749_; 
lean_dec_ref(v___x_746_);
v_a_748_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v_a_747_);
v_snd_749_ = lean_ctor_get(v_a_748_, 1);
lean_inc(v_snd_749_);
lean_dec(v_a_748_);
v_ns_735_ = v_pre_745_;
v_a_736_ = v_snd_749_;
goto _start;
}
}
else
{
lean_dec(v_pre_745_);
lean_dec_ref(v_matchUsingNamespace_734_);
return v___x_746_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_ns_735_);
lean_dec_ref(v_matchUsingNamespace_734_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v_a_736_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces___boxed(lean_object* v_matchUsingNamespace_755_, lean_object* v_ns_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_755_, v_ns_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(lean_object* v_id_767_, uint8_t v_danglingDot_768_, lean_object* v_declName_769_, lean_object* v_ns_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_802_; 
v___x_780_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_770_, v_id_767_, v_danglingDot_768_, v_declName_769_, v___y_778_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_802_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_802_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_802_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
if (lean_obj_tag(v_a_781_) == 1)
{
lean_object* v_val_785_; lean_object* v___x_786_; lean_object* v___y_788_; 
v_val_785_ = lean_ctor_get(v_a_781_, 0);
v___x_786_ = lean_box(0);
if (lean_obj_tag(v___y_771_) == 0)
{
v___y_788_ = v_a_781_;
goto v___jp_787_;
}
else
{
lean_object* v_val_794_; uint8_t v___x_795_; 
v_val_794_ = lean_ctor_get(v___y_771_, 0);
v___x_795_ = l_Lean_Name_isSuffixOf(v_val_785_, v_val_794_);
if (v___x_795_ == 0)
{
lean_dec_ref(v_a_781_);
v___y_788_ = v___y_771_;
goto v___jp_787_;
}
else
{
lean_dec_ref(v___y_771_);
v___y_788_ = v_a_781_;
goto v___jp_787_;
}
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___y_788_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_790_);
v___x_792_ = v___x_783_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_a_781_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___y_771_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_798_);
v___x_800_ = v___x_783_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed(lean_object* v_id_803_, lean_object* v_danglingDot_804_, lean_object* v_declName_805_, lean_object* v_ns_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v_danglingDot_boxed_816_; lean_object* v_res_817_; 
v_danglingDot_boxed_816_ = lean_unbox(v_danglingDot_804_);
v_res_817_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_803_, v_danglingDot_boxed_816_, v_declName_805_, v_ns_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v_ns_806_);
lean_dec(v_id_803_);
return v_res_817_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
else
{
lean_object* v_head_821_; lean_object* v_tail_822_; uint8_t v___x_823_; 
v_head_821_ = lean_ctor_get(v_x_819_, 0);
v_tail_822_ = lean_ctor_get(v_x_819_, 1);
v___x_823_ = lean_name_eq(v_a_818_, v_head_821_);
if (v___x_823_ == 0)
{
v_x_819_ = v_tail_822_;
goto _start;
}
else
{
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0___boxed(lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(lean_object* v_declName_829_, lean_object* v_id_830_, uint8_t v_danglingDot_831_, lean_object* v_as_x27_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
if (lean_obj_tag(v_as_x27_832_) == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_declName_829_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_b_833_);
lean_ctor_set(v___x_837_, 1, v___y_834_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
else
{
lean_object* v_head_840_; lean_object* v_tail_841_; lean_object* v___x_842_; 
v_head_840_ = lean_ctor_get(v_as_x27_832_, 0);
v_tail_841_ = lean_ctor_get(v_as_x27_832_, 1);
v___x_842_ = lean_box(0);
if (lean_obj_tag(v_head_840_) == 0)
{
lean_object* v_ns_843_; lean_object* v_except_844_; uint8_t v___x_845_; 
v_ns_843_ = lean_ctor_get(v_head_840_, 0);
v_except_844_ = lean_ctor_get(v_head_840_, 1);
v___x_845_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_829_, v_except_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v_a_847_; 
lean_inc(v_declName_829_);
v___x_846_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_843_, v_id_830_, v_danglingDot_831_, v_declName_829_, v___y_835_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
if (lean_obj_tag(v_a_847_) == 1)
{
if (lean_obj_tag(v___y_834_) == 0)
{
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
v___y_834_ = v_a_847_;
goto _start;
}
else
{
lean_object* v_val_849_; lean_object* v_val_850_; uint8_t v___x_851_; 
v_val_849_ = lean_ctor_get(v_a_847_, 0);
v_val_850_ = lean_ctor_get(v___y_834_, 0);
v___x_851_ = l_Lean_Name_isSuffixOf(v_val_849_, v_val_850_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_a_847_);
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
goto _start;
}
else
{
lean_dec_ref(v___y_834_);
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
v___y_834_ = v_a_847_;
goto _start;
}
}
}
else
{
lean_dec(v_a_847_);
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
goto _start;
}
}
else
{
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
goto _start;
}
}
else
{
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_declName_857_, lean_object* v_id_858_, lean_object* v_danglingDot_859_, lean_object* v_as_x27_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v_danglingDot_boxed_865_; lean_object* v_res_866_; 
v_danglingDot_boxed_865_ = lean_unbox(v_danglingDot_859_);
v_res_866_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_857_, v_id_858_, v_danglingDot_boxed_865_, v_as_x27_860_, v_b_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec(v_as_x27_860_);
lean_dec(v_id_858_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(lean_object* v_declName_867_, lean_object* v_id_868_, uint8_t v_danglingDot_869_, lean_object* v_as_870_, lean_object* v_as_x27_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
if (lean_obj_tag(v_as_x27_871_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v_declName_867_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_b_872_);
lean_ctor_set(v___x_882_, 1, v___y_873_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; lean_object* v___x_887_; 
v_head_885_ = lean_ctor_get(v_as_x27_871_, 0);
v_tail_886_ = lean_ctor_get(v_as_x27_871_, 1);
v___x_887_ = lean_box(0);
if (lean_obj_tag(v_head_885_) == 0)
{
lean_object* v_ns_888_; lean_object* v_except_889_; uint8_t v___x_890_; 
v_ns_888_ = lean_ctor_get(v_head_885_, 0);
v_except_889_ = lean_ctor_get(v_head_885_, 1);
v___x_890_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_867_, v_except_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v_a_892_; 
lean_inc(v_declName_867_);
v___x_891_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_888_, v_id_868_, v_danglingDot_869_, v_declName_867_, v___y_880_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
if (lean_obj_tag(v_a_892_) == 1)
{
if (lean_obj_tag(v___y_873_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v_a_892_, v___y_880_);
return v___x_893_;
}
else
{
lean_object* v_val_894_; lean_object* v_val_895_; uint8_t v___x_896_; 
v_val_894_ = lean_ctor_get(v_a_892_, 0);
v_val_895_ = lean_ctor_get(v___y_873_, 0);
v___x_896_ = l_Lean_Name_isSuffixOf(v_val_894_, v_val_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec_ref(v_a_892_);
v___x_897_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v___y_873_, v___y_880_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; 
lean_dec_ref(v___y_873_);
v___x_898_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v_a_892_, v___y_880_);
return v___x_898_;
}
}
}
else
{
lean_object* v___x_899_; 
lean_dec(v_a_892_);
v___x_899_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v___y_873_, v___y_880_);
return v___x_899_;
}
}
else
{
lean_object* v___x_900_; 
v___x_900_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v___y_873_, v___y_880_);
return v___x_900_;
}
}
else
{
lean_object* v___x_901_; 
v___x_901_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v___y_873_, v___y_880_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg___boxed(lean_object* v_declName_902_, lean_object* v_id_903_, lean_object* v_danglingDot_904_, lean_object* v_as_905_, lean_object* v_as_x27_906_, lean_object* v_b_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_danglingDot_boxed_917_; lean_object* v_res_918_; 
v_danglingDot_boxed_917_ = lean_unbox(v_danglingDot_904_);
v_res_918_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_902_, v_id_903_, v_danglingDot_boxed_917_, v_as_905_, v_as_x27_906_, v_b_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v_as_x27_906_);
lean_dec(v_as_905_);
lean_dec(v_id_903_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(lean_object* v_ctx_919_, lean_object* v_declName_920_, lean_object* v_id_921_, uint8_t v_danglingDot_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___y_932_; lean_object* v_toCommandContextInfo_969_; lean_object* v_currNamespace_970_; lean_object* v_openDecls_971_; lean_object* v___x_972_; lean_object* v_matchUsingNamespace_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_toCommandContextInfo_969_ = lean_ctor_get(v_ctx_919_, 0);
lean_inc_ref(v_toCommandContextInfo_969_);
lean_dec_ref(v_ctx_919_);
v_currNamespace_970_ = lean_ctor_get(v_toCommandContextInfo_969_, 5);
lean_inc(v_currNamespace_970_);
v_openDecls_971_ = lean_ctor_get(v_toCommandContextInfo_969_, 6);
lean_inc(v_openDecls_971_);
lean_dec_ref(v_toCommandContextInfo_969_);
v___x_972_ = lean_box(v_danglingDot_922_);
lean_inc(v_declName_920_);
lean_inc(v_id_921_);
v_matchUsingNamespace_973_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v_matchUsingNamespace_973_, 0, v_id_921_);
lean_closure_set(v_matchUsingNamespace_973_, 1, v___x_972_);
lean_closure_set(v_matchUsingNamespace_973_, 2, v_declName_920_);
v___x_974_ = lean_box(0);
v___x_975_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_973_, v_currNamespace_970_, v___x_974_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
if (lean_obj_tag(v_a_976_) == 0)
{
lean_dec_ref(v_a_976_);
lean_dec(v_openDecls_971_);
lean_dec(v_id_921_);
lean_dec(v_declName_920_);
v___y_932_ = v___x_975_;
goto v___jp_931_;
}
else
{
lean_object* v_a_977_; lean_object* v_snd_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v___x_975_);
v_a_977_ = lean_ctor_get(v_a_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v_a_976_);
v_snd_978_ = lean_ctor_get(v_a_977_, 1);
lean_inc(v_snd_978_);
lean_dec(v_a_977_);
v___x_979_ = lean_box(0);
lean_inc(v_declName_920_);
v___x_980_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_920_, v_id_921_, v_danglingDot_922_, v_openDecls_971_, v_openDecls_971_, v___x_979_, v_snd_978_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_openDecls_971_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v_snd_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v_a_982_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_a_982_);
lean_dec(v_a_981_);
v_snd_983_ = lean_ctor_get(v_a_982_, 1);
lean_inc(v_snd_983_);
lean_dec(v_a_982_);
v___x_984_ = lean_box(0);
v___x_985_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_921_, v_danglingDot_922_, v_declName_920_, v___x_984_, v_snd_983_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_id_921_);
v___y_932_ = v___x_985_;
goto v___jp_931_;
}
else
{
lean_dec(v_id_921_);
lean_dec(v_declName_920_);
v___y_932_ = v___x_980_;
goto v___jp_931_;
}
}
}
else
{
lean_dec(v_openDecls_971_);
lean_dec(v_id_921_);
lean_dec(v_declName_920_);
v___y_932_ = v___x_975_;
goto v___jp_931_;
}
v___jp_931_:
{
if (lean_obj_tag(v___y_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_960_; 
v_a_933_ = lean_ctor_get(v___y_932_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___y_932_);
if (v_isSharedCheck_960_ == 0)
{
v___x_935_ = v___y_932_;
v_isShared_936_ = v_isSharedCheck_960_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___y_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_960_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_a_933_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v_a_937_ = lean_ctor_get(v_a_933_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v_a_933_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v_a_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_942_);
v___x_944_ = v___x_935_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_959_; 
v_a_948_ = lean_ctor_get(v_a_933_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_959_ == 0)
{
v___x_950_ = v_a_933_;
v_isShared_951_ = v_isSharedCheck_959_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v_a_933_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_959_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_snd_952_; lean_object* v___x_954_; 
v_snd_952_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_snd_952_);
lean_dec(v_a_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_snd_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_snd_952_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_954_);
v___x_956_ = v___x_935_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___y_932_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___y_932_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___y_932_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___y_932_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___boxed(lean_object* v_ctx_986_, lean_object* v_declName_987_, lean_object* v_id_988_, lean_object* v_danglingDot_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
uint8_t v_danglingDot_boxed_998_; lean_object* v_res_999_; 
v_danglingDot_boxed_998_ = lean_unbox(v_danglingDot_989_);
v_res_999_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_986_, v_declName_987_, v_id_988_, v_danglingDot_boxed_998_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(lean_object* v_declName_1000_, lean_object* v_id_1001_, uint8_t v_danglingDot_1002_, lean_object* v_as_1003_, lean_object* v_as_x27_1004_, lean_object* v_b_1005_, lean_object* v_a_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_1000_, v_id_1001_, v_danglingDot_1002_, v_as_1003_, v_as_x27_1004_, v_b_1005_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___boxed(lean_object* v_declName_1017_, lean_object* v_id_1018_, lean_object* v_danglingDot_1019_, lean_object* v_as_1020_, lean_object* v_as_x27_1021_, lean_object* v_b_1022_, lean_object* v_a_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v_danglingDot_boxed_1033_; lean_object* v_res_1034_; 
v_danglingDot_boxed_1033_ = lean_unbox(v_danglingDot_1019_);
v_res_1034_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(v_declName_1017_, v_id_1018_, v_danglingDot_boxed_1033_, v_as_1020_, v_as_x27_1021_, v_b_1022_, v_a_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v_as_x27_1021_);
lean_dec(v_as_1020_);
lean_dec(v_id_1018_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(lean_object* v_declName_1035_, lean_object* v_id_1036_, uint8_t v_danglingDot_1037_, lean_object* v_as_1038_, lean_object* v_as_x27_1039_, lean_object* v_b_1040_, lean_object* v_a_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_1035_, v_id_1036_, v_danglingDot_1037_, v_as_x27_1039_, v_b_1040_, v___y_1042_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___boxed(lean_object* v_declName_1052_, lean_object* v_id_1053_, lean_object* v_danglingDot_1054_, lean_object* v_as_1055_, lean_object* v_as_x27_1056_, lean_object* v_b_1057_, lean_object* v_a_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v_danglingDot_boxed_1068_; lean_object* v_res_1069_; 
v_danglingDot_boxed_1068_ = lean_unbox(v_danglingDot_1054_);
v_res_1069_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(v_declName_1052_, v_id_1053_, v_danglingDot_boxed_1068_, v_as_1055_, v_as_x27_1056_, v_b_1057_, v_a_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v_as_x27_1056_);
lean_dec(v_as_1055_);
lean_dec(v_id_1053_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object* v_ctx_1070_, lean_object* v_id_1071_, uint8_t v_danglingDot_1072_, lean_object* v___x_1073_, lean_object* v_a_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_it_1085_; lean_object* v_a_1089_; lean_object* v___x_1092_; lean_object* v___y_1094_; lean_object* v___y_1095_; uint8_t v___y_1096_; lean_object* v_it_1117_; lean_object* v_fst_1118_; lean_object* v_it_1123_; lean_object* v_fst_1124_; 
v___x_1092_ = lean_box(0);
if (lean_obj_tag(v_a_1074_) == 0)
{
lean_object* v_a_1126_; lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1194_; 
v_a_1126_ = lean_ctor_get(v_a_1074_, 0);
v_a_1127_ = lean_ctor_get(v_a_1074_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_a_1074_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1129_ = v_a_1074_;
v_isShared_1130_ = v_isSharedCheck_1194_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
lean_dec(v_a_1074_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1194_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_it_1132_; lean_object* v_it_u2082_1137_; 
v_it_u2082_1137_ = lean_ctor_get(v_a_1126_, 1);
lean_inc(v_it_u2082_1137_);
if (lean_obj_tag(v_it_u2082_1137_) == 0)
{
lean_object* v_it_u2081_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1162_; 
v_it_u2081_1138_ = lean_ctor_get(v_a_1126_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_a_1126_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_a_1126_, 1);
lean_dec(v_unused_1163_);
v___x_1140_ = v_a_1126_;
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_it_u2081_1138_);
lean_dec(v_a_1126_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_array_1142_; lean_object* v_pos_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1161_; 
v_array_1142_ = lean_ctor_get(v_it_u2081_1138_, 0);
v_pos_1143_ = lean_ctor_get(v_it_u2081_1138_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_it_u2081_1138_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1145_ = v_it_u2081_1138_;
v_isShared_1146_ = v_isSharedCheck_1161_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_pos_1143_);
lean_inc(v_array_1142_);
lean_dec(v_it_u2081_1138_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1161_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_array_get_size(v_array_1142_);
v___x_1148_ = lean_nat_dec_lt(v_pos_1143_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_del_object(v___x_1145_);
lean_dec(v_pos_1143_);
lean_dec_ref(v_array_1142_);
lean_del_object(v___x_1140_);
lean_del_object(v___x_1129_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_a_1127_);
v_a_1074_ = v___x_1149_;
goto _start;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_pos_1143_, v___x_1151_);
lean_inc_ref(v_array_1142_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1152_);
v___x_1154_ = v___x_1145_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_array_1142_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1155_ = lean_array_fget(v_array_1142_, v_pos_1143_);
lean_dec(v_pos_1143_);
lean_dec_ref(v_array_1142_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1156_);
lean_ctor_set(v___x_1140_, 0, v___x_1154_);
v___x_1158_ = v___x_1140_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
v_it_1132_ = v___x_1158_;
goto v___jp_1131_;
}
}
}
}
}
}
else
{
lean_object* v_val_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1193_; 
v_val_1164_ = lean_ctor_get(v_it_u2082_1137_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_it_u2082_1137_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1166_ = v_it_u2082_1137_;
v_isShared_1167_ = v_isSharedCheck_1193_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_val_1164_);
lean_dec(v_it_u2082_1137_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1193_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
if (lean_obj_tag(v_val_1164_) == 0)
{
lean_object* v_it_u2081_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1176_; 
lean_del_object(v___x_1166_);
v_it_u2081_1168_ = lean_ctor_get(v_a_1126_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_a_1126_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v_a_1126_, 1);
lean_dec(v_unused_1177_);
v___x_1170_ = v_a_1126_;
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_it_u2081_1168_);
lean_dec(v_a_1126_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_box(0);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1172_);
v___x_1174_ = v___x_1170_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_it_u2081_1168_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v_it_1132_ = v___x_1174_;
goto v___jp_1131_;
}
}
}
else
{
lean_object* v_it_u2081_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1191_; 
lean_del_object(v___x_1129_);
v_it_u2081_1178_ = lean_ctor_get(v_a_1126_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_a_1126_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_a_1126_, 1);
lean_dec(v_unused_1192_);
v___x_1180_ = v_a_1126_;
v_isShared_1181_ = v_isSharedCheck_1191_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_it_u2081_1178_);
lean_dec(v_a_1126_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1191_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_key_1182_; lean_object* v_tail_1183_; lean_object* v___x_1185_; 
v_key_1182_ = lean_ctor_get(v_val_1164_, 0);
lean_inc(v_key_1182_);
v_tail_1183_ = lean_ctor_get(v_val_1164_, 2);
lean_inc(v_tail_1183_);
lean_dec_ref(v_val_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_tail_1183_);
v___x_1185_ = v___x_1166_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_tail_1183_);
v___x_1185_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1185_);
v___x_1187_ = v___x_1180_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_it_u2081_1178_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v_a_1127_);
v_it_1117_ = v___x_1188_;
v_fst_1118_ = v_key_1182_;
goto v___jp_1116_;
}
}
}
}
}
}
v___jp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_it_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_it_1132_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_a_1127_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v_a_1074_ = v___x_1134_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1195_; 
v_a_1195_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v_a_1074_);
switch(lean_obj_tag(v_a_1195_))
{
case 0:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_b_1075_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
case 1:
{
lean_object* v_a_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1217_; 
v_a_1198_ = lean_ctor_get(v_a_1195_, 0);
v_a_1199_ = lean_ctor_get(v_a_1195_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1195_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1201_ = v_a_1195_;
v_isShared_1202_ = v_isSharedCheck_1217_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_inc(v_a_1198_);
lean_dec(v_a_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1217_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_start_1203_; lean_object* v_stop_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_start_1203_ = lean_ctor_get(v_a_1198_, 1);
v_stop_1204_ = lean_ctor_get(v_a_1198_, 2);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_nat_sub(v_stop_1204_, v_start_1203_);
v___x_1207_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
lean_dec(v___x_1206_);
if (v___x_1207_ == 0)
{
lean_del_object(v___x_1201_);
lean_dec_ref(v_a_1198_);
v_it_1085_ = v_a_1199_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_z_1211_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_1198_);
v___x_1209_ = l_Subarray_drop___redArg(v_a_1198_, v___x_1208_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1209_);
v_z_1211_ = v___x_1201_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_a_1199_);
v_z_1211_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Subarray_get___redArg(v_a_1198_, v___x_1205_);
lean_dec_ref(v_a_1198_);
switch(lean_obj_tag(v___x_1212_))
{
case 0:
{
lean_object* v_key_1213_; 
v_key_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_key_1213_);
lean_dec_ref(v___x_1212_);
v_it_1123_ = v_z_1211_;
v_fst_1124_ = v_key_1213_;
goto v___jp_1122_;
}
case 1:
{
lean_object* v_node_1214_; lean_object* v___x_1215_; 
v_node_1214_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_node_1214_);
lean_dec_ref(v___x_1212_);
v___x_1215_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1214_, v_z_1211_);
v_it_1085_ = v___x_1215_;
goto v___jp_1084_;
}
default: 
{
v_it_1085_ = v_z_1211_;
goto v___jp_1084_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_1218_; lean_object* v_keys_1219_; lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1236_; 
v_vals_1218_ = lean_ctor_get(v_a_1195_, 1);
v_keys_1219_ = lean_ctor_get(v_a_1195_, 0);
v_a_1220_ = lean_ctor_get(v_a_1195_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_a_1195_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1222_ = v_a_1195_;
v_isShared_1223_ = v_isSharedCheck_1236_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_inc(v_vals_1218_);
lean_inc(v_keys_1219_);
lean_dec(v_a_1195_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1236_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_start_1224_; lean_object* v_stop_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_start_1224_ = lean_ctor_get(v_vals_1218_, 1);
v_stop_1225_ = lean_ctor_get(v_vals_1218_, 2);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_nat_sub(v_stop_1225_, v_start_1224_);
v___x_1228_ = lean_nat_dec_lt(v___x_1226_, v___x_1227_);
lean_dec(v___x_1227_);
if (v___x_1228_ == 0)
{
lean_del_object(v___x_1222_);
lean_dec_ref(v_keys_1219_);
lean_dec_ref(v_vals_1218_);
v_it_1085_ = v_a_1220_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1229_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_1219_);
v___x_1230_ = l_Subarray_drop___redArg(v_keys_1219_, v___x_1229_);
v___x_1231_ = l_Subarray_drop___redArg(v_vals_1218_, v___x_1229_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v___x_1231_);
lean_ctor_set(v___x_1222_, 0, v___x_1230_);
v___x_1233_ = v___x_1222_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_a_1220_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Subarray_get___redArg(v_keys_1219_, v___x_1226_);
lean_dec_ref(v_keys_1219_);
v_it_1123_ = v___x_1233_;
v_fst_1124_ = v___x_1234_;
goto v___jp_1122_;
}
}
}
}
}
}
v___jp_1084_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_it_1085_);
v_a_1074_ = v___x_1086_;
goto _start;
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_a_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
v___jp_1093_:
{
if (v___y_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_inc(v_id_1071_);
lean_inc_ref(v_ctx_1070_);
v___x_1097_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_1070_, v___y_1094_, v_id_1071_, v_danglingDot_1072_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v___x_1097_);
if (lean_obj_tag(v_a_1098_) == 0)
{
lean_object* v_a_1099_; 
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v_a_1099_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref(v_a_1098_);
v_a_1089_ = v_a_1099_;
goto v___jp_1088_;
}
else
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v_a_1098_);
if (lean_obj_tag(v_a_1100_) == 1)
{
lean_object* v_val_1101_; lean_object* v___x_1102_; 
v_val_1101_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_val_1101_);
lean_dec_ref(v_a_1100_);
v___x_1102_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_val_1101_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
if (lean_obj_tag(v_a_1103_) == 0)
{
lean_object* v_a_1104_; 
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v_a_1104_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref(v_a_1103_);
v_a_1089_ = v_a_1104_;
goto v___jp_1088_;
}
else
{
lean_dec_ref(v_a_1103_);
v_a_1074_ = v___y_1095_;
v_b_1075_ = v___x_1092_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
return v___x_1102_;
}
}
else
{
lean_dec(v_a_1100_);
v_a_1074_ = v___y_1095_;
v_b_1075_ = v___x_1092_;
goto _start;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v_a_1107_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1097_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1097_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_dec(v___y_1094_);
v_a_1074_ = v___y_1095_;
v_b_1075_ = v___x_1092_;
goto _start;
}
}
v___jp_1116_:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_Name_isInternal(v_fst_1118_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 1;
lean_inc(v_fst_1118_);
lean_inc_ref(v___x_1073_);
v___x_1121_ = l_Lean_Environment_contains(v___x_1073_, v_fst_1118_, v___x_1120_);
v___y_1094_ = v_fst_1118_;
v___y_1095_ = v_it_1117_;
v___y_1096_ = v___x_1121_;
goto v___jp_1093_;
}
else
{
v___y_1094_ = v_fst_1118_;
v___y_1095_ = v_it_1117_;
v___y_1096_ = v___x_1119_;
goto v___jp_1093_;
}
}
v___jp_1122_:
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_it_1123_);
v_it_1117_ = v___x_1125_;
v_fst_1118_ = v_fst_1124_;
goto v___jp_1116_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object* v_ctx_1237_, lean_object* v_id_1238_, lean_object* v_danglingDot_1239_, lean_object* v___x_1240_, lean_object* v_a_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v_danglingDot_boxed_1251_; lean_object* v_res_1252_; 
v_danglingDot_boxed_1251_ = lean_unbox(v_danglingDot_1239_);
v_res_1252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1237_, v_id_1238_, v_danglingDot_boxed_1251_, v___x_1240_, v_a_1241_, v_b_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object* v_ctx_1253_, lean_object* v_id_1254_, uint8_t v_danglingDot_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_env_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1264_ = lean_st_ref_get(v_a_1262_);
v_env_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc_ref_n(v_env_1265_, 2);
lean_dec(v___x_1264_);
v___x_1266_ = l_Lean_Environment_getNamespaces(v_env_1265_);
v___x_1267_ = lean_box(0);
v___x_1268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1253_, v_id_1254_, v_danglingDot_1255_, v_env_1265_, v___x_1266_, v___x_1267_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
if (lean_obj_tag(v_a_1269_) == 0)
{
lean_dec_ref(v_a_1269_);
return v___x_1268_;
}
else
{
lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_a_1269_);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1268_, 0);
lean_dec(v_unused_1278_);
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object* v_ctx_1279_, lean_object* v_id_1280_, lean_object* v_danglingDot_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_danglingDot_boxed_1290_; lean_object* v_res_1291_; 
v_danglingDot_boxed_1290_ = lean_unbox(v_danglingDot_1281_);
v_res_1291_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1279_, v_id_1280_, v_danglingDot_boxed_1290_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object* v_ctx_1292_, lean_object* v_id_1293_, uint8_t v_danglingDot_1294_, lean_object* v___x_1295_, lean_object* v_inst_1296_, lean_object* v_R_1297_, lean_object* v_a_1298_, lean_object* v_b_1299_, lean_object* v_c_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1292_, v_id_1293_, v_danglingDot_1294_, v___x_1295_, v_a_1298_, v_b_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object** _args){
lean_object* v_ctx_1310_ = _args[0];
lean_object* v_id_1311_ = _args[1];
lean_object* v_danglingDot_1312_ = _args[2];
lean_object* v___x_1313_ = _args[3];
lean_object* v_inst_1314_ = _args[4];
lean_object* v_R_1315_ = _args[5];
lean_object* v_a_1316_ = _args[6];
lean_object* v_b_1317_ = _args[7];
lean_object* v_c_1318_ = _args[8];
lean_object* v___y_1319_ = _args[9];
lean_object* v___y_1320_ = _args[10];
lean_object* v___y_1321_ = _args[11];
lean_object* v___y_1322_ = _args[12];
lean_object* v___y_1323_ = _args[13];
lean_object* v___y_1324_ = _args[14];
lean_object* v___y_1325_ = _args[15];
lean_object* v___y_1326_ = _args[16];
_start:
{
uint8_t v_danglingDot_boxed_1327_; lean_object* v_res_1328_; 
v_danglingDot_boxed_1327_ = lean_unbox(v_danglingDot_1312_);
v_res_1328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_ctx_1310_, v_id_1311_, v_danglingDot_boxed_1327_, v___x_1313_, v_inst_1314_, v_R_1315_, v_a_1316_, v_b_1317_, v_c_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* v_n_1329_){
_start:
{
if (lean_obj_tag(v_n_1329_) == 2)
{
lean_object* v_i_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_i_1330_ = lean_ctor_get(v_n_1329_, 1);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_nat_dec_eq(v_i_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_inc_ref(v_n_1329_);
return v_n_1329_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_isPrivatePrefix(v_n_1329_);
if (v___x_1333_ == 0)
{
lean_inc_ref(v_n_1329_);
return v_n_1329_;
}
else
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_box(0);
return v___x_1334_;
}
}
}
else
{
lean_inc(v_n_1329_);
return v_n_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* v_n_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_1335_);
lean_dec(v_n_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* v_n_u2081_1337_, lean_object* v_n_u2082_1338_){
_start:
{
lean_object* v_n_u2081_1339_; lean_object* v_n_u2082_1340_; 
v_n_u2081_1339_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2081_1337_);
lean_dec(v_n_u2081_1337_);
v_n_u2082_1340_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2082_1338_);
lean_dec(v_n_u2082_1338_);
switch(lean_obj_tag(v_n_u2081_1339_))
{
case 0:
{
if (lean_obj_tag(v_n_u2082_1340_) == 0)
{
uint8_t v___x_1341_; 
v___x_1341_ = 1;
return v___x_1341_;
}
else
{
uint8_t v___x_1342_; 
lean_dec(v_n_u2082_1340_);
v___x_1342_ = 0;
return v___x_1342_;
}
}
case 1:
{
if (lean_obj_tag(v_n_u2082_1340_) == 1)
{
lean_object* v_pre_1343_; lean_object* v_str_1344_; lean_object* v_pre_1345_; lean_object* v_str_1346_; uint8_t v___x_1347_; 
v_pre_1343_ = lean_ctor_get(v_n_u2081_1339_, 0);
lean_inc(v_pre_1343_);
v_str_1344_ = lean_ctor_get(v_n_u2081_1339_, 1);
lean_inc_ref(v_str_1344_);
lean_dec_ref(v_n_u2081_1339_);
v_pre_1345_ = lean_ctor_get(v_n_u2082_1340_, 0);
lean_inc(v_pre_1345_);
v_str_1346_ = lean_ctor_get(v_n_u2082_1340_, 1);
lean_inc_ref(v_str_1346_);
lean_dec_ref(v_n_u2082_1340_);
v___x_1347_ = lean_string_dec_lt(v_str_1344_, v_str_1346_);
if (v___x_1347_ == 0)
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_string_dec_eq(v_str_1344_, v_str_1346_);
lean_dec_ref(v_str_1346_);
lean_dec_ref(v_str_1344_);
if (v___x_1348_ == 0)
{
uint8_t v___x_1349_; 
lean_dec(v_pre_1345_);
lean_dec(v_pre_1343_);
v___x_1349_ = 2;
return v___x_1349_;
}
else
{
v_n_u2081_1337_ = v_pre_1343_;
v_n_u2082_1338_ = v_pre_1345_;
goto _start;
}
}
else
{
uint8_t v___x_1351_; 
lean_dec_ref(v_str_1346_);
lean_dec(v_pre_1345_);
lean_dec_ref(v_str_1344_);
lean_dec(v_pre_1343_);
v___x_1351_ = 0;
return v___x_1351_;
}
}
else
{
uint8_t v___x_1352_; 
lean_dec_ref(v_n_u2081_1339_);
lean_dec(v_n_u2082_1340_);
v___x_1352_ = 2;
return v___x_1352_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1340_))
{
case 0:
{
uint8_t v___x_1353_; 
lean_dec_ref(v_n_u2081_1339_);
v___x_1353_ = 2;
return v___x_1353_;
}
case 1:
{
uint8_t v___x_1354_; 
lean_dec_ref(v_n_u2082_1340_);
lean_dec_ref(v_n_u2081_1339_);
v___x_1354_ = 0;
return v___x_1354_;
}
default: 
{
lean_object* v_pre_1355_; lean_object* v_i_1356_; lean_object* v_pre_1357_; lean_object* v_i_1358_; uint8_t v___x_1359_; 
v_pre_1355_ = lean_ctor_get(v_n_u2081_1339_, 0);
lean_inc(v_pre_1355_);
v_i_1356_ = lean_ctor_get(v_n_u2081_1339_, 1);
lean_inc(v_i_1356_);
lean_dec_ref(v_n_u2081_1339_);
v_pre_1357_ = lean_ctor_get(v_n_u2082_1340_, 0);
lean_inc(v_pre_1357_);
v_i_1358_ = lean_ctor_get(v_n_u2082_1340_, 1);
lean_inc(v_i_1358_);
lean_dec_ref(v_n_u2082_1340_);
v___x_1359_ = lean_nat_dec_lt(v_i_1356_, v_i_1358_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_nat_dec_eq(v_i_1356_, v_i_1358_);
lean_dec(v_i_1358_);
lean_dec(v_i_1356_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; 
lean_dec(v_pre_1357_);
lean_dec(v_pre_1355_);
v___x_1361_ = 2;
return v___x_1361_;
}
else
{
v_n_u2081_1337_ = v_pre_1355_;
v_n_u2082_1338_ = v_pre_1357_;
goto _start;
}
}
else
{
uint8_t v___x_1363_; 
lean_dec(v_i_1358_);
lean_dec(v_pre_1357_);
lean_dec(v_i_1356_);
lean_dec(v_pre_1355_);
v___x_1363_ = 0;
return v___x_1363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1364_, lean_object* v_n_u2082_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1364_, v_n_u2082_1365_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1371_ = l_Std_TreeSet_ofArray___redArg(v_names_1369_, v___x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1372_);
lean_dec_ref(v_names_1372_);
return v_res_1373_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1374_, lean_object* v_t_1375_){
_start:
{
if (lean_obj_tag(v_t_1375_) == 0)
{
lean_object* v_k_1376_; lean_object* v_l_1377_; lean_object* v_r_1378_; uint8_t v___x_1379_; 
v_k_1376_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_k_1376_);
v_l_1377_ = lean_ctor_get(v_t_1375_, 3);
lean_inc(v_l_1377_);
v_r_1378_ = lean_ctor_get(v_t_1375_, 4);
lean_inc(v_r_1378_);
lean_dec_ref(v_t_1375_);
lean_inc(v_k_1374_);
v___x_1379_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1374_, v_k_1376_);
switch(v___x_1379_)
{
case 0:
{
lean_dec(v_r_1378_);
v_t_1375_ = v_l_1377_;
goto _start;
}
case 1:
{
uint8_t v___x_1381_; 
lean_dec(v_r_1378_);
lean_dec(v_l_1377_);
lean_dec(v_k_1374_);
v___x_1381_ = 1;
return v___x_1381_;
}
default: 
{
lean_dec(v_l_1377_);
v_t_1375_ = v_r_1378_;
goto _start;
}
}
}
else
{
uint8_t v___x_1383_; 
lean_dec(v_k_1374_);
v___x_1383_ = 0;
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1384_, lean_object* v_t_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1384_, v_t_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1388_, lean_object* v_v_1389_, lean_object* v_t_1390_){
_start:
{
if (lean_obj_tag(v_t_1390_) == 0)
{
lean_object* v_size_1391_; lean_object* v_k_1392_; lean_object* v_v_1393_; lean_object* v_l_1394_; lean_object* v_r_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1675_; 
v_size_1391_ = lean_ctor_get(v_t_1390_, 0);
v_k_1392_ = lean_ctor_get(v_t_1390_, 1);
v_v_1393_ = lean_ctor_get(v_t_1390_, 2);
v_l_1394_ = lean_ctor_get(v_t_1390_, 3);
v_r_1395_ = lean_ctor_get(v_t_1390_, 4);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_t_1390_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1397_ = v_t_1390_;
v_isShared_1398_ = v_isSharedCheck_1675_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_r_1395_);
lean_inc(v_l_1394_);
lean_inc(v_v_1393_);
lean_inc(v_k_1392_);
lean_inc(v_size_1391_);
lean_dec(v_t_1390_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1675_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___x_1399_; 
lean_inc(v_k_1392_);
lean_inc(v_k_1388_);
v___x_1399_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1388_, v_k_1392_);
switch(v___x_1399_)
{
case 0:
{
lean_object* v_impl_1400_; lean_object* v___x_1401_; 
lean_dec(v_size_1391_);
v_impl_1400_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1388_, v_v_1389_, v_l_1394_);
v___x_1401_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1395_) == 0)
{
lean_object* v_size_1402_; lean_object* v_size_1403_; lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v_l_1406_; lean_object* v_r_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_size_1402_ = lean_ctor_get(v_r_1395_, 0);
v_size_1403_ = lean_ctor_get(v_impl_1400_, 0);
lean_inc(v_size_1403_);
v_k_1404_ = lean_ctor_get(v_impl_1400_, 1);
lean_inc(v_k_1404_);
v_v_1405_ = lean_ctor_get(v_impl_1400_, 2);
lean_inc(v_v_1405_);
v_l_1406_ = lean_ctor_get(v_impl_1400_, 3);
lean_inc(v_l_1406_);
v_r_1407_ = lean_ctor_get(v_impl_1400_, 4);
lean_inc(v_r_1407_);
v___x_1408_ = lean_unsigned_to_nat(3u);
v___x_1409_ = lean_nat_mul(v___x_1408_, v_size_1402_);
v___x_1410_ = lean_nat_dec_lt(v___x_1409_, v_size_1403_);
lean_dec(v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec(v_r_1407_);
lean_dec(v_l_1406_);
lean_dec(v_v_1405_);
lean_dec(v_k_1404_);
v___x_1411_ = lean_nat_add(v___x_1401_, v_size_1403_);
lean_dec(v_size_1403_);
v___x_1412_ = lean_nat_add(v___x_1411_, v_size_1402_);
lean_dec(v___x_1411_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 3, v_impl_1400_);
lean_ctor_set(v___x_1397_, 0, v___x_1412_);
v___x_1414_ = v___x_1397_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_impl_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_r_1395_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v_impl_1400_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1482_ = lean_ctor_get(v_impl_1400_, 4);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_impl_1400_, 3);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_impl_1400_, 2);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_impl_1400_, 1);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_impl_1400_, 0);
lean_dec(v_unused_1486_);
v___x_1417_ = v_impl_1400_;
v_isShared_1418_ = v_isSharedCheck_1481_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v_impl_1400_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1481_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_size_1419_; lean_object* v_size_1420_; lean_object* v_k_1421_; lean_object* v_v_1422_; lean_object* v_l_1423_; lean_object* v_r_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_size_1419_ = lean_ctor_get(v_l_1406_, 0);
v_size_1420_ = lean_ctor_get(v_r_1407_, 0);
v_k_1421_ = lean_ctor_get(v_r_1407_, 1);
v_v_1422_ = lean_ctor_get(v_r_1407_, 2);
v_l_1423_ = lean_ctor_get(v_r_1407_, 3);
v_r_1424_ = lean_ctor_get(v_r_1407_, 4);
v___x_1425_ = lean_unsigned_to_nat(2u);
v___x_1426_ = lean_nat_mul(v___x_1425_, v_size_1419_);
v___x_1427_ = lean_nat_dec_lt(v_size_1420_, v___x_1426_);
lean_dec(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1456_; 
lean_inc(v_r_1424_);
lean_inc(v_l_1423_);
lean_inc(v_v_1422_);
lean_inc(v_k_1421_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1457_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_r_1407_, 2);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1407_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1461_);
v___x_1429_ = v_r_1407_;
v_isShared_1430_ = v_isSharedCheck_1456_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v_r_1407_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1456_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___x_1444_; lean_object* v___y_1446_; 
v___x_1431_ = lean_nat_add(v___x_1401_, v_size_1403_);
lean_dec(v_size_1403_);
v___x_1432_ = lean_nat_add(v___x_1431_, v_size_1402_);
lean_dec(v___x_1431_);
v___x_1444_ = lean_nat_add(v___x_1401_, v_size_1419_);
if (lean_obj_tag(v_l_1423_) == 0)
{
lean_object* v_size_1454_; 
v_size_1454_ = lean_ctor_get(v_l_1423_, 0);
lean_inc(v_size_1454_);
v___y_1446_ = v_size_1454_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___y_1446_ = v___x_1455_;
goto v___jp_1445_;
}
v___jp_1433_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = lean_nat_add(v___y_1434_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec(v___y_1434_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 4, v_r_1395_);
lean_ctor_set(v___x_1429_, 3, v_r_1424_);
lean_ctor_set(v___x_1429_, 2, v_v_1393_);
lean_ctor_set(v___x_1429_, 1, v_k_1392_);
lean_ctor_set(v___x_1429_, 0, v___x_1437_);
v___x_1439_ = v___x_1429_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_r_1424_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_r_1395_);
v___x_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1441_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 4, v___x_1439_);
lean_ctor_set(v___x_1417_, 3, v___y_1435_);
lean_ctor_set(v___x_1417_, 2, v_v_1422_);
lean_ctor_set(v___x_1417_, 1, v_k_1421_);
lean_ctor_set(v___x_1417_, 0, v___x_1432_);
v___x_1441_ = v___x_1417_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_k_1421_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_v_1422_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v___y_1435_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
v___jp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_nat_add(v___x_1444_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec(v___x_1444_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_l_1423_);
lean_ctor_set(v___x_1397_, 3, v_l_1406_);
lean_ctor_set(v___x_1397_, 2, v_v_1405_);
lean_ctor_set(v___x_1397_, 1, v_k_1404_);
lean_ctor_set(v___x_1397_, 0, v___x_1447_);
v___x_1449_ = v___x_1397_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_l_1423_);
v___x_1449_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_nat_add(v___x_1401_, v_size_1402_);
if (lean_obj_tag(v_r_1424_) == 0)
{
lean_object* v_size_1451_; 
v_size_1451_ = lean_ctor_get(v_r_1424_, 0);
lean_inc(v_size_1451_);
v___y_1434_ = v___x_1450_;
v___y_1435_ = v___x_1449_;
v___y_1436_ = v_size_1451_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___y_1434_ = v___x_1450_;
v___y_1435_ = v___x_1449_;
v___y_1436_ = v___x_1452_;
goto v___jp_1433_;
}
}
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_del_object(v___x_1397_);
v___x_1462_ = lean_nat_add(v___x_1401_, v_size_1403_);
lean_dec(v_size_1403_);
v___x_1463_ = lean_nat_add(v___x_1462_, v_size_1402_);
lean_dec(v___x_1462_);
v___x_1464_ = lean_nat_add(v___x_1401_, v_size_1402_);
v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1420_);
lean_dec(v___x_1464_);
lean_inc_ref(v_r_1395_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 4, v_r_1395_);
lean_ctor_set(v___x_1417_, 3, v_r_1407_);
lean_ctor_set(v___x_1417_, 2, v_v_1393_);
lean_ctor_set(v___x_1417_, 1, v_k_1392_);
lean_ctor_set(v___x_1417_, 0, v___x_1465_);
v___x_1467_ = v___x_1417_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1407_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1395_);
v___x_1467_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_isSharedCheck_1474_ = !lean_is_exclusive(v_r_1395_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; 
v_unused_1475_ = lean_ctor_get(v_r_1395_, 4);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_r_1395_, 3);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_r_1395_, 2);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_r_1395_, 1);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_r_1395_, 0);
lean_dec(v_unused_1479_);
v___x_1469_ = v_r_1395_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v_r_1395_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 4, v___x_1467_);
lean_ctor_set(v___x_1469_, 3, v_l_1406_);
lean_ctor_set(v___x_1469_, 2, v_v_1405_);
lean_ctor_set(v___x_1469_, 1, v_k_1404_);
lean_ctor_set(v___x_1469_, 0, v___x_1463_);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v___x_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1487_; 
v_l_1487_ = lean_ctor_get(v_impl_1400_, 3);
lean_inc(v_l_1487_);
if (lean_obj_tag(v_l_1487_) == 0)
{
lean_object* v_r_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1501_; 
v_r_1488_ = lean_ctor_get(v_impl_1400_, 4);
v_k_1489_ = lean_ctor_get(v_impl_1400_, 1);
v_v_1490_ = lean_ctor_get(v_impl_1400_, 2);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_impl_1400_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1502_ = lean_ctor_get(v_impl_1400_, 3);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_impl_1400_, 0);
lean_dec(v_unused_1503_);
v___x_1492_ = v_impl_1400_;
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_r_1488_);
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_dec(v_impl_1400_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1488_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 3, v_r_1488_);
lean_ctor_set(v___x_1492_, 2, v_v_1393_);
lean_ctor_set(v___x_1492_, 1, v_k_1392_);
lean_ctor_set(v___x_1492_, 0, v___x_1401_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_r_1488_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1488_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v___x_1496_);
lean_ctor_set(v___x_1397_, 3, v_l_1487_);
lean_ctor_set(v___x_1397_, 2, v_v_1490_);
lean_ctor_set(v___x_1397_, 1, v_k_1489_);
lean_ctor_set(v___x_1397_, 0, v___x_1494_);
v___x_1498_ = v___x_1397_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_l_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v___x_1496_);
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
lean_object* v_r_1504_; 
v_r_1504_ = lean_ctor_get(v_impl_1400_, 4);
lean_inc(v_r_1504_);
if (lean_obj_tag(v_r_1504_) == 0)
{
lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1529_; 
v_k_1505_ = lean_ctor_get(v_impl_1400_, 1);
v_v_1506_ = lean_ctor_get(v_impl_1400_, 2);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_impl_1400_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; 
v_unused_1530_ = lean_ctor_get(v_impl_1400_, 4);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_impl_1400_, 3);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_impl_1400_, 0);
lean_dec(v_unused_1532_);
v___x_1508_ = v_impl_1400_;
v_isShared_1509_ = v_isSharedCheck_1529_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_v_1506_);
lean_inc(v_k_1505_);
lean_dec(v_impl_1400_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1529_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_k_1510_; lean_object* v_v_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1525_; 
v_k_1510_ = lean_ctor_get(v_r_1504_, 1);
v_v_1511_ = lean_ctor_get(v_r_1504_, 2);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_r_1504_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; lean_object* v_unused_1527_; lean_object* v_unused_1528_; 
v_unused_1526_ = lean_ctor_get(v_r_1504_, 4);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_r_1504_, 3);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_r_1504_, 0);
lean_dec(v_unused_1528_);
v___x_1513_ = v_r_1504_;
v_isShared_1514_ = v_isSharedCheck_1525_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_v_1511_);
lean_inc(v_k_1510_);
lean_dec(v_r_1504_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1525_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1515_ = lean_unsigned_to_nat(3u);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_l_1487_);
lean_ctor_set(v___x_1513_, 3, v_l_1487_);
lean_ctor_set(v___x_1513_, 2, v_v_1506_);
lean_ctor_set(v___x_1513_, 1, v_k_1505_);
lean_ctor_set(v___x_1513_, 0, v___x_1401_);
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_l_1487_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_l_1487_);
v___x_1517_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_l_1487_);
lean_ctor_set(v___x_1508_, 2, v_v_1393_);
lean_ctor_set(v___x_1508_, 1, v_k_1392_);
lean_ctor_set(v___x_1508_, 0, v___x_1401_);
v___x_1519_ = v___x_1508_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_l_1487_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_l_1487_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v___x_1519_);
lean_ctor_set(v___x_1397_, 3, v___x_1517_);
lean_ctor_set(v___x_1397_, 2, v_v_1511_);
lean_ctor_set(v___x_1397_, 1, v_k_1510_);
lean_ctor_set(v___x_1397_, 0, v___x_1515_);
v___x_1521_ = v___x_1397_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1510_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1511_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_unsigned_to_nat(2u);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_r_1504_);
lean_ctor_set(v___x_1397_, 3, v_impl_1400_);
lean_ctor_set(v___x_1397_, 0, v___x_1533_);
v___x_1535_ = v___x_1397_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_impl_1400_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_r_1504_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1538_; 
lean_dec(v_v_1393_);
lean_dec(v_k_1392_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 2, v_v_1389_);
lean_ctor_set(v___x_1397_, 1, v_k_1388_);
v___x_1538_ = v___x_1397_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_size_1391_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_l_1394_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1395_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
default: 
{
lean_object* v_impl_1540_; lean_object* v___x_1541_; 
lean_dec(v_size_1391_);
v_impl_1540_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1388_, v_v_1389_, v_r_1395_);
v___x_1541_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1394_) == 0)
{
lean_object* v_size_1542_; lean_object* v_size_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v_l_1546_; lean_object* v_r_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_size_1542_ = lean_ctor_get(v_l_1394_, 0);
v_size_1543_ = lean_ctor_get(v_impl_1540_, 0);
lean_inc(v_size_1543_);
v_k_1544_ = lean_ctor_get(v_impl_1540_, 1);
lean_inc(v_k_1544_);
v_v_1545_ = lean_ctor_get(v_impl_1540_, 2);
lean_inc(v_v_1545_);
v_l_1546_ = lean_ctor_get(v_impl_1540_, 3);
lean_inc(v_l_1546_);
v_r_1547_ = lean_ctor_get(v_impl_1540_, 4);
lean_inc(v_r_1547_);
v___x_1548_ = lean_unsigned_to_nat(3u);
v___x_1549_ = lean_nat_mul(v___x_1548_, v_size_1542_);
v___x_1550_ = lean_nat_dec_lt(v___x_1549_, v_size_1543_);
lean_dec(v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_r_1547_);
lean_dec(v_l_1546_);
lean_dec(v_v_1545_);
lean_dec(v_k_1544_);
v___x_1551_ = lean_nat_add(v___x_1541_, v_size_1542_);
v___x_1552_ = lean_nat_add(v___x_1551_, v_size_1543_);
lean_dec(v_size_1543_);
lean_dec(v___x_1551_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_impl_1540_);
lean_ctor_set(v___x_1397_, 0, v___x_1552_);
v___x_1554_ = v___x_1397_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_l_1394_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_impl_1540_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1619_; 
v_isSharedCheck_1619_ = !lean_is_exclusive(v_impl_1540_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; 
v_unused_1620_ = lean_ctor_get(v_impl_1540_, 4);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_impl_1540_, 3);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_impl_1540_, 2);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_impl_1540_, 1);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_impl_1540_, 0);
lean_dec(v_unused_1624_);
v___x_1557_ = v_impl_1540_;
v_isShared_1558_ = v_isSharedCheck_1619_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v_impl_1540_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1619_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_size_1559_; lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v_l_1562_; lean_object* v_r_1563_; lean_object* v_size_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v_size_1559_ = lean_ctor_get(v_l_1546_, 0);
v_k_1560_ = lean_ctor_get(v_l_1546_, 1);
v_v_1561_ = lean_ctor_get(v_l_1546_, 2);
v_l_1562_ = lean_ctor_get(v_l_1546_, 3);
v_r_1563_ = lean_ctor_get(v_l_1546_, 4);
v_size_1564_ = lean_ctor_get(v_r_1547_, 0);
v___x_1565_ = lean_unsigned_to_nat(2u);
v___x_1566_ = lean_nat_mul(v___x_1565_, v_size_1564_);
v___x_1567_ = lean_nat_dec_lt(v_size_1559_, v___x_1566_);
lean_dec(v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1595_; 
lean_inc(v_r_1563_);
lean_inc(v_l_1562_);
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_l_1546_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1596_ = lean_ctor_get(v_l_1546_, 4);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_l_1546_, 3);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_l_1546_, 2);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_l_1546_, 1);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_l_1546_, 0);
lean_dec(v_unused_1600_);
v___x_1569_ = v_l_1546_;
v_isShared_1570_ = v_isSharedCheck_1595_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v_l_1546_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1595_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1585_; 
v___x_1571_ = lean_nat_add(v___x_1541_, v_size_1542_);
v___x_1572_ = lean_nat_add(v___x_1571_, v_size_1543_);
lean_dec(v_size_1543_);
if (lean_obj_tag(v_l_1562_) == 0)
{
lean_object* v_size_1593_; 
v_size_1593_ = lean_ctor_get(v_l_1562_, 0);
lean_inc(v_size_1593_);
v___y_1585_ = v_size_1593_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___y_1585_ = v___x_1594_;
goto v___jp_1584_;
}
v___jp_1573_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_nat_add(v___y_1574_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec(v___y_1574_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 4, v_r_1547_);
lean_ctor_set(v___x_1569_, 3, v_r_1563_);
lean_ctor_set(v___x_1569_, 2, v_v_1545_);
lean_ctor_set(v___x_1569_, 1, v_k_1544_);
lean_ctor_set(v___x_1569_, 0, v___x_1577_);
v___x_1579_ = v___x_1569_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_r_1563_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_r_1547_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v___x_1579_);
lean_ctor_set(v___x_1557_, 3, v___y_1575_);
lean_ctor_set(v___x_1557_, 2, v_v_1561_);
lean_ctor_set(v___x_1557_, 1, v_k_1560_);
lean_ctor_set(v___x_1557_, 0, v___x_1572_);
v___x_1581_ = v___x_1557_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v___y_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
v___jp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_nat_add(v___x_1571_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec(v___x_1571_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_l_1562_);
lean_ctor_set(v___x_1397_, 0, v___x_1586_);
v___x_1588_ = v___x_1397_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_l_1394_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_l_1562_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_nat_add(v___x_1541_, v_size_1564_);
if (lean_obj_tag(v_r_1563_) == 0)
{
lean_object* v_size_1590_; 
v_size_1590_ = lean_ctor_get(v_r_1563_, 0);
lean_inc(v_size_1590_);
v___y_1574_ = v___x_1589_;
v___y_1575_ = v___x_1588_;
v___y_1576_ = v_size_1590_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
v___y_1574_ = v___x_1589_;
v___y_1575_ = v___x_1588_;
v___y_1576_ = v___x_1591_;
goto v___jp_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_del_object(v___x_1397_);
v___x_1601_ = lean_nat_add(v___x_1541_, v_size_1542_);
v___x_1602_ = lean_nat_add(v___x_1601_, v_size_1543_);
lean_dec(v_size_1543_);
v___x_1603_ = lean_nat_add(v___x_1601_, v_size_1559_);
lean_dec(v___x_1601_);
lean_inc_ref(v_l_1394_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v_l_1546_);
lean_ctor_set(v___x_1557_, 3, v_l_1394_);
lean_ctor_set(v___x_1557_, 2, v_v_1393_);
lean_ctor_set(v___x_1557_, 1, v_k_1392_);
lean_ctor_set(v___x_1557_, 0, v___x_1603_);
v___x_1605_ = v___x_1557_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_l_1394_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_l_1546_);
v___x_1605_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_isSharedCheck_1612_ = !lean_is_exclusive(v_l_1394_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v_l_1394_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_l_1394_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_l_1394_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_l_1394_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_l_1394_, 0);
lean_dec(v_unused_1617_);
v___x_1607_ = v_l_1394_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_dec(v_l_1394_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 4, v_r_1547_);
lean_ctor_set(v___x_1607_, 3, v___x_1605_);
lean_ctor_set(v___x_1607_, 2, v_v_1545_);
lean_ctor_set(v___x_1607_, 1, v_k_1544_);
lean_ctor_set(v___x_1607_, 0, v___x_1602_);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_r_1547_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1625_; 
v_l_1625_ = lean_ctor_get(v_impl_1540_, 3);
lean_inc(v_l_1625_);
if (lean_obj_tag(v_l_1625_) == 0)
{
lean_object* v_r_1626_; lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1651_; 
v_r_1626_ = lean_ctor_get(v_impl_1540_, 4);
v_k_1627_ = lean_ctor_get(v_impl_1540_, 1);
v_v_1628_ = lean_ctor_get(v_impl_1540_, 2);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_impl_1540_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; lean_object* v_unused_1653_; 
v_unused_1652_ = lean_ctor_get(v_impl_1540_, 3);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_impl_1540_, 0);
lean_dec(v_unused_1653_);
v___x_1630_ = v_impl_1540_;
v_isShared_1631_ = v_isSharedCheck_1651_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_r_1626_);
lean_inc(v_v_1628_);
lean_inc(v_k_1627_);
lean_dec(v_impl_1540_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1651_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_k_1632_; lean_object* v_v_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1647_; 
v_k_1632_ = lean_ctor_get(v_l_1625_, 1);
v_v_1633_ = lean_ctor_get(v_l_1625_, 2);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_l_1625_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1648_ = lean_ctor_get(v_l_1625_, 4);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_l_1625_, 3);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_l_1625_, 0);
lean_dec(v_unused_1650_);
v___x_1635_ = v_l_1625_;
v_isShared_1636_ = v_isSharedCheck_1647_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_v_1633_);
lean_inc(v_k_1632_);
lean_dec(v_l_1625_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1647_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1626_, 2);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 4, v_r_1626_);
lean_ctor_set(v___x_1635_, 3, v_r_1626_);
lean_ctor_set(v___x_1635_, 2, v_v_1393_);
lean_ctor_set(v___x_1635_, 1, v_k_1392_);
lean_ctor_set(v___x_1635_, 0, v___x_1541_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_r_1626_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_r_1626_);
v___x_1639_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
lean_inc(v_r_1626_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 3, v_r_1626_);
lean_ctor_set(v___x_1630_, 0, v___x_1541_);
v___x_1641_ = v___x_1630_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_r_1626_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_r_1626_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v___x_1641_);
lean_ctor_set(v___x_1397_, 3, v___x_1639_);
lean_ctor_set(v___x_1397_, 2, v_v_1633_);
lean_ctor_set(v___x_1397_, 1, v_k_1632_);
lean_ctor_set(v___x_1397_, 0, v___x_1637_);
v___x_1643_ = v___x_1397_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1632_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1633_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
else
{
lean_object* v_r_1654_; 
v_r_1654_ = lean_ctor_get(v_impl_1540_, 4);
lean_inc(v_r_1654_);
if (lean_obj_tag(v_r_1654_) == 0)
{
lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1667_; 
v_k_1655_ = lean_ctor_get(v_impl_1540_, 1);
v_v_1656_ = lean_ctor_get(v_impl_1540_, 2);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_impl_1540_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; 
v_unused_1668_ = lean_ctor_get(v_impl_1540_, 4);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_impl_1540_, 3);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_impl_1540_, 0);
lean_dec(v_unused_1670_);
v___x_1658_ = v_impl_1540_;
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_v_1656_);
lean_inc(v_k_1655_);
lean_dec(v_impl_1540_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(3u);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v_l_1625_);
lean_ctor_set(v___x_1658_, 2, v_v_1393_);
lean_ctor_set(v___x_1658_, 1, v_k_1392_);
lean_ctor_set(v___x_1658_, 0, v___x_1541_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_l_1625_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_l_1625_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_r_1654_);
lean_ctor_set(v___x_1397_, 3, v___x_1662_);
lean_ctor_set(v___x_1397_, 2, v_v_1656_);
lean_ctor_set(v___x_1397_, 1, v_k_1655_);
lean_ctor_set(v___x_1397_, 0, v___x_1660_);
v___x_1664_ = v___x_1397_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1655_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1654_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(2u);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 4, v_impl_1540_);
lean_ctor_set(v___x_1397_, 3, v_r_1654_);
lean_ctor_set(v___x_1397_, 0, v___x_1671_);
v___x_1673_ = v___x_1397_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1392_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1393_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_r_1654_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_impl_1540_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_unsigned_to_nat(1u);
v___x_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_k_1388_);
lean_ctor_set(v___x_1677_, 2, v_v_1389_);
lean_ctor_set(v___x_1677_, 3, v_t_1390_);
lean_ctor_set(v___x_1677_, 4, v_t_1390_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_1678_, size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_b_1681_){
_start:
{
lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_b_1681_);
return v___x_1689_;
}
else
{
lean_object* v_a_1690_; uint8_t v___x_1691_; 
v_a_1690_ = lean_array_uget_borrowed(v_as_1678_, v_i_1680_);
lean_inc(v_b_1681_);
lean_inc(v_a_1690_);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_1690_, v_b_1681_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_box(0);
lean_inc(v_a_1690_);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_1690_, v___x_1692_, v_b_1681_);
v___y_1684_ = v___x_1693_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v_b_1681_;
goto v___jp_1683_;
}
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1680_, v___x_1685_);
v_i_1680_ = v___x_1686_;
v_b_1681_ = v___y_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_1694_, lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_b_1697_, lean_object* v___y_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1694_, v_sz_boxed_1699_, v_i_boxed_1700_, v_b_1697_);
lean_dec_ref(v_as_1694_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_set_1710_; size_t v_sz_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v_set_1710_ = lean_box(1);
v_sz_1711_ = lean_array_size(v_a_1709_);
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_1709_, v_sz_1711_, v___x_1712_, v_set_1710_);
lean_dec(v_a_1709_);
return v___x_1713_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1708_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1708_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_1729_, lean_object* v_k_1730_, lean_object* v_t_1731_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1730_, v_t_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_1733_, lean_object* v_k_1734_, lean_object* v_t_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_1733_, v_k_1734_, v_t_1735_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_1738_, lean_object* v_k_1739_, lean_object* v_v_1740_, lean_object* v_t_1741_, lean_object* v_hl_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1739_, v_v_1740_, v_t_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_1744_, size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_b_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1744_, v_sz_1745_, v_i_1746_, v_b_1747_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_1754_, lean_object* v_sz_1755_, lean_object* v_i_1756_, lean_object* v_b_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1755_);
lean_dec(v_sz_1755_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1754_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_as_1754_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_1766_, lean_object* v_declName_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
uint8_t v___y_1774_; uint8_t v___y_1796_; lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Expr_getAppFn(v_e_1766_);
if (lean_obj_tag(v___x_1799_) == 4)
{
lean_object* v_declName_1800_; lean_object* v___x_1801_; 
v_declName_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc_n(v_declName_1800_, 2);
lean_dec_ref(v___x_1799_);
v___x_1801_ = lean_private_to_user_name(v_declName_1800_);
if (lean_obj_tag(v___x_1801_) == 0)
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_name_eq(v_declName_1800_, v_declName_1767_);
lean_dec(v_declName_1800_);
v___y_1796_ = v___x_1802_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1803_; uint8_t v___x_1804_; 
lean_dec(v_declName_1800_);
v_val_1803_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_val_1803_);
lean_dec_ref(v___x_1801_);
v___x_1804_ = lean_name_eq(v_val_1803_, v_declName_1767_);
lean_dec(v_val_1803_);
v___y_1796_ = v___x_1804_;
goto v___jp_1795_;
}
}
else
{
uint8_t v___x_1805_; 
lean_dec_ref(v___x_1799_);
v___x_1805_ = 0;
v___y_1774_ = v___x_1805_;
goto v___jp_1773_;
}
v___jp_1773_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_1766_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1786_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
if (lean_obj_tag(v_a_1776_) == 1)
{
lean_object* v_val_1780_; 
lean_del_object(v___x_1778_);
v_val_1780_ = lean_ctor_get(v_a_1776_, 0);
lean_inc(v_val_1780_);
lean_dec_ref(v_a_1776_);
v_e_1766_ = v_val_1780_;
goto _start;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
lean_dec(v_a_1776_);
v___x_1782_ = lean_box(v___y_1774_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1782_);
v___x_1784_ = v___x_1778_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1775_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1775_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
v___jp_1795_:
{
if (v___y_1796_ == 0)
{
v___y_1774_ = v___y_1796_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v_e_1766_);
v___x_1797_ = lean_box(v___y_1796_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_1806_, lean_object* v_declName_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1806_, v_declName_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_declName_1807_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_1814_, lean_object* v_b_1815_, lean_object* v_c_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
v___x_1822_ = lean_apply_7(v_k_1814_, v_b_1815_, v_c_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, lean_box(0));
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_1823_, lean_object* v_b_1824_, lean_object* v_c_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1823_, v_b_1824_, v_c_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_1832_, lean_object* v_k_1833_, uint8_t v_cleanupAnnotations_1834_, uint8_t v_whnfType_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___f_1841_; lean_object* v___x_1842_; 
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1841_, 0, v_k_1833_);
v___x_1842_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1832_, v___f_1841_, v_cleanupAnnotations_1834_, v_whnfType_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1842_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_1859_, lean_object* v_k_1860_, lean_object* v_cleanupAnnotations_1861_, lean_object* v_whnfType_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1868_; uint8_t v_whnfType_boxed_1869_; lean_object* v_res_1870_; 
v_cleanupAnnotations_boxed_1868_ = lean_unbox(v_cleanupAnnotations_1861_);
v_whnfType_boxed_1869_ = lean_unbox(v_whnfType_1862_);
v_res_1870_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1859_, v_k_1860_, v_cleanupAnnotations_boxed_1868_, v_whnfType_boxed_1869_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_1871_, lean_object* v_type_1872_, lean_object* v_k_1873_, uint8_t v_cleanupAnnotations_1874_, uint8_t v_whnfType_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1872_, v_k_1873_, v_cleanupAnnotations_1874_, v_whnfType_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_type_1883_, lean_object* v_k_1884_, lean_object* v_cleanupAnnotations_1885_, lean_object* v_whnfType_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1892_; uint8_t v_whnfType_boxed_1893_; lean_object* v_res_1894_; 
v_cleanupAnnotations_boxed_1892_ = lean_unbox(v_cleanupAnnotations_1885_);
v_whnfType_boxed_1893_ = lean_unbox(v_whnfType_1886_);
v_res_1894_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_1882_, v_type_1883_, v_k_1884_, v_cleanupAnnotations_boxed_1892_, v_whnfType_boxed_1893_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_1898_, lean_object* v_as_1899_, size_t v_sz_1900_, size_t v_i_1901_, lean_object* v_b_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_lt(v_i_1901_, v_sz_1900_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_b_1902_);
return v___x_1909_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec_ref(v_b_1902_);
v_a_1910_ = lean_array_uget_borrowed(v_as_1899_, v_i_1901_);
v___x_1911_ = l_Lean_Expr_fvarId_x21(v_a_1910_);
v___x_1912_ = l_Lean_FVarId_getDecl___redArg(v___x_1911_, v___y_1903_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = l_Lean_LocalDecl_type(v_a_1913_);
lean_dec(v_a_1913_);
v___x_1915_ = l_Lean_Expr_consumeMData(v___x_1914_);
lean_dec_ref(v___x_1914_);
v___x_1916_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_1915_, v_typeName_1898_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1932_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1932_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1932_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_unbox(v_a_1917_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; 
lean_del_object(v___x_1919_);
lean_dec(v_a_1917_);
v___x_1923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v___x_1924_ = ((size_t)1ULL);
v___x_1925_ = lean_usize_add(v_i_1901_, v___x_1924_);
v_i_1901_ = v___x_1925_;
v_b_1902_ = v___x_1923_;
goto _start;
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_a_1917_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v___x_1921_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1928_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1916_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1916_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1912_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1912_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_1949_, lean_object* v_as_1950_, lean_object* v_sz_1951_, lean_object* v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1951_);
lean_dec(v_sz_1951_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1949_, v_as_1950_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_as_1950_);
lean_dec(v_typeName_1949_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_1962_, lean_object* v_xs_1963_, lean_object* v_x_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; size_t v_sz_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_1971_ = lean_array_size(v_xs_1963_);
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1962_, v_xs_1963_, v_sz_1971_, v___x_1972_, v___x_1970_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1988_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1988_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1988_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_fst_1978_; 
v_fst_1978_ = lean_ctor_get(v_a_1974_, 0);
lean_inc(v_fst_1978_);
lean_dec(v_a_1974_);
if (lean_obj_tag(v_fst_1978_) == 0)
{
uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1979_ = 0;
v___x_1980_ = lean_box(v___x_1979_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1980_);
v___x_1982_ = v___x_1976_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
else
{
lean_object* v_val_1984_; lean_object* v___x_1986_; 
v_val_1984_ = lean_ctor_get(v_fst_1978_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v_fst_1978_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_val_1984_);
v___x_1986_ = v___x_1976_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
v_a_1989_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1973_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1973_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_1997_, lean_object* v_xs_1998_, lean_object* v_x_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_1997_, v_xs_1998_, v_x_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v_x_1999_);
lean_dec_ref(v_xs_1998_);
lean_dec(v_typeName_1997_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_2006_, lean_object* v_info_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___f_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___f_2013_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2013_, 0, v_typeName_2006_);
v___x_2014_ = l_Lean_ConstantInfo_type(v_info_2007_);
v___x_2015_ = 0;
v___x_2016_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_2014_, v___f_2013_, v___x_2015_, v___x_2015_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_2017_, lean_object* v_info_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2017_, v_info_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec_ref(v_info_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_hasMVar(v_e_2025_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_e_2025_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v_mctx_2031_; lean_object* v___x_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2035_; lean_object* v_cache_2036_; lean_object* v_zetaDeltaFVarIds_2037_; lean_object* v_postponed_2038_; lean_object* v_diag_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2048_; 
v___x_2030_ = lean_st_ref_get(v___y_2026_);
v_mctx_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_mctx_2031_);
lean_dec(v___x_2030_);
v___x_2032_ = l_Lean_instantiateMVarsCore(v_mctx_2031_, v_e_2025_);
v_fst_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_fst_2033_);
v_snd_2034_ = lean_ctor_get(v___x_2032_, 1);
lean_inc(v_snd_2034_);
lean_dec_ref(v___x_2032_);
v___x_2035_ = lean_st_ref_take(v___y_2026_);
v_cache_2036_ = lean_ctor_get(v___x_2035_, 1);
v_zetaDeltaFVarIds_2037_ = lean_ctor_get(v___x_2035_, 2);
v_postponed_2038_ = lean_ctor_get(v___x_2035_, 3);
v_diag_2039_ = lean_ctor_get(v___x_2035_, 4);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2049_);
v___x_2041_ = v___x_2035_;
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_diag_2039_);
lean_inc(v_postponed_2038_);
lean_inc(v_zetaDeltaFVarIds_2037_);
lean_inc(v_cache_2036_);
lean_dec(v___x_2035_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v_snd_2034_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_snd_2034_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_cache_2036_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_zetaDeltaFVarIds_2037_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_postponed_2038_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_diag_2039_);
v___x_2044_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_st_ref_set(v___y_2026_, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_fst_2033_);
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object* v_e_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2050_, v___y_2051_);
lean_dec(v___y_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object* v_e_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2054_, v___y_2056_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object* v_e_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object* v_type_2068_, lean_object* v_k_2069_, uint8_t v_cleanupAnnotations_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___f_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2076_, 0, v_k_2069_);
v___x_2077_ = 0;
v___x_2078_ = lean_box(0);
v___x_2079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2077_, v___x_2078_, v_type_2068_, v___f_2076_, v_cleanupAnnotations_2070_, v___x_2077_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2079_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2079_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object* v_type_2096_, lean_object* v_k_2097_, lean_object* v_cleanupAnnotations_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2104_; lean_object* v_res_2105_; 
v_cleanupAnnotations_boxed_2104_ = lean_unbox(v_cleanupAnnotations_2098_);
v_res_2105_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2096_, v_k_2097_, v_cleanupAnnotations_boxed_2104_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object* v_00_u03b1_2106_, lean_object* v_type_2107_, lean_object* v_k_2108_, uint8_t v_cleanupAnnotations_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2107_, v_k_2108_, v_cleanupAnnotations_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_type_2117_, lean_object* v_k_2118_, lean_object* v_cleanupAnnotations_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2125_; lean_object* v_res_2126_; 
v_cleanupAnnotations_boxed_2125_ = lean_unbox(v_cleanupAnnotations_2119_);
v_res_2126_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(v_00_u03b1_2116_, v_type_2117_, v_k_2118_, v_cleanupAnnotations_boxed_2125_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object* v_typeNameSet_2127_, lean_object* v_x_2128_, lean_object* v_type_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2127_, v_x_2128_, v_type_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v_x_2128_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object* v_typeNameSet_2136_, lean_object* v_type_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___f_2143_; lean_object* v_a_2145_; lean_object* v___y_2195_; lean_object* v___x_2205_; 
lean_inc(v_typeNameSet_2136_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2143_, 0, v_typeNameSet_2136_);
lean_inc_ref(v_type_2137_);
v___x_2205_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(v_type_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref(v_type_2137_);
v___y_2195_ = v___x_2205_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2206_; uint8_t v___y_2208_; uint8_t v___x_2209_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
v___x_2209_ = l_Lean_Exception_isInterrupt(v_a_2206_);
if (v___x_2209_ == 0)
{
uint8_t v___x_2210_; 
v___x_2210_ = l_Lean_Exception_isRuntime(v_a_2206_);
v___y_2208_ = v___x_2210_;
goto v___jp_2207_;
}
else
{
lean_dec(v_a_2206_);
v___y_2208_ = v___x_2209_;
goto v___jp_2207_;
}
v___jp_2207_:
{
if (v___y_2208_ == 0)
{
lean_dec_ref(v___x_2205_);
v_a_2145_ = v_type_2137_;
goto v___jp_2144_;
}
else
{
lean_dec_ref(v_type_2137_);
v___y_2195_ = v___x_2205_;
goto v___jp_2194_;
}
}
}
v___jp_2144_:
{
uint8_t v___x_2146_; 
v___x_2146_ = l_Lean_Expr_isForall(v_a_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec_ref(v___f_2143_);
v___x_2147_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_a_2145_, v_a_2139_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2183_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2183_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2183_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Expr_getAppFn(v_a_2148_);
if (lean_obj_tag(v___x_2152_) == 4)
{
lean_object* v_declName_2153_; uint8_t v___x_2154_; 
v_declName_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_declName_2153_);
lean_dec_ref(v___x_2152_);
lean_inc(v_typeNameSet_2136_);
v___x_2154_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_declName_2153_, v_typeNameSet_2136_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_del_object(v___x_2150_);
v___x_2155_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_a_2148_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2166_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2166_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2166_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
if (lean_obj_tag(v_a_2156_) == 1)
{
lean_object* v_val_2160_; 
lean_del_object(v___x_2158_);
v_val_2160_ = lean_ctor_get(v_a_2156_, 0);
lean_inc(v_val_2160_);
lean_dec_ref(v_a_2156_);
v_type_2137_ = v_val_2160_;
goto _start;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_a_2156_);
lean_dec(v_typeNameSet_2136_);
v___x_2162_ = lean_box(v___x_2154_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2162_);
v___x_2164_ = v___x_2158_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_typeNameSet_2136_);
v_a_2167_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2155_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2155_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_a_2148_);
lean_dec(v_typeNameSet_2136_);
v___x_2175_ = lean_box(v___x_2154_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2175_);
v___x_2177_ = v___x_2150_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
lean_dec_ref(v___x_2152_);
lean_dec(v_a_2148_);
lean_dec(v_typeNameSet_2136_);
v___x_2179_ = lean_box(v___x_2146_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2179_);
v___x_2181_ = v___x_2150_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_typeNameSet_2136_);
v_a_2184_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2147_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2147_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
uint8_t v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v_typeNameSet_2136_);
v___x_2192_ = 0;
v___x_2193_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_a_2145_, v___f_2143_, v___x_2192_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2193_;
}
}
v___jp_2194_:
{
if (lean_obj_tag(v___y_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___y_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___y_2195_);
v_a_2145_ = v_a_2196_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___f_2143_);
lean_dec(v_typeNameSet_2136_);
v_a_2197_ = lean_ctor_get(v___y_2195_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___y_2195_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___y_2195_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___y_2195_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object* v_typeNameSet_2211_, lean_object* v_x_2212_, lean_object* v_type_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2211_, v_type_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object* v_typeNameSet_2220_, lean_object* v_type_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2220_, v_type_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* v_typeNameSet_2228_, lean_object* v_info_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = l_Lean_ConstantInfo_type(v_info_2229_);
v___x_2236_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2228_, v___x_2235_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* v_typeNameSet_2237_, lean_object* v_info_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2237_, v_info_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec_ref(v_info_2238_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* v_matchAlias_2245_, lean_object* v_addAlias_2246_, lean_object* v_alias_2247_, lean_object* v_declNames_2248_, lean_object* v_ns_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
lean_inc_ref(v_matchAlias_2245_);
lean_inc(v_alias_2247_);
lean_inc(v_ns_2249_);
v___x_2258_ = lean_apply_2(v_matchAlias_2245_, v_ns_2249_, v_alias_2247_);
v___x_2259_ = lean_unbox(v___x_2258_);
if (v___x_2259_ == 0)
{
if (lean_obj_tag(v_ns_2249_) == 1)
{
lean_object* v_pre_2260_; 
v_pre_2260_ = lean_ctor_get(v_ns_2249_, 0);
lean_inc(v_pre_2260_);
lean_dec_ref(v_ns_2249_);
v_ns_2249_ = v_pre_2260_;
goto _start;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v_ns_2249_);
lean_dec(v_declNames_2248_);
lean_dec(v_alias_2247_);
lean_dec_ref(v_addAlias_2246_);
lean_dec_ref(v_matchAlias_2245_);
v___x_2262_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
}
else
{
lean_object* v___x_2264_; 
lean_dec(v_ns_2249_);
lean_dec_ref(v_matchAlias_2245_);
lean_inc(v_a_2256_);
lean_inc_ref(v_a_2255_);
lean_inc(v_a_2254_);
lean_inc_ref(v_a_2253_);
lean_inc_ref(v_a_2252_);
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
v___x_2264_ = lean_apply_10(v_addAlias_2246_, v_alias_2247_, v_declNames_2248_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, lean_box(0));
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object* v_matchAlias_2265_, lean_object* v_addAlias_2266_, lean_object* v_alias_2267_, lean_object* v_declNames_2268_, lean_object* v_ns_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2265_, v_addAlias_2266_, v_alias_2267_, v_declNames_2268_, v_ns_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object* v_a_2281_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_2281_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0));
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object* v_a_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2288_);
lean_dec_ref(v_a_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object* v_a_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2291_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object* v_a_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec_ref(v_a_2298_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object* v_ctx_2305_, lean_object* v_id_2306_, uint8_t v_danglingDot_2307_, lean_object* v_declName_2308_, lean_object* v_decl_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
lean_inc(v_declName_2308_);
v___x_2318_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_2305_, v_declName_2308_, v_id_2306_, v_danglingDot_2307_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2371_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2371_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2371_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
if (lean_obj_tag(v_a_2319_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_decl_2309_);
lean_dec(v_declName_2308_);
v_a_2323_ = lean_ctor_get(v_a_2319_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2319_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2325_ = v_a_2319_;
v_isShared_2326_ = v_isSharedCheck_2333_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v_a_2319_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2333_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2328_);
v___x_2330_ = v___x_2321_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2334_; 
v_a_2334_ = lean_ctor_get(v_a_2319_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v_a_2319_);
if (lean_obj_tag(v_a_2334_) == 1)
{
lean_object* v_val_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2366_; 
lean_del_object(v___x_2321_);
v_val_2335_ = lean_ctor_get(v_a_2334_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_a_2334_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2337_ = v_a_2334_;
v_isShared_2338_ = v_isSharedCheck_2366_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_val_2335_);
lean_dec(v_a_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2366_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_kind_2339_; lean_object* v_tags_2340_; lean_object* v___x_2341_; 
v_kind_2339_ = lean_ctor_get(v_decl_2309_, 1);
lean_inc_ref(v_kind_2339_);
v_tags_2340_ = lean_ctor_get(v_decl_2309_, 2);
lean_inc_ref(v_tags_2340_);
lean_dec_ref(v_decl_2309_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
v___x_2341_ = lean_apply_5(v_kind_2339_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, lean_box(0));
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v___x_2341_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
v___x_2343_ = lean_apply_5(v_tags_2340_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, lean_box(0));
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v___x_2343_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 0);
lean_ctor_set(v___x_2337_, 0, v_declName_2308_);
v___x_2346_ = v___x_2337_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_declName_2308_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
uint8_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_unbox(v_a_2342_);
lean_dec(v_a_2342_);
v___x_2348_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_2335_, v___x_2346_, v___x_2347_, v_a_2344_, v___y_2310_, v___y_2311_);
return v___x_2348_;
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2342_);
lean_del_object(v___x_2337_);
lean_dec(v_val_2335_);
lean_dec(v_declName_2308_);
v_a_2350_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2343_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2343_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_tags_2340_);
lean_del_object(v___x_2337_);
lean_dec(v_val_2335_);
lean_dec(v_declName_2308_);
v_a_2358_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2341_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2341_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec(v_a_2334_);
lean_dec_ref(v_decl_2309_);
lean_dec(v_declName_2308_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2367_);
v___x_2369_ = v___x_2321_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec_ref(v_decl_2309_);
lean_dec(v_declName_2308_);
v_a_2372_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2318_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2318_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object* v_ctx_2380_, lean_object* v_id_2381_, lean_object* v_danglingDot_2382_, lean_object* v_declName_2383_, lean_object* v_decl_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v_danglingDot_boxed_2393_; lean_object* v_res_2394_; 
v_danglingDot_boxed_2393_ = lean_unbox(v_danglingDot_2382_);
v_res_2394_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2380_, v_id_2381_, v_danglingDot_boxed_2393_, v_declName_2383_, v_decl_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2394_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object* v_id_2395_, uint8_t v_danglingDot_2396_, lean_object* v_ns_2397_, lean_object* v_alias_2398_){
_start:
{
uint8_t v___x_2399_; 
v___x_2399_ = l_Lean_Name_isPrefixOf(v_ns_2397_, v_alias_2398_);
if (v___x_2399_ == 0)
{
lean_dec(v_alias_2398_);
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = lean_box(0);
v___x_2401_ = l_Lean_Name_replacePrefix(v_alias_2398_, v_ns_2397_, v___x_2400_);
v___x_2402_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_2395_, v___x_2401_, v_danglingDot_2396_);
lean_dec(v___x_2401_);
return v___x_2402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object* v_id_2403_, lean_object* v_danglingDot_2404_, lean_object* v_ns_2405_, lean_object* v_alias_2406_){
_start:
{
uint8_t v_danglingDot_boxed_2407_; uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_danglingDot_boxed_2407_ = lean_unbox(v_danglingDot_2404_);
v_res_2408_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2403_, v_danglingDot_boxed_2407_, v_ns_2405_, v_alias_2406_);
lean_dec(v_ns_2405_);
lean_dec(v_id_2403_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object* v_a_2410_, lean_object* v___x_2411_, lean_object* v_alias_2412_, lean_object* v_as_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
if (lean_obj_tag(v_as_2413_) == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v___x_2411_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
else
{
lean_object* v_head_2423_; lean_object* v_tail_2424_; uint8_t v___x_2425_; 
v_head_2423_ = lean_ctor_get(v_as_2413_, 0);
lean_inc_n(v_head_2423_, 2);
v_tail_2424_ = lean_ctor_get(v_as_2413_, 1);
lean_inc(v_tail_2424_);
lean_dec_ref(v_as_2413_);
lean_inc_ref(v___x_2411_);
v___x_2425_ = l_Lean_Server_Completion_allowCompletion(v_a_2410_, v___x_2411_, v_head_2423_);
if (v___x_2425_ == 0)
{
lean_dec(v_head_2423_);
v_as_2413_ = v_tail_2424_;
goto _start;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2427_ = l_Lean_Name_getString_x21(v_alias_2412_);
v___x_2428_ = lean_box(0);
v___x_2429_ = l_Lean_Name_str___override(v___x_2428_, v___x_2427_);
v___x_2430_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_2429_, v_head_2423_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_dec_ref(v___x_2430_);
v_as_2413_ = v_tail_2424_;
goto _start;
}
else
{
lean_dec(v_tail_2424_);
lean_dec_ref(v___x_2411_);
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object* v_a_2432_, lean_object* v___x_2433_, lean_object* v_alias_2434_, lean_object* v_as_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2432_, v___x_2433_, v_alias_2434_, v_as_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v_alias_2434_);
lean_dec_ref(v_a_2432_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object* v_a_2444_, lean_object* v_env_2445_, lean_object* v_alias_2446_, lean_object* v_declNames_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2444_, v_env_2445_, v_alias_2446_, v_declNames_2447_, v___y_2448_, v___y_2449_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object* v_a_2457_, lean_object* v_env_2458_, lean_object* v_alias_2459_, lean_object* v_declNames_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2457_, v_env_2458_, v_alias_2459_, v_declNames_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v_alias_2459_);
lean_dec_ref(v_a_2457_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object* v___f_2470_, lean_object* v___f_2471_, lean_object* v_currNamespace_2472_, lean_object* v_alias_2473_, lean_object* v_declNames_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v___f_2470_, v___f_2471_, v_alias_2473_, v_declNames_2474_, v_currNamespace_2472_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object* v___f_2484_, lean_object* v___f_2485_, lean_object* v_currNamespace_2486_, lean_object* v_alias_2487_, lean_object* v_declNames_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2484_, v___f_2485_, v_currNamespace_2486_, v_alias_2487_, v_declNames_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object* v_f_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec_ref(v_f_2498_);
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_x_2499_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
else
{
lean_object* v_key_2511_; lean_object* v_value_2512_; lean_object* v_tail_2513_; lean_object* v___x_2514_; 
v_key_2511_ = lean_ctor_get(v_x_2500_, 0);
lean_inc(v_key_2511_);
v_value_2512_ = lean_ctor_get(v_x_2500_, 1);
lean_inc(v_value_2512_);
v_tail_2513_ = lean_ctor_get(v_x_2500_, 2);
lean_inc(v_tail_2513_);
lean_dec_ref(v_x_2500_);
lean_inc_ref(v_f_2498_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
v___x_2514_ = lean_apply_10(v_f_2498_, v_key_2511_, v_value_2512_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
if (lean_obj_tag(v_a_2515_) == 0)
{
lean_dec_ref(v_a_2515_);
lean_dec(v_tail_2513_);
lean_dec_ref(v_f_2498_);
return v___x_2514_;
}
else
{
lean_object* v_a_2516_; 
lean_dec_ref(v___x_2514_);
v_a_2516_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v_a_2515_);
v_x_2499_ = v_a_2516_;
v_x_2500_ = v_tail_2513_;
goto _start;
}
}
else
{
lean_dec(v_tail_2513_);
lean_dec_ref(v_f_2498_);
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object* v_f_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2518_, v_x_2519_, v_x_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(lean_object* v_f_2530_, lean_object* v_as_2531_, size_t v_i_2532_, size_t v_stop_2533_, lean_object* v_b_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_eq(v_i_2532_, v_stop_2533_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_array_uget_borrowed(v_as_2531_, v_i_2532_);
v___x_2545_ = lean_box(0);
lean_inc(v___x_2544_);
lean_inc_ref(v_f_2530_);
v___x_2546_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2530_, v___x_2545_, v___x_2544_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
if (lean_obj_tag(v_a_2547_) == 0)
{
lean_dec_ref(v_a_2547_);
lean_dec_ref(v_f_2530_);
return v___x_2546_;
}
else
{
lean_object* v_a_2548_; size_t v___x_2549_; size_t v___x_2550_; 
lean_dec_ref(v___x_2546_);
v_a_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v_a_2547_);
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_add(v_i_2532_, v___x_2549_);
v_i_2532_ = v___x_2550_;
v_b_2534_ = v_a_2548_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_2530_);
return v___x_2546_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec_ref(v_f_2530_);
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_b_2534_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg___boxed(lean_object* v_f_2554_, lean_object* v_as_2555_, lean_object* v_i_2556_, lean_object* v_stop_2557_, lean_object* v_b_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
size_t v_i_boxed_2567_; size_t v_stop_boxed_2568_; lean_object* v_res_2569_; 
v_i_boxed_2567_ = lean_unbox_usize(v_i_2556_);
lean_dec(v_i_2556_);
v_stop_boxed_2568_ = lean_unbox_usize(v_stop_2557_);
lean_dec(v_stop_2557_);
v_res_2569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2554_, v_as_2555_, v_i_boxed_2567_, v_stop_boxed_2568_, v_b_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec_ref(v_as_2555_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object* v_f_2570_, lean_object* v_x_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc_ref(v___y_2576_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
v___x_2582_ = lean_apply_10(v_f_2570_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, lean_box(0));
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_f_2583_, lean_object* v_x_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(v_f_2583_, v_x_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(lean_object* v_f_2596_, lean_object* v_keys_2597_, lean_object* v_vals_2598_, lean_object* v_i_2599_, lean_object* v_acc_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = lean_array_get_size(v_keys_2597_);
v___x_2610_ = lean_nat_dec_lt(v_i_2599_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_dec(v_i_2599_);
lean_dec_ref(v_f_2596_);
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_acc_2600_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
else
{
lean_object* v_k_2613_; lean_object* v_v_2614_; lean_object* v___x_2615_; 
v_k_2613_ = lean_array_fget_borrowed(v_keys_2597_, v_i_2599_);
v_v_2614_ = lean_array_fget_borrowed(v_vals_2598_, v_i_2599_);
lean_inc_ref(v_f_2596_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v_v_2614_);
lean_inc(v_k_2613_);
v___x_2615_ = lean_apply_11(v_f_2596_, v_acc_2600_, v_k_2613_, v_v_2614_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
if (lean_obj_tag(v_a_2616_) == 0)
{
lean_dec_ref(v_a_2616_);
lean_dec(v_i_2599_);
lean_dec_ref(v_f_2596_);
return v___x_2615_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec_ref(v___x_2615_);
v_a_2617_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v_a_2616_);
v___x_2618_ = lean_unsigned_to_nat(1u);
v___x_2619_ = lean_nat_add(v_i_2599_, v___x_2618_);
lean_dec(v_i_2599_);
v_i_2599_ = v___x_2619_;
v_acc_2600_ = v_a_2617_;
goto _start;
}
}
else
{
lean_dec(v_i_2599_);
lean_dec_ref(v_f_2596_);
return v___x_2615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg___boxed(lean_object* v_f_2621_, lean_object* v_keys_2622_, lean_object* v_vals_2623_, lean_object* v_i_2624_, lean_object* v_acc_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2621_, v_keys_2622_, v_vals_2623_, v_i_2624_, v_acc_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_vals_2623_);
lean_dec_ref(v_keys_2622_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(lean_object* v_f_2635_, lean_object* v_x_2636_, lean_object* v_x_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
if (lean_obj_tag(v_x_2636_) == 0)
{
lean_object* v_es_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2668_; 
v_es_2646_ = lean_ctor_get(v_x_2636_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_x_2636_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2648_ = v_x_2636_;
v_isShared_2649_ = v_isSharedCheck_2668_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_es_2646_);
lean_dec(v_x_2636_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2668_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = lean_array_get_size(v_es_2646_);
v___x_2652_ = lean_nat_dec_lt(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref(v_es_2646_);
lean_dec_ref(v_f_2635_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set_tag(v___x_2648_, 1);
lean_ctor_set(v___x_2648_, 0, v_x_2637_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_x_2637_);
v___x_2654_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
}
else
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_le(v___x_2651_, v___x_2651_);
if (v___x_2657_ == 0)
{
if (v___x_2652_ == 0)
{
lean_object* v___x_2659_; 
lean_dec_ref(v_es_2646_);
lean_dec_ref(v_f_2635_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set_tag(v___x_2648_, 1);
lean_ctor_set(v___x_2648_, 0, v_x_2637_);
v___x_2659_ = v___x_2648_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_x_2637_);
v___x_2659_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
else
{
size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
lean_del_object(v___x_2648_);
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = lean_usize_of_nat(v___x_2651_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2635_, v_es_2646_, v___x_2662_, v___x_2663_, v_x_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v_es_2646_);
return v___x_2664_;
}
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
lean_del_object(v___x_2648_);
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = lean_usize_of_nat(v___x_2651_);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2635_, v_es_2646_, v___x_2665_, v___x_2666_, v_x_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v_es_2646_);
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_ks_2669_; lean_object* v_vs_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_ks_2669_ = lean_ctor_get(v_x_2636_, 0);
lean_inc_ref(v_ks_2669_);
v_vs_2670_ = lean_ctor_get(v_x_2636_, 1);
lean_inc_ref(v_vs_2670_);
lean_dec_ref(v_x_2636_);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2635_, v_ks_2669_, v_vs_2670_, v___x_2671_, v_x_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v_vs_2670_);
lean_dec_ref(v_ks_2669_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(lean_object* v_f_2673_, lean_object* v_as_2674_, size_t v_i_2675_, size_t v_stop_2676_, lean_object* v_b_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_a_2687_; lean_object* v___y_2692_; uint8_t v___x_2695_; 
v___x_2695_ = lean_usize_dec_eq(v_i_2675_, v_stop_2676_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_array_uget_borrowed(v_as_2674_, v_i_2675_);
switch(lean_obj_tag(v___x_2696_))
{
case 0:
{
lean_object* v_key_2697_; lean_object* v_val_2698_; lean_object* v___x_2699_; 
v_key_2697_ = lean_ctor_get(v___x_2696_, 0);
v_val_2698_ = lean_ctor_get(v___x_2696_, 1);
lean_inc_ref(v_f_2673_);
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
lean_inc(v_val_2698_);
lean_inc(v_key_2697_);
v___x_2699_ = lean_apply_11(v_f_2673_, v_b_2677_, v_key_2697_, v_val_2698_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, lean_box(0));
v___y_2692_ = v___x_2699_;
goto v___jp_2691_;
}
case 1:
{
lean_object* v_node_2700_; lean_object* v___x_2701_; 
v_node_2700_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_node_2700_);
lean_inc_ref(v_f_2673_);
v___x_2701_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2673_, v_node_2700_, v_b_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
v___y_2692_ = v___x_2701_;
goto v___jp_2691_;
}
default: 
{
v_a_2687_ = v_b_2677_;
goto v___jp_2686_;
}
}
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec_ref(v_f_2673_);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v_b_2677_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
v___jp_2686_:
{
size_t v___x_2688_; size_t v___x_2689_; 
v___x_2688_ = ((size_t)1ULL);
v___x_2689_ = lean_usize_add(v_i_2675_, v___x_2688_);
v_i_2675_ = v___x_2689_;
v_b_2677_ = v_a_2687_;
goto _start;
}
v___jp_2691_:
{
if (lean_obj_tag(v___y_2692_) == 0)
{
lean_object* v_a_2693_; 
v_a_2693_ = lean_ctor_get(v___y_2692_, 0);
if (lean_obj_tag(v_a_2693_) == 0)
{
lean_dec_ref(v_f_2673_);
return v___y_2692_;
}
else
{
lean_object* v_a_2694_; 
lean_inc_ref(v_a_2693_);
lean_dec_ref(v___y_2692_);
v_a_2694_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v_a_2693_);
v_a_2687_ = v_a_2694_;
goto v___jp_2686_;
}
}
else
{
lean_dec_ref(v_f_2673_);
return v___y_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_f_2704_, lean_object* v_as_2705_, lean_object* v_i_2706_, lean_object* v_stop_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
size_t v_i_boxed_2717_; size_t v_stop_boxed_2718_; lean_object* v_res_2719_; 
v_i_boxed_2717_ = lean_unbox_usize(v_i_2706_);
lean_dec(v_i_2706_);
v_stop_boxed_2718_ = lean_unbox_usize(v_stop_2707_);
lean_dec(v_stop_2707_);
v_res_2719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2704_, v_as_2705_, v_i_boxed_2717_, v_stop_boxed_2718_, v_b_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_as_2705_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_f_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2720_, v_x_2721_, v_x_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object* v_map_2732_, lean_object* v_f_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___f_2742_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2742_, 0, v_f_2733_);
v___x_2743_ = lean_box(0);
v___x_2744_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v___f_2742_, v_map_2732_, v___x_2743_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object* v_map_2745_, lean_object* v_f_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_2745_, v_f_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object* v_s_2756_, lean_object* v_f_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_map_u2081_2766_; lean_object* v_map_u2082_2767_; lean_object* v_buckets_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_map_u2081_2766_ = lean_ctor_get(v_s_2756_, 0);
lean_inc_ref(v_map_u2081_2766_);
v_map_u2082_2767_ = lean_ctor_get(v_s_2756_, 1);
lean_inc_ref(v_map_u2082_2767_);
lean_dec_ref(v_s_2756_);
v_buckets_2768_ = lean_ctor_get(v_map_u2081_2766_, 1);
lean_inc_ref(v_buckets_2768_);
lean_dec_ref(v_map_u2081_2766_);
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_array_get_size(v_buckets_2768_);
v___x_2771_ = lean_nat_dec_lt(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; 
lean_dec_ref(v_buckets_2768_);
v___x_2772_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2767_, v_f_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2772_;
}
else
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_nat_dec_le(v___x_2770_, v___x_2770_);
if (v___x_2774_ == 0)
{
if (v___x_2771_ == 0)
{
lean_object* v___x_2775_; 
lean_dec_ref(v_buckets_2768_);
v___x_2775_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2767_, v_f_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2775_;
}
else
{
size_t v___x_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = lean_usize_of_nat(v___x_2770_);
lean_inc_ref(v_f_2757_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2757_, v_buckets_2768_, v___x_2776_, v___x_2777_, v___x_2773_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec_ref(v_buckets_2768_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
if (lean_obj_tag(v_a_2779_) == 0)
{
lean_dec_ref(v_a_2779_);
lean_dec_ref(v_map_u2082_2767_);
lean_dec_ref(v_f_2757_);
return v___x_2778_;
}
else
{
lean_object* v___x_2780_; 
lean_dec_ref(v_a_2779_);
lean_dec_ref(v___x_2778_);
v___x_2780_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2767_, v_f_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2780_;
}
}
else
{
lean_dec_ref(v_map_u2082_2767_);
lean_dec_ref(v_f_2757_);
return v___x_2778_;
}
}
}
else
{
size_t v___x_2781_; size_t v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = ((size_t)0ULL);
v___x_2782_ = lean_usize_of_nat(v___x_2770_);
lean_inc_ref(v_f_2757_);
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2757_, v_buckets_2768_, v___x_2781_, v___x_2782_, v___x_2773_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec_ref(v_buckets_2768_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
if (lean_obj_tag(v_a_2784_) == 0)
{
lean_dec_ref(v_a_2784_);
lean_dec_ref(v_map_u2082_2767_);
lean_dec_ref(v_f_2757_);
return v___x_2783_;
}
else
{
lean_object* v___x_2785_; 
lean_dec_ref(v_a_2784_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2767_, v_f_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2785_;
}
}
else
{
lean_dec_ref(v_map_u2082_2767_);
lean_dec_ref(v_f_2757_);
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object* v_s_2786_, lean_object* v_f_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_2786_, v_f_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object* v_f_2797_, lean_object* v_decl_2798_, lean_object* v_ci_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___y_2810_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2848_ = lean_unsigned_to_nat(1u);
v___x_2849_ = lean_nat_add(v___y_2800_, v___x_2848_);
v___x_2850_ = lean_unsigned_to_nat(10000u);
v___x_2851_ = lean_nat_dec_le(v___x_2850_, v___x_2849_);
if (v___x_2851_ == 0)
{
v___y_2810_ = v___x_2849_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2852_; lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v___x_2849_);
v___x_2852_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_2803_);
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_ci_2799_);
lean_dec(v_decl_2798_);
lean_dec_ref(v_f_2797_);
v_a_2857_ = lean_ctor_get(v_a_2853_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2859_ = v_a_2853_;
v_isShared_2860_ = v_isSharedCheck_2867_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v_a_2853_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2867_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2864_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2862_);
v___x_2864_ = v___x_2855_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v___x_2868_; 
lean_dec_ref(v_a_2853_);
lean_del_object(v___x_2855_);
v___x_2868_ = lean_unsigned_to_nat(0u);
v___y_2810_ = v___x_2868_;
goto v___jp_2809_;
}
}
}
v___jp_2809_:
{
lean_object* v___x_2811_; 
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
v___x_2811_ = lean_apply_10(v_f_2797_, v_decl_2798_, v_ci_2799_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2839_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2839_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2839_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_a_2812_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___y_2810_);
v_a_2816_ = lean_ctor_get(v_a_2812_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2818_ = v_a_2812_;
v_isShared_2819_ = v_isSharedCheck_2826_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v_a_2812_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2826_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2821_);
v___x_2823_ = v___x_2814_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2838_; 
v_a_2827_ = lean_ctor_get(v_a_2812_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2829_ = v_a_2812_;
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v_a_2812_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_a_2827_);
lean_ctor_set(v___x_2831_, 1, v___y_2810_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2831_);
v___x_2833_ = v___x_2829_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2835_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2833_);
v___x_2835_ = v___x_2814_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___y_2810_);
v_a_2840_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2811_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2811_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object* v_f_2870_, lean_object* v_decl_2871_, lean_object* v_ci_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2870_, v_decl_2871_, v_ci_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(lean_object* v_f_2883_, lean_object* v_keys_2884_, lean_object* v_vals_2885_, lean_object* v_i_2886_, lean_object* v_acc_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = lean_array_get_size(v_keys_2884_);
v___x_2898_ = lean_nat_dec_lt(v_i_2886_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v_i_2886_);
lean_dec_ref(v_f_2883_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_acc_2887_);
lean_ctor_set(v___x_2899_, 1, v___y_2888_);
v___x_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
else
{
lean_object* v_k_2902_; lean_object* v_v_2903_; lean_object* v___x_2904_; 
v_k_2902_ = lean_array_fget_borrowed(v_keys_2884_, v_i_2886_);
v_v_2903_ = lean_array_fget_borrowed(v_vals_2885_, v_i_2886_);
lean_inc_ref(v_f_2883_);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2894_);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2892_);
lean_inc_ref(v___y_2891_);
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc(v_v_2903_);
lean_inc(v_k_2902_);
v___x_2904_ = lean_apply_12(v_f_2883_, v_acc_2887_, v_k_2902_, v_v_2903_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, lean_box(0));
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
if (lean_obj_tag(v_a_2905_) == 0)
{
lean_dec_ref(v_a_2905_);
lean_dec(v_i_2886_);
lean_dec_ref(v_f_2883_);
return v___x_2904_;
}
else
{
lean_object* v_a_2906_; lean_object* v_fst_2907_; lean_object* v_snd_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec_ref(v___x_2904_);
v_a_2906_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v_a_2905_);
v_fst_2907_ = lean_ctor_get(v_a_2906_, 0);
lean_inc(v_fst_2907_);
v_snd_2908_ = lean_ctor_get(v_a_2906_, 1);
lean_inc(v_snd_2908_);
lean_dec(v_a_2906_);
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = lean_nat_add(v_i_2886_, v___x_2909_);
lean_dec(v_i_2886_);
v_i_2886_ = v___x_2910_;
v_acc_2887_ = v_fst_2907_;
v___y_2888_ = v_snd_2908_;
goto _start;
}
}
else
{
lean_dec(v_i_2886_);
lean_dec_ref(v_f_2883_);
return v___x_2904_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg___boxed(lean_object* v_f_2912_, lean_object* v_keys_2913_, lean_object* v_vals_2914_, lean_object* v_i_2915_, lean_object* v_acc_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2912_, v_keys_2913_, v_vals_2914_, v_i_2915_, v_acc_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v_vals_2914_);
lean_dec_ref(v_keys_2913_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(lean_object* v_f_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
if (lean_obj_tag(v_x_2928_) == 0)
{
lean_object* v_es_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2963_; 
v_es_2939_ = lean_ctor_get(v_x_2928_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_x_2928_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2941_ = v_x_2928_;
v_isShared_2942_ = v_isSharedCheck_2963_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_es_2939_);
lean_dec(v_x_2928_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2963_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_array_get_size(v_es_2939_);
v___x_2945_ = lean_nat_dec_lt(v___x_2943_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
lean_dec_ref(v_es_2939_);
lean_dec_ref(v_f_2927_);
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v_x_2929_);
lean_ctor_set(v___x_2946_, 1, v___y_2930_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 1);
lean_ctor_set(v___x_2941_, 0, v___x_2946_);
v___x_2948_ = v___x_2941_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
else
{
uint8_t v___x_2951_; 
v___x_2951_ = lean_nat_dec_le(v___x_2944_, v___x_2944_);
if (v___x_2951_ == 0)
{
if (v___x_2945_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
lean_dec_ref(v_es_2939_);
lean_dec_ref(v_f_2927_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_x_2929_);
lean_ctor_set(v___x_2952_, 1, v___y_2930_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 1);
lean_ctor_set(v___x_2941_, 0, v___x_2952_);
v___x_2954_ = v___x_2941_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
else
{
size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
lean_del_object(v___x_2941_);
v___x_2957_ = ((size_t)0ULL);
v___x_2958_ = lean_usize_of_nat(v___x_2944_);
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2927_, v_es_2939_, v___x_2957_, v___x_2958_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec_ref(v_es_2939_);
return v___x_2959_;
}
}
else
{
size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; 
lean_del_object(v___x_2941_);
v___x_2960_ = ((size_t)0ULL);
v___x_2961_ = lean_usize_of_nat(v___x_2944_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2927_, v_es_2939_, v___x_2960_, v___x_2961_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec_ref(v_es_2939_);
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_ks_2964_; lean_object* v_vs_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_ks_2964_ = lean_ctor_get(v_x_2928_, 0);
lean_inc_ref(v_ks_2964_);
v_vs_2965_ = lean_ctor_get(v_x_2928_, 1);
lean_inc_ref(v_vs_2965_);
lean_dec_ref(v_x_2928_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2927_, v_ks_2964_, v_vs_2965_, v___x_2966_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec_ref(v_vs_2965_);
lean_dec_ref(v_ks_2964_);
return v___x_2967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(lean_object* v_f_2968_, lean_object* v_as_2969_, size_t v_i_2970_, size_t v_stop_2971_, lean_object* v_b_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_fst_2983_; lean_object* v_snd_2984_; lean_object* v___y_2989_; uint8_t v___x_2994_; 
v___x_2994_ = lean_usize_dec_eq(v_i_2970_, v_stop_2971_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_array_uget_borrowed(v_as_2969_, v_i_2970_);
switch(lean_obj_tag(v___x_2995_))
{
case 0:
{
lean_object* v_key_2996_; lean_object* v_val_2997_; lean_object* v___x_2998_; 
v_key_2996_ = lean_ctor_get(v___x_2995_, 0);
v_val_2997_ = lean_ctor_get(v___x_2995_, 1);
lean_inc_ref(v_f_2968_);
lean_inc(v___y_2980_);
lean_inc_ref(v___y_2979_);
lean_inc(v___y_2978_);
lean_inc_ref(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc(v_val_2997_);
lean_inc(v_key_2996_);
v___x_2998_ = lean_apply_12(v_f_2968_, v_b_2972_, v_key_2996_, v_val_2997_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, lean_box(0));
v___y_2989_ = v___x_2998_;
goto v___jp_2988_;
}
case 1:
{
lean_object* v_node_2999_; lean_object* v___x_3000_; 
v_node_2999_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_node_2999_);
lean_inc_ref(v_f_2968_);
v___x_3000_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_2968_, v_node_2999_, v_b_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
v___y_2989_ = v___x_3000_;
goto v___jp_2988_;
}
default: 
{
v_fst_2983_ = v_b_2972_;
v_snd_2984_ = v___y_2973_;
goto v___jp_2982_;
}
}
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref(v_f_2968_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v_b_2972_);
lean_ctor_set(v___x_3001_, 1, v___y_2973_);
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
v___jp_2982_:
{
size_t v___x_2985_; size_t v___x_2986_; 
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_add(v_i_2970_, v___x_2985_);
v_i_2970_ = v___x_2986_;
v_b_2972_ = v_fst_2983_;
v___y_2973_ = v_snd_2984_;
goto _start;
}
v___jp_2988_:
{
if (lean_obj_tag(v___y_2989_) == 0)
{
lean_object* v_a_2990_; 
v_a_2990_ = lean_ctor_get(v___y_2989_, 0);
if (lean_obj_tag(v_a_2990_) == 0)
{
lean_dec_ref(v_f_2968_);
return v___y_2989_;
}
else
{
lean_object* v_a_2991_; lean_object* v_fst_2992_; lean_object* v_snd_2993_; 
lean_inc_ref(v_a_2990_);
lean_dec_ref(v___y_2989_);
v_a_2991_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v_a_2990_);
v_fst_2992_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_fst_2992_);
v_snd_2993_ = lean_ctor_get(v_a_2991_, 1);
lean_inc(v_snd_2993_);
lean_dec(v_a_2991_);
v_fst_2983_ = v_fst_2992_;
v_snd_2984_ = v_snd_2993_;
goto v___jp_2982_;
}
}
else
{
lean_dec_ref(v_f_2968_);
return v___y_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg___boxed(lean_object* v_f_3004_, lean_object* v_as_3005_, lean_object* v_i_3006_, lean_object* v_stop_3007_, lean_object* v_b_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
size_t v_i_boxed_3018_; size_t v_stop_boxed_3019_; lean_object* v_res_3020_; 
v_i_boxed_3018_ = lean_unbox_usize(v_i_3006_);
lean_dec(v_i_3006_);
v_stop_boxed_3019_ = lean_unbox_usize(v_stop_3007_);
lean_dec(v_stop_3007_);
v_res_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_3004_, v_as_3005_, v_i_boxed_3018_, v_stop_boxed_3019_, v_b_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v_as_3005_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg___boxed(lean_object* v_f_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_3021_, v_x_3022_, v_x_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_f_3034_, lean_object* v_x_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; 
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3044_);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc_ref(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc_ref(v___y_3039_);
v___x_3047_ = lean_apply_11(v_f_3034_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, lean_box(0));
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_f_3048_, lean_object* v_x_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_3048_, v_x_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_map_3062_, lean_object* v_f_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___f_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___f_3073_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3073_, 0, v_f_3063_);
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v___f_3073_, v_map_3062_, v___x_3074_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_map_3076_, lean_object* v_f_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3076_, v_f_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object* v_f_3088_, lean_object* v_x_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_dec_ref(v_f_3088_);
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_x_3089_);
lean_ctor_set(v___x_3100_, 1, v___y_3091_);
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
return v___x_3102_;
}
else
{
lean_object* v_key_3103_; lean_object* v_value_3104_; lean_object* v_tail_3105_; lean_object* v___x_3106_; 
v_key_3103_ = lean_ctor_get(v_x_3090_, 0);
lean_inc(v_key_3103_);
v_value_3104_ = lean_ctor_get(v_x_3090_, 1);
lean_inc(v_value_3104_);
v_tail_3105_ = lean_ctor_get(v_x_3090_, 2);
lean_inc(v_tail_3105_);
lean_dec_ref(v_x_3090_);
lean_inc_ref(v_f_3088_);
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
lean_inc_ref(v___y_3094_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
v___x_3106_ = lean_apply_11(v_f_3088_, v_key_3103_, v_value_3104_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, lean_box(0));
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
if (lean_obj_tag(v_a_3107_) == 0)
{
lean_dec_ref(v_a_3107_);
lean_dec(v_tail_3105_);
lean_dec_ref(v_f_3088_);
return v___x_3106_;
}
else
{
lean_object* v_a_3108_; lean_object* v_fst_3109_; lean_object* v_snd_3110_; 
lean_dec_ref(v___x_3106_);
v_a_3108_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref(v_a_3107_);
v_fst_3109_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_fst_3109_);
v_snd_3110_ = lean_ctor_get(v_a_3108_, 1);
lean_inc(v_snd_3110_);
lean_dec(v_a_3108_);
v_x_3089_ = v_fst_3109_;
v_x_3090_ = v_tail_3105_;
v___y_3091_ = v_snd_3110_;
goto _start;
}
}
else
{
lean_dec(v_tail_3105_);
lean_dec_ref(v_f_3088_);
return v___x_3106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_f_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3112_, v_x_3113_, v_x_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(lean_object* v_f_3125_, lean_object* v_as_3126_, size_t v_i_3127_, size_t v_stop_3128_, lean_object* v_b_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_usize_dec_eq(v_i_3127_, v_stop_3128_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_array_uget_borrowed(v_as_3126_, v_i_3127_);
v___x_3141_ = lean_box(0);
lean_inc(v___x_3140_);
lean_inc_ref(v_f_3125_);
v___x_3142_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3125_, v___x_3141_, v___x_3140_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
if (lean_obj_tag(v_a_3143_) == 0)
{
lean_dec_ref(v_a_3143_);
lean_dec_ref(v_f_3125_);
return v___x_3142_;
}
else
{
lean_object* v_a_3144_; lean_object* v_fst_3145_; lean_object* v_snd_3146_; size_t v___x_3147_; size_t v___x_3148_; 
lean_dec_ref(v___x_3142_);
v_a_3144_ = lean_ctor_get(v_a_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v_a_3143_);
v_fst_3145_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_fst_3145_);
v_snd_3146_ = lean_ctor_get(v_a_3144_, 1);
lean_inc(v_snd_3146_);
lean_dec(v_a_3144_);
v___x_3147_ = ((size_t)1ULL);
v___x_3148_ = lean_usize_add(v_i_3127_, v___x_3147_);
v_i_3127_ = v___x_3148_;
v_b_3129_ = v_fst_3145_;
v___y_3130_ = v_snd_3146_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_3125_);
return v___x_3142_;
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec_ref(v_f_3125_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_b_3129_);
lean_ctor_set(v___x_3150_, 1, v___y_3130_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4___boxed(lean_object* v_f_3153_, lean_object* v_as_3154_, lean_object* v_i_3155_, lean_object* v_stop_3156_, lean_object* v_b_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
size_t v_i_boxed_3167_; size_t v_stop_boxed_3168_; lean_object* v_res_3169_; 
v_i_boxed_3167_ = lean_unbox_usize(v_i_3155_);
lean_dec(v_i_3155_);
v_stop_boxed_3168_ = lean_unbox_usize(v_stop_3156_);
lean_dec(v_stop_3156_);
v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3153_, v_as_3154_, v_i_boxed_3167_, v_stop_boxed_3168_, v_b_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v_as_3154_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object* v_env_3170_, lean_object* v_f_3171_, lean_object* v_name_3172_, lean_object* v_c_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
uint8_t v___x_3183_; 
lean_inc(v_name_3172_);
v___x_3183_ = l_Lean_Meta_allowCompletion(v_env_3170_, v_name_3172_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec_ref(v_c_3173_);
lean_dec(v_name_3172_);
lean_dec_ref(v_f_3171_);
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v___y_3174_);
v___x_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_inc_ref(v_c_3173_);
v___x_3188_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionKindForDecl___boxed), 6, 1);
lean_closure_set(v___x_3188_, 0, v_c_3173_);
lean_inc(v_name_3172_);
v___x_3189_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionTagsForDecl___boxed), 6, 1);
lean_closure_set(v___x_3189_, 0, v_name_3172_);
v___x_3190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3190_, 0, v_c_3173_);
lean_ctor_set(v___x_3190_, 1, v___x_3188_);
lean_ctor_set(v___x_3190_, 2, v___x_3189_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
v___x_3191_ = lean_apply_11(v_f_3171_, v_name_3172_, v___x_3190_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, lean_box(0));
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object* v_env_3192_, lean_object* v_f_3193_, lean_object* v_name_3194_, lean_object* v_c_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3192_, v_f_3193_, v_name_3194_, v_c_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object* v_f_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v_env_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_st_ref_get(v___y_3214_);
v_env_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc_ref_n(v_env_3217_, 2);
lean_dec(v___x_3216_);
v___x_3218_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_3217_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v_buckets_3220_; lean_object* v___f_3221_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref(v___x_3218_);
v_buckets_3220_ = lean_ctor_get(v_a_3219_, 1);
lean_inc_ref(v_buckets_3220_);
lean_dec(v_a_3219_);
lean_inc_ref(v_f_3206_);
lean_inc_ref(v_env_3217_);
v___f_3221_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3221_, 0, v_env_3217_);
lean_closure_set(v___f_3221_, 1, v_f_3206_);
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = lean_array_get_size(v_buckets_3220_);
v___x_3236_ = lean_nat_dec_lt(v___x_3234_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v_map_u2082_3238_; lean_object* v___x_3239_; 
lean_dec_ref(v_buckets_3220_);
lean_dec_ref(v_f_3206_);
v___x_3237_ = l_Lean_Environment_constants(v_env_3217_);
v_map_u2082_3238_ = lean_ctor_get(v___x_3237_, 1);
lean_inc_ref(v_map_u2082_3238_);
lean_dec_ref(v___x_3237_);
v___x_3239_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3238_, v___f_3221_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = lean_box(0);
v___x_3241_ = lean_nat_dec_le(v___x_3235_, v___x_3235_);
if (v___x_3241_ == 0)
{
if (v___x_3236_ == 0)
{
lean_dec_ref(v_buckets_3220_);
lean_dec_ref(v_f_3206_);
v___y_3223_ = v___y_3207_;
v___y_3224_ = v___y_3208_;
v___y_3225_ = v___y_3209_;
v___y_3226_ = v___y_3210_;
v___y_3227_ = v___y_3211_;
v___y_3228_ = v___y_3212_;
v___y_3229_ = v___y_3213_;
v___y_3230_ = v___y_3214_;
goto v___jp_3222_;
}
else
{
size_t v___x_3242_; size_t v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = lean_usize_of_nat(v___x_3235_);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3206_, v_buckets_3220_, v___x_3242_, v___x_3243_, v___x_3240_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec_ref(v_buckets_3220_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
if (lean_obj_tag(v_a_3245_) == 0)
{
lean_dec_ref(v_a_3245_);
lean_dec_ref(v___f_3221_);
lean_dec_ref(v_env_3217_);
return v___x_3244_;
}
else
{
lean_object* v_a_3246_; lean_object* v_snd_3247_; 
lean_dec_ref(v___x_3244_);
v_a_3246_ = lean_ctor_get(v_a_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref(v_a_3245_);
v_snd_3247_ = lean_ctor_get(v_a_3246_, 1);
lean_inc(v_snd_3247_);
lean_dec(v_a_3246_);
v___y_3223_ = v_snd_3247_;
v___y_3224_ = v___y_3208_;
v___y_3225_ = v___y_3209_;
v___y_3226_ = v___y_3210_;
v___y_3227_ = v___y_3211_;
v___y_3228_ = v___y_3212_;
v___y_3229_ = v___y_3213_;
v___y_3230_ = v___y_3214_;
goto v___jp_3222_;
}
}
else
{
lean_dec_ref(v___f_3221_);
lean_dec_ref(v_env_3217_);
return v___x_3244_;
}
}
}
else
{
size_t v___x_3248_; size_t v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = ((size_t)0ULL);
v___x_3249_ = lean_usize_of_nat(v___x_3235_);
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3206_, v_buckets_3220_, v___x_3248_, v___x_3249_, v___x_3240_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec_ref(v_buckets_3220_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
if (lean_obj_tag(v_a_3251_) == 0)
{
lean_dec_ref(v_a_3251_);
lean_dec_ref(v___f_3221_);
lean_dec_ref(v_env_3217_);
return v___x_3250_;
}
else
{
lean_object* v_a_3252_; lean_object* v_snd_3253_; 
lean_dec_ref(v___x_3250_);
v_a_3252_ = lean_ctor_get(v_a_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v_a_3251_);
v_snd_3253_ = lean_ctor_get(v_a_3252_, 1);
lean_inc(v_snd_3253_);
lean_dec(v_a_3252_);
v___y_3223_ = v_snd_3253_;
v___y_3224_ = v___y_3208_;
v___y_3225_ = v___y_3209_;
v___y_3226_ = v___y_3210_;
v___y_3227_ = v___y_3211_;
v___y_3228_ = v___y_3212_;
v___y_3229_ = v___y_3213_;
v___y_3230_ = v___y_3214_;
goto v___jp_3222_;
}
}
else
{
lean_dec_ref(v___f_3221_);
lean_dec_ref(v_env_3217_);
return v___x_3250_;
}
}
}
v___jp_3222_:
{
lean_object* v___x_3231_; lean_object* v_map_u2082_3232_; lean_object* v___x_3233_; 
v___x_3231_ = l_Lean_Environment_constants(v_env_3217_);
v_map_u2082_3232_ = lean_ctor_get(v___x_3231_, 1);
lean_inc_ref(v_map_u2082_3232_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3232_, v___f_3221_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3233_;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_env_3217_);
lean_dec(v___y_3207_);
lean_dec_ref(v_f_3206_);
v_a_3254_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3218_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3218_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object* v_f_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object* v_f_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___f_3282_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3282_, 0, v_f_3273_);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v___f_3282_, v___x_3283_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3304_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3304_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3304_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
if (lean_obj_tag(v_a_3285_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3299_; 
v_a_3289_ = lean_ctor_get(v_a_3285_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_a_3285_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3291_ = v_a_3285_;
v_isShared_3292_ = v_isSharedCheck_3299_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v_a_3285_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3299_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3294_);
v___x_3296_ = v___x_3287_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
lean_dec_ref(v_a_3285_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3300_);
v___x_3302_ = v___x_3287_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
v_a_3305_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3284_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3284_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object* v_f_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(lean_object* v_id_3325_, uint8_t v_danglingDot_3326_, lean_object* v_as_3327_, size_t v_sz_3328_, size_t v_i_3329_, lean_object* v_b_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v___x_3334_; 
v___x_3334_ = lean_usize_dec_lt(v_i_3329_, v_sz_3328_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_b_3330_);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
return v___x_3336_;
}
else
{
lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3390_; 
v_snd_3337_ = lean_ctor_get(v_b_3330_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_b_3330_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_b_3330_, 0);
lean_dec(v_unused_3391_);
v___x_3339_ = v_b_3330_;
v_isShared_3340_ = v_isSharedCheck_3390_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_dec(v_b_3330_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3390_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v_a_3343_; lean_object* v_a_3350_; 
v___x_3341_ = lean_box(0);
v_a_3350_ = lean_array_uget(v_as_3327_, v_i_3329_);
if (lean_obj_tag(v_a_3350_) == 0)
{
v_a_3343_ = v_snd_3337_;
goto v___jp_3342_;
}
else
{
lean_object* v_val_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v_snd_3337_);
v_val_3351_ = lean_ctor_get(v_a_3350_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_3350_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3353_ = v_a_3350_;
v_isShared_3354_ = v_isSharedCheck_3389_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_val_3351_);
lean_dec(v_a_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3389_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3355_ = lean_box(0);
v___x_3356_ = l_Lean_LocalDecl_userName(v_val_3351_);
v___x_3357_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3325_, v___x_3356_, v_danglingDot_3326_);
if (v___x_3357_ == 0)
{
lean_dec(v___x_3356_);
lean_del_object(v___x_3353_);
lean_dec(v_val_3351_);
v_a_3343_ = v___x_3355_;
goto v___jp_3342_;
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3358_ = l_Lean_LocalDecl_fvarId(v_val_3351_);
lean_dec(v_val_3351_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3358_);
v___x_3360_ = v___x_3353_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = 5;
v___x_3362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3363_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3356_, v___x_3360_, v___x_3361_, v___x_3362_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3379_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3379_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3379_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
if (lean_obj_tag(v_a_3364_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3378_; 
lean_del_object(v___x_3339_);
v_a_3368_ = lean_ctor_get(v_a_3364_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_a_3364_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3370_ = v_a_3364_;
v_isShared_3371_ = v_isSharedCheck_3378_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v_a_3364_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3378_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3373_);
v___x_3375_ = v___x_3366_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_dec_ref(v_a_3364_);
lean_del_object(v___x_3366_);
v_a_3343_ = v___x_3355_;
goto v___jp_3342_;
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_del_object(v___x_3339_);
v_a_3380_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3363_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3363_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
}
}
v___jp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v_a_3343_);
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3345_ = v___x_3339_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3343_);
v___x_3345_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
size_t v___x_3346_; size_t v___x_3347_; 
v___x_3346_ = ((size_t)1ULL);
v___x_3347_ = lean_usize_add(v_i_3329_, v___x_3346_);
v_i_3329_ = v___x_3347_;
v_b_3330_ = v___x_3345_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___boxed(lean_object* v_id_3392_, lean_object* v_danglingDot_3393_, lean_object* v_as_3394_, lean_object* v_sz_3395_, lean_object* v_i_3396_, lean_object* v_b_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v_danglingDot_boxed_3401_; size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_danglingDot_boxed_3401_ = lean_unbox(v_danglingDot_3393_);
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3395_);
lean_dec(v_sz_3395_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3396_);
lean_dec(v_i_3396_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3392_, v_danglingDot_boxed_3401_, v_as_3394_, v_sz_boxed_3402_, v_i_boxed_3403_, v_b_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_as_3394_);
lean_dec(v_id_3392_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(lean_object* v_id_3405_, uint8_t v_danglingDot_3406_, lean_object* v_as_3407_, size_t v_sz_3408_, size_t v_i_3409_, lean_object* v_b_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_usize_dec_lt(v_i_3409_, v_sz_3408_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3420_, 0, v_b_3410_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
else
{
lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3475_; 
v_snd_3422_ = lean_ctor_get(v_b_3410_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_b_3410_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v_b_3410_, 0);
lean_dec(v_unused_3476_);
v___x_3424_ = v_b_3410_;
v_isShared_3425_ = v_isSharedCheck_3475_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_dec(v_b_3410_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3475_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_a_3428_; lean_object* v_a_3435_; 
v___x_3426_ = lean_box(0);
v_a_3435_ = lean_array_uget(v_as_3407_, v_i_3409_);
if (lean_obj_tag(v_a_3435_) == 0)
{
v_a_3428_ = v_snd_3422_;
goto v___jp_3427_;
}
else
{
lean_object* v_val_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_snd_3422_);
v_val_3436_ = lean_ctor_get(v_a_3435_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_a_3435_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3438_ = v_a_3435_;
v_isShared_3439_ = v_isSharedCheck_3474_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_val_3436_);
lean_dec(v_a_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3474_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_LocalDecl_userName(v_val_3436_);
v___x_3442_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3405_, v___x_3441_, v_danglingDot_3406_);
if (v___x_3442_ == 0)
{
lean_dec(v___x_3441_);
lean_del_object(v___x_3438_);
lean_dec(v_val_3436_);
v_a_3428_ = v___x_3440_;
goto v___jp_3427_;
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = l_Lean_LocalDecl_fvarId(v_val_3436_);
lean_dec(v_val_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3443_);
v___x_3445_ = v___x_3438_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = 5;
v___x_3447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3448_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3441_, v___x_3445_, v___x_3446_, v___x_3447_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3464_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3464_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3464_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
if (lean_obj_tag(v_a_3449_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3463_; 
lean_del_object(v___x_3424_);
v_a_3453_ = lean_ctor_get(v_a_3449_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3449_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3455_ = v_a_3449_;
v_isShared_3456_ = v_isSharedCheck_3463_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v_a_3449_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3463_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3458_);
v___x_3460_ = v___x_3451_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_dec_ref(v_a_3449_);
lean_del_object(v___x_3451_);
v_a_3428_ = v___x_3440_;
goto v___jp_3427_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3424_);
v_a_3465_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3448_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3448_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
}
v___jp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v_a_3428_);
lean_ctor_set(v___x_3424_, 0, v___x_3426_);
v___x_3430_ = v___x_3424_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_a_3428_);
v___x_3430_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3409_, v___x_3431_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3405_, v_danglingDot_3406_, v_as_3407_, v_sz_3408_, v___x_3432_, v___x_3430_, v___y_3411_, v___y_3412_);
return v___x_3433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17___boxed(lean_object* v_id_3477_, lean_object* v_danglingDot_3478_, lean_object* v_as_3479_, lean_object* v_sz_3480_, lean_object* v_i_3481_, lean_object* v_b_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
uint8_t v_danglingDot_boxed_3491_; size_t v_sz_boxed_3492_; size_t v_i_boxed_3493_; lean_object* v_res_3494_; 
v_danglingDot_boxed_3491_ = lean_unbox(v_danglingDot_3478_);
v_sz_boxed_3492_ = lean_unbox_usize(v_sz_3480_);
lean_dec(v_sz_3480_);
v_i_boxed_3493_ = lean_unbox_usize(v_i_3481_);
lean_dec(v_i_3481_);
v_res_3494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3477_, v_danglingDot_boxed_3491_, v_as_3479_, v_sz_boxed_3492_, v_i_boxed_3493_, v_b_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v_as_3479_);
lean_dec(v_id_3477_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object* v_init_3495_, lean_object* v_id_3496_, uint8_t v_danglingDot_3497_, lean_object* v_n_3498_, lean_object* v_b_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
if (lean_obj_tag(v_n_3498_) == 0)
{
lean_object* v_cs_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3564_; 
v_cs_3508_ = lean_ctor_get(v_n_3498_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_n_3498_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3510_ = v_n_3498_;
v_isShared_3511_ = v_isSharedCheck_3564_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_cs_3508_);
lean_dec(v_n_3498_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3564_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; size_t v_sz_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
lean_ctor_set(v___x_3513_, 1, v_b_3499_);
v_sz_3514_ = lean_array_size(v_cs_3508_);
v___x_3515_ = ((size_t)0ULL);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3495_, v_id_3496_, v_danglingDot_3497_, v_cs_3508_, v_sz_3514_, v___x_3515_, v___x_3513_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_cs_3508_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3555_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3555_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3555_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
if (lean_obj_tag(v_a_3517_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3531_; 
lean_del_object(v___x_3510_);
v_a_3521_ = lean_ctor_get(v_a_3517_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3517_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3523_ = v_a_3517_;
v_isShared_3524_ = v_isSharedCheck_3531_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v_a_3517_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3531_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3526_);
v___x_3528_ = v___x_3519_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3554_; 
v_a_3532_ = lean_ctor_get(v_a_3517_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_a_3517_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3534_ = v_a_3517_;
v_isShared_3535_ = v_isSharedCheck_3554_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v_a_3517_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3554_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v_fst_3536_; 
v_fst_3536_ = lean_ctor_get(v_a_3532_, 0);
if (lean_obj_tag(v_fst_3536_) == 0)
{
lean_object* v_snd_3537_; lean_object* v___x_3539_; 
v_snd_3537_ = lean_ctor_get(v_a_3532_, 1);
lean_inc(v_snd_3537_);
lean_dec(v_a_3532_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set_tag(v___x_3510_, 1);
lean_ctor_set(v___x_3510_, 0, v_snd_3537_);
v___x_3539_ = v___x_3510_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_snd_3537_);
v___x_3539_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3539_);
v___x_3541_ = v___x_3534_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3541_);
v___x_3543_ = v___x_3519_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_val_3547_; lean_object* v___x_3549_; 
lean_inc_ref(v_fst_3536_);
lean_dec(v_a_3532_);
lean_del_object(v___x_3510_);
v_val_3547_ = lean_ctor_get(v_fst_3536_, 0);
lean_inc(v_val_3547_);
lean_dec_ref(v_fst_3536_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v_val_3547_);
v___x_3549_ = v___x_3534_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_val_3547_);
v___x_3549_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3551_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3549_);
v___x_3551_ = v___x_3519_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3510_);
v_a_3556_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3516_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3516_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
else
{
lean_object* v_vs_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3621_; 
v_vs_3565_ = lean_ctor_get(v_n_3498_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_n_3498_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3567_ = v_n_3498_;
v_isShared_3568_ = v_isSharedCheck_3621_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_vs_3565_);
lean_dec(v_n_3498_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3621_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; size_t v_sz_3571_; size_t v___x_3572_; lean_object* v___x_3573_; 
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
lean_ctor_set(v___x_3570_, 1, v_b_3499_);
v_sz_3571_ = lean_array_size(v_vs_3565_);
v___x_3572_ = ((size_t)0ULL);
v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3496_, v_danglingDot_3497_, v_vs_3565_, v_sz_3571_, v___x_3572_, v___x_3570_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_vs_3565_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3612_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3612_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3612_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
if (lean_obj_tag(v_a_3574_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3588_; 
lean_del_object(v___x_3567_);
v_a_3578_ = lean_ctor_get(v_a_3574_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3580_ = v_a_3574_;
v_isShared_3581_ = v_isSharedCheck_3588_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v_a_3574_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3588_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3583_);
v___x_3585_ = v___x_3576_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3611_; 
v_a_3589_ = lean_ctor_get(v_a_3574_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3591_ = v_a_3574_;
v_isShared_3592_ = v_isSharedCheck_3611_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v_a_3574_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3611_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_fst_3593_; 
v_fst_3593_ = lean_ctor_get(v_a_3589_, 0);
if (lean_obj_tag(v_fst_3593_) == 0)
{
lean_object* v_snd_3594_; lean_object* v___x_3596_; 
v_snd_3594_ = lean_ctor_get(v_a_3589_, 1);
lean_inc(v_snd_3594_);
lean_dec(v_a_3589_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v_snd_3594_);
v___x_3596_ = v___x_3567_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_snd_3594_);
v___x_3596_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3598_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3596_);
v___x_3598_ = v___x_3591_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3598_);
v___x_3600_ = v___x_3576_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_val_3604_; lean_object* v___x_3606_; 
lean_inc_ref(v_fst_3593_);
lean_dec(v_a_3589_);
lean_del_object(v___x_3567_);
v_val_3604_ = lean_ctor_get(v_fst_3593_, 0);
lean_inc(v_val_3604_);
lean_dec_ref(v_fst_3593_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v_val_3604_);
v___x_3606_ = v___x_3591_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_val_3604_);
v___x_3606_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3606_);
v___x_3608_ = v___x_3576_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_del_object(v___x_3567_);
v_a_3613_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3573_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3573_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(lean_object* v_init_3622_, lean_object* v_id_3623_, uint8_t v_danglingDot_3624_, lean_object* v_as_3625_, size_t v_sz_3626_, size_t v_i_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_usize_dec_lt(v_i_3627_, v_sz_3626_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_b_3628_);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
return v___x_3639_;
}
else
{
lean_object* v_snd_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3693_; 
v_snd_3640_ = lean_ctor_get(v_b_3628_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_b_3628_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; 
v_unused_3694_ = lean_ctor_get(v_b_3628_, 0);
lean_dec(v_unused_3694_);
v___x_3642_ = v_b_3628_;
v_isShared_3643_ = v_isSharedCheck_3693_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_snd_3640_);
lean_dec(v_b_3628_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3693_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_a_3644_; lean_object* v___x_3645_; 
v_a_3644_ = lean_array_uget_borrowed(v_as_3625_, v_i_3627_);
lean_inc(v_snd_3640_);
lean_inc(v_a_3644_);
v___x_3645_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3622_, v_id_3623_, v_danglingDot_3624_, v_a_3644_, v_snd_3640_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3684_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3684_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3684_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
if (lean_obj_tag(v_a_3646_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3660_; 
lean_del_object(v___x_3642_);
lean_dec(v_snd_3640_);
v_a_3650_ = lean_ctor_get(v_a_3646_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_a_3646_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3652_ = v_a_3646_;
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v_a_3646_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3655_);
v___x_3657_ = v___x_3648_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3683_; 
v_a_3661_ = lean_ctor_get(v_a_3646_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_a_3646_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3663_ = v_a_3646_;
v_isShared_3664_ = v_isSharedCheck_3683_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v_a_3646_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3683_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
if (lean_obj_tag(v_a_3661_) == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3665_, 0, v_a_3661_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3665_);
v___x_3667_ = v___x_3642_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_snd_3640_);
v___x_3667_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3667_);
v___x_3669_ = v___x_3663_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3669_);
v___x_3671_ = v___x_3648_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_del_object(v___x_3663_);
lean_del_object(v___x_3648_);
lean_dec(v_snd_3640_);
v_a_3675_ = lean_ctor_get(v_a_3661_, 0);
lean_inc(v_a_3675_);
lean_dec_ref(v_a_3661_);
v___x_3676_ = lean_box(0);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 1, v_a_3675_);
lean_ctor_set(v___x_3642_, 0, v___x_3676_);
v___x_3678_ = v___x_3642_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_a_3675_);
v___x_3678_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
size_t v___x_3679_; size_t v___x_3680_; 
v___x_3679_ = ((size_t)1ULL);
v___x_3680_ = lean_usize_add(v_i_3627_, v___x_3679_);
v_i_3627_ = v___x_3680_;
v_b_3628_ = v___x_3678_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_del_object(v___x_3642_);
lean_dec(v_snd_3640_);
v_a_3685_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3645_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3645_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16___boxed(lean_object* v_init_3695_, lean_object* v_id_3696_, lean_object* v_danglingDot_3697_, lean_object* v_as_3698_, lean_object* v_sz_3699_, lean_object* v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
uint8_t v_danglingDot_boxed_3710_; size_t v_sz_boxed_3711_; size_t v_i_boxed_3712_; lean_object* v_res_3713_; 
v_danglingDot_boxed_3710_ = lean_unbox(v_danglingDot_3697_);
v_sz_boxed_3711_ = lean_unbox_usize(v_sz_3699_);
lean_dec(v_sz_3699_);
v_i_boxed_3712_ = lean_unbox_usize(v_i_3700_);
lean_dec(v_i_3700_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3695_, v_id_3696_, v_danglingDot_boxed_3710_, v_as_3698_, v_sz_boxed_3711_, v_i_boxed_3712_, v_b_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v_as_3698_);
lean_dec(v_id_3696_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object* v_init_3714_, lean_object* v_id_3715_, lean_object* v_danglingDot_3716_, lean_object* v_n_3717_, lean_object* v_b_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v_danglingDot_boxed_3727_; lean_object* v_res_3728_; 
v_danglingDot_boxed_3727_ = lean_unbox(v_danglingDot_3716_);
v_res_3728_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3714_, v_id_3715_, v_danglingDot_boxed_3727_, v_n_3717_, v_b_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v_id_3715_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(lean_object* v_id_3729_, uint8_t v_danglingDot_3730_, lean_object* v_as_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v___x_3738_; 
v___x_3738_ = lean_usize_dec_lt(v_i_3733_, v_sz_3732_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v_b_3734_);
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
else
{
lean_object* v_snd_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3794_; 
v_snd_3741_ = lean_ctor_get(v_b_3734_, 1);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_b_3734_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; 
v_unused_3795_ = lean_ctor_get(v_b_3734_, 0);
lean_dec(v_unused_3795_);
v___x_3743_ = v_b_3734_;
v_isShared_3744_ = v_isSharedCheck_3794_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_snd_3741_);
lean_dec(v_b_3734_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3794_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v_a_3747_; lean_object* v_a_3754_; 
v___x_3745_ = lean_box(0);
v_a_3754_ = lean_array_uget(v_as_3731_, v_i_3733_);
if (lean_obj_tag(v_a_3754_) == 0)
{
v_a_3747_ = v_snd_3741_;
goto v___jp_3746_;
}
else
{
lean_object* v_val_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v_snd_3741_);
v_val_3755_ = lean_ctor_get(v_a_3754_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v_a_3754_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3757_ = v_a_3754_;
v_isShared_3758_ = v_isSharedCheck_3793_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_val_3755_);
lean_dec(v_a_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3793_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3759_ = lean_box(0);
v___x_3760_ = l_Lean_LocalDecl_userName(v_val_3755_);
v___x_3761_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3729_, v___x_3760_, v_danglingDot_3730_);
if (v___x_3761_ == 0)
{
lean_dec(v___x_3760_);
lean_del_object(v___x_3757_);
lean_dec(v_val_3755_);
v_a_3747_ = v___x_3759_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = l_Lean_LocalDecl_fvarId(v_val_3755_);
lean_dec(v_val_3755_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3762_);
v___x_3764_ = v___x_3757_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
uint8_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3765_ = 5;
v___x_3766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3767_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3760_, v___x_3764_, v___x_3765_, v___x_3766_, v___y_3735_, v___y_3736_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3783_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3770_ = v___x_3767_;
v_isShared_3771_ = v_isSharedCheck_3783_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3783_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
if (lean_obj_tag(v_a_3768_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3782_; 
lean_del_object(v___x_3743_);
v_a_3772_ = lean_ctor_get(v_a_3768_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_a_3768_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3774_ = v_a_3768_;
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v_a_3768_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v___x_3777_);
v___x_3779_ = v___x_3770_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_dec_ref(v_a_3768_);
lean_del_object(v___x_3770_);
v_a_3747_ = v___x_3759_;
goto v___jp_3746_;
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_del_object(v___x_3743_);
v_a_3784_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3767_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3767_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
}
}
v___jp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 1, v_a_3747_);
lean_ctor_set(v___x_3743_, 0, v___x_3745_);
v___x_3749_ = v___x_3743_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_a_3747_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
size_t v___x_3750_; size_t v___x_3751_; 
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_add(v_i_3733_, v___x_3750_);
v_i_3733_ = v___x_3751_;
v_b_3734_ = v___x_3749_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_id_3796_, lean_object* v_danglingDot_3797_, lean_object* v_as_3798_, lean_object* v_sz_3799_, lean_object* v_i_3800_, lean_object* v_b_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
uint8_t v_danglingDot_boxed_3805_; size_t v_sz_boxed_3806_; size_t v_i_boxed_3807_; lean_object* v_res_3808_; 
v_danglingDot_boxed_3805_ = lean_unbox(v_danglingDot_3797_);
v_sz_boxed_3806_ = lean_unbox_usize(v_sz_3799_);
lean_dec(v_sz_3799_);
v_i_boxed_3807_ = lean_unbox_usize(v_i_3800_);
lean_dec(v_i_3800_);
v_res_3808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3796_, v_danglingDot_boxed_3805_, v_as_3798_, v_sz_boxed_3806_, v_i_boxed_3807_, v_b_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v_as_3798_);
lean_dec(v_id_3796_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(lean_object* v_id_3809_, uint8_t v_danglingDot_3810_, lean_object* v_as_3811_, size_t v_sz_3812_, size_t v_i_3813_, lean_object* v_b_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v___x_3823_; 
v___x_3823_ = lean_usize_dec_lt(v_i_3813_, v_sz_3812_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3814_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
return v___x_3825_;
}
else
{
lean_object* v_snd_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3879_; 
v_snd_3826_ = lean_ctor_get(v_b_3814_, 1);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_b_3814_);
if (v_isSharedCheck_3879_ == 0)
{
lean_object* v_unused_3880_; 
v_unused_3880_ = lean_ctor_get(v_b_3814_, 0);
lean_dec(v_unused_3880_);
v___x_3828_ = v_b_3814_;
v_isShared_3829_ = v_isSharedCheck_3879_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_snd_3826_);
lean_dec(v_b_3814_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3879_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; lean_object* v_a_3832_; lean_object* v_a_3839_; 
v___x_3830_ = lean_box(0);
v_a_3839_ = lean_array_uget(v_as_3811_, v_i_3813_);
if (lean_obj_tag(v_a_3839_) == 0)
{
v_a_3832_ = v_snd_3826_;
goto v___jp_3831_;
}
else
{
lean_object* v_val_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3878_; 
lean_dec(v_snd_3826_);
v_val_3840_ = lean_ctor_get(v_a_3839_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3839_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3842_ = v_a_3839_;
v_isShared_3843_ = v_isSharedCheck_3878_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_val_3840_);
lean_dec(v_a_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3878_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v___x_3844_ = lean_box(0);
v___x_3845_ = l_Lean_LocalDecl_userName(v_val_3840_);
v___x_3846_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3809_, v___x_3845_, v_danglingDot_3810_);
if (v___x_3846_ == 0)
{
lean_dec(v___x_3845_);
lean_del_object(v___x_3842_);
lean_dec(v_val_3840_);
v_a_3832_ = v___x_3844_;
goto v___jp_3831_;
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = l_Lean_LocalDecl_fvarId(v_val_3840_);
lean_dec(v_val_3840_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3847_);
v___x_3849_ = v___x_3842_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3850_ = 5;
v___x_3851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3852_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3845_, v___x_3849_, v___x_3850_, v___x_3851_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3868_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3868_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3868_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
if (lean_obj_tag(v_a_3853_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3867_; 
lean_del_object(v___x_3828_);
v_a_3857_ = lean_ctor_get(v_a_3853_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_a_3853_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3859_ = v_a_3853_;
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v_a_3853_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3864_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3862_);
v___x_3864_ = v___x_3855_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_dec_ref(v_a_3853_);
lean_del_object(v___x_3855_);
v_a_3832_ = v___x_3844_;
goto v___jp_3831_;
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_del_object(v___x_3828_);
v_a_3869_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3852_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3852_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
}
}
v___jp_3831_:
{
lean_object* v___x_3834_; 
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 1, v_a_3832_);
lean_ctor_set(v___x_3828_, 0, v___x_3830_);
v___x_3834_ = v___x_3828_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_a_3832_);
v___x_3834_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
size_t v___x_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
v___x_3835_ = ((size_t)1ULL);
v___x_3836_ = lean_usize_add(v_i_3813_, v___x_3835_);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3809_, v_danglingDot_3810_, v_as_3811_, v_sz_3812_, v___x_3836_, v___x_3834_, v___y_3815_, v___y_3816_);
return v___x_3837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12___boxed(lean_object* v_id_3881_, lean_object* v_danglingDot_3882_, lean_object* v_as_3883_, lean_object* v_sz_3884_, lean_object* v_i_3885_, lean_object* v_b_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
uint8_t v_danglingDot_boxed_3895_; size_t v_sz_boxed_3896_; size_t v_i_boxed_3897_; lean_object* v_res_3898_; 
v_danglingDot_boxed_3895_ = lean_unbox(v_danglingDot_3882_);
v_sz_boxed_3896_ = lean_unbox_usize(v_sz_3884_);
lean_dec(v_sz_3884_);
v_i_boxed_3897_ = lean_unbox_usize(v_i_3885_);
lean_dec(v_i_3885_);
v_res_3898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3881_, v_danglingDot_boxed_3895_, v_as_3883_, v_sz_boxed_3896_, v_i_boxed_3897_, v_b_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v_as_3883_);
lean_dec(v_id_3881_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object* v_id_3899_, uint8_t v_danglingDot_3900_, lean_object* v_t_3901_, lean_object* v_init_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_b_3912_; lean_object* v_root_3915_; lean_object* v_tail_3916_; lean_object* v___x_3917_; 
v_root_3915_ = lean_ctor_get(v_t_3901_, 0);
lean_inc_ref(v_root_3915_);
v_tail_3916_ = lean_ctor_get(v_t_3901_, 1);
lean_inc_ref(v_tail_3916_);
lean_dec_ref(v_t_3901_);
v___x_3917_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3902_, v_id_3899_, v_danglingDot_3900_, v_root_3915_, v_init_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3979_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3979_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3979_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
if (lean_obj_tag(v_a_3918_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_tail_3916_);
v_a_3922_ = lean_ctor_get(v_a_3918_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_a_3918_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3924_ = v_a_3918_;
v_isShared_3925_ = v_isSharedCheck_3932_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v_a_3918_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3932_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3929_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3927_);
v___x_3929_ = v___x_3920_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3933_; 
lean_del_object(v___x_3920_);
v_a_3933_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_a_3933_);
lean_dec_ref(v_a_3918_);
if (lean_obj_tag(v_a_3933_) == 0)
{
lean_object* v_a_3934_; 
lean_dec_ref(v_tail_3916_);
v_a_3934_ = lean_ctor_get(v_a_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v_a_3933_);
v_b_3912_ = v_a_3934_;
goto v___jp_3911_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; size_t v_sz_3938_; size_t v___x_3939_; lean_object* v___x_3940_; 
v_a_3935_ = lean_ctor_get(v_a_3933_, 0);
lean_inc(v_a_3935_);
lean_dec_ref(v_a_3933_);
v___x_3936_ = lean_box(0);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v_a_3935_);
v_sz_3938_ = lean_array_size(v_tail_3916_);
v___x_3939_ = ((size_t)0ULL);
v___x_3940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3899_, v_danglingDot_3900_, v_tail_3916_, v_sz_3938_, v___x_3939_, v___x_3937_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec_ref(v_tail_3916_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3970_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3943_ = v___x_3940_;
v_isShared_3944_ = v_isSharedCheck_3970_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3940_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3970_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
if (lean_obj_tag(v_a_3941_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3955_; 
v_a_3945_ = lean_ctor_get(v_a_3941_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_a_3941_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3947_ = v_a_3941_;
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v_a_3941_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v___x_3950_);
v___x_3952_ = v___x_3943_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3969_; 
v_a_3956_ = lean_ctor_get(v_a_3941_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_a_3941_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3958_ = v_a_3941_;
v_isShared_3959_ = v_isSharedCheck_3969_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v_a_3941_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3969_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_fst_3960_; 
v_fst_3960_ = lean_ctor_get(v_a_3956_, 0);
if (lean_obj_tag(v_fst_3960_) == 0)
{
lean_object* v_snd_3961_; lean_object* v___x_3963_; 
v_snd_3961_ = lean_ctor_get(v_a_3956_, 1);
lean_inc(v_snd_3961_);
lean_dec(v_a_3956_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v_snd_3961_);
v___x_3963_ = v___x_3958_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_snd_3961_);
v___x_3963_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v___x_3963_);
v___x_3965_ = v___x_3943_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
else
{
lean_object* v_val_3968_; 
lean_inc_ref(v_fst_3960_);
lean_del_object(v___x_3958_);
lean_dec(v_a_3956_);
lean_del_object(v___x_3943_);
v_val_3968_ = lean_ctor_get(v_fst_3960_, 0);
lean_inc(v_val_3968_);
lean_dec_ref(v_fst_3960_);
v_b_3912_ = v_val_3968_;
goto v___jp_3911_;
}
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3940_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3940_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v_tail_3916_);
v_a_3980_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3917_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3917_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
v___jp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_b_3912_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
return v___x_3914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object* v_id_3988_, lean_object* v_danglingDot_3989_, lean_object* v_t_3990_, lean_object* v_init_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v_danglingDot_boxed_4000_; lean_object* v_res_4001_; 
v_danglingDot_boxed_4000_ = lean_unbox(v_danglingDot_3989_);
v_res_4001_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_3988_, v_danglingDot_boxed_4000_, v_t_3990_, v_init_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v_id_3988_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object* v_as_4002_, size_t v_sz_4003_, size_t v_i_4004_, lean_object* v_b_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_usize_dec_lt(v_i_4004_, v_sz_4003_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v_b_4005_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4013_; 
v_a_4012_ = lean_array_uget_borrowed(v_as_4002_, v_i_4004_);
lean_inc(v_a_4012_);
v___x_4013_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_4012_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
if (lean_obj_tag(v_a_4014_) == 0)
{
lean_dec_ref(v_a_4014_);
return v___x_4013_;
}
else
{
lean_object* v___x_4015_; size_t v___x_4016_; size_t v___x_4017_; 
lean_dec_ref(v_a_4014_);
lean_dec_ref(v___x_4013_);
v___x_4015_ = lean_box(0);
v___x_4016_ = ((size_t)1ULL);
v___x_4017_ = lean_usize_add(v_i_4004_, v___x_4016_);
v_i_4004_ = v___x_4017_;
v_b_4005_ = v___x_4015_;
goto _start;
}
}
else
{
return v___x_4013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object* v_as_4019_, lean_object* v_sz_4020_, lean_object* v_i_4021_, lean_object* v_b_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
size_t v_sz_boxed_4026_; size_t v_i_boxed_4027_; lean_object* v_res_4028_; 
v_sz_boxed_4026_ = lean_unbox_usize(v_sz_4020_);
lean_dec(v_sz_4020_);
v_i_boxed_4027_ = lean_unbox_usize(v_i_4021_);
lean_dec(v_i_4021_);
v_res_4028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4019_, v_sz_boxed_4026_, v_i_boxed_4027_, v_b_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec_ref(v_as_4019_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object* v___x_4029_, lean_object* v_a_4030_, lean_object* v___x_4031_, lean_object* v_ns_4032_, lean_object* v_id_4033_, uint8_t v_danglingDot_4034_, lean_object* v_alias_4035_, lean_object* v_declNames_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
uint8_t v___y_4046_; uint8_t v___x_4050_; 
v___x_4050_ = l_Lean_Name_isPrefixOf(v_ns_4032_, v_alias_4035_);
if (v___x_4050_ == 0)
{
v___y_4046_ = v___x_4050_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4051_ = lean_box(0);
lean_inc(v_alias_4035_);
v___x_4052_ = l_Lean_Name_replacePrefix(v_alias_4035_, v_ns_4032_, v___x_4051_);
v___x_4053_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4033_, v___x_4052_, v_danglingDot_4034_);
lean_dec(v___x_4052_);
v___y_4046_ = v___x_4053_;
goto v___jp_4045_;
}
v___jp_4045_:
{
if (v___y_4046_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_dec(v_declNames_4036_);
lean_dec(v_alias_4035_);
lean_dec_ref(v___x_4031_);
v___x_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4029_);
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
else
{
lean_object* v___x_4049_; 
v___x_4049_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4030_, v___x_4031_, v_alias_4035_, v_declNames_4036_, v___y_4037_, v___y_4038_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v_alias_4035_);
return v___x_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_4054_, lean_object* v_a_4055_, lean_object* v___x_4056_, lean_object* v_ns_4057_, lean_object* v_id_4058_, lean_object* v_danglingDot_4059_, lean_object* v_alias_4060_, lean_object* v_declNames_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
uint8_t v_danglingDot_boxed_4070_; lean_object* v_res_4071_; 
v_danglingDot_boxed_4070_ = lean_unbox(v_danglingDot_4059_);
v_res_4071_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_4054_, v_a_4055_, v___x_4056_, v_ns_4057_, v_id_4058_, v_danglingDot_boxed_4070_, v_alias_4060_, v_declNames_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v_id_4058_);
lean_dec(v_ns_4057_);
lean_dec_ref(v_a_4055_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(lean_object* v_a_4072_, lean_object* v___x_4073_, lean_object* v_id_4074_, uint8_t v_danglingDot_4075_, lean_object* v_as_x27_4076_, lean_object* v_b_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_a_4087_; 
if (lean_obj_tag(v_as_x27_4076_) == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
lean_dec(v_id_4074_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v_a_4072_);
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v_b_4077_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
return v___x_4091_;
}
else
{
lean_object* v_head_4092_; lean_object* v_tail_4093_; lean_object* v___x_4094_; 
v_head_4092_ = lean_ctor_get(v_as_x27_4076_, 0);
lean_inc(v_head_4092_);
v_tail_4093_ = lean_ctor_get(v_as_x27_4076_, 1);
lean_inc(v_tail_4093_);
lean_dec_ref(v_as_x27_4076_);
v___x_4094_ = lean_box(0);
if (lean_obj_tag(v_head_4092_) == 0)
{
lean_object* v_ns_4095_; lean_object* v___x_4096_; lean_object* v___f_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_ns_4095_ = lean_ctor_get(v_head_4092_, 0);
lean_inc(v_ns_4095_);
lean_dec_ref(v_head_4092_);
v___x_4096_ = lean_box(v_danglingDot_4075_);
lean_inc(v_id_4074_);
lean_inc_ref_n(v___x_4073_, 2);
lean_inc_ref(v_a_4072_);
v___f_4097_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4097_, 0, v___x_4094_);
lean_closure_set(v___f_4097_, 1, v_a_4072_);
lean_closure_set(v___f_4097_, 2, v___x_4073_);
lean_closure_set(v___f_4097_, 3, v_ns_4095_);
lean_closure_set(v___f_4097_, 4, v_id_4074_);
lean_closure_set(v___f_4097_, 5, v___x_4096_);
v___x_4098_ = l_Lean_getAliasState(v___x_4073_);
v___x_4099_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4098_, v___f_4097_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
if (lean_obj_tag(v_a_4100_) == 0)
{
lean_object* v_a_4101_; 
lean_dec(v_tail_4093_);
lean_dec(v_id_4074_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v_a_4072_);
v_a_4101_ = lean_ctor_get(v_a_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v_a_4100_);
v_a_4087_ = v_a_4101_;
goto v___jp_4086_;
}
else
{
lean_dec_ref(v_a_4100_);
v_as_x27_4076_ = v_tail_4093_;
v_b_4077_ = v___x_4094_;
goto _start;
}
}
else
{
lean_dec(v_tail_4093_);
lean_dec(v_id_4074_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v_a_4072_);
return v___x_4099_;
}
}
else
{
lean_object* v_id_4103_; lean_object* v_declName_4104_; uint8_t v___x_4105_; 
v_id_4103_ = lean_ctor_get(v_head_4092_, 0);
lean_inc(v_id_4103_);
v_declName_4104_ = lean_ctor_get(v_head_4092_, 1);
lean_inc_n(v_declName_4104_, 2);
lean_dec_ref(v_head_4092_);
lean_inc_ref(v___x_4073_);
v___x_4105_ = l_Lean_Server_Completion_allowCompletion(v_a_4072_, v___x_4073_, v_declName_4104_);
if (v___x_4105_ == 0)
{
lean_dec(v_declName_4104_);
lean_dec(v_id_4103_);
v_as_x27_4076_ = v_tail_4093_;
v_b_4077_ = v___x_4094_;
goto _start;
}
else
{
uint8_t v___x_4107_; 
v___x_4107_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4074_, v_id_4103_, v_danglingDot_4075_);
if (v___x_4107_ == 0)
{
lean_dec(v_declName_4104_);
lean_dec(v_id_4103_);
v_as_x27_4076_ = v_tail_4093_;
v_b_4077_ = v___x_4094_;
goto _start;
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4109_ = l_Lean_Name_getString_x21(v_id_4103_);
lean_dec(v_id_4103_);
v___x_4110_ = lean_box(0);
v___x_4111_ = l_Lean_Name_str___override(v___x_4110_, v___x_4109_);
v___x_4112_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4111_, v_declName_4104_, v___y_4078_, v___y_4079_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_dec_ref(v___x_4112_);
v_as_x27_4076_ = v_tail_4093_;
v_b_4077_ = v___x_4094_;
goto _start;
}
else
{
lean_dec(v_tail_4093_);
lean_dec(v_id_4074_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v_a_4072_);
return v___x_4112_;
}
}
}
}
}
v___jp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v_a_4087_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
return v___x_4089_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg___boxed(lean_object* v_a_4114_, lean_object* v___x_4115_, lean_object* v_id_4116_, lean_object* v_danglingDot_4117_, lean_object* v_as_x27_4118_, lean_object* v_b_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
uint8_t v_danglingDot_boxed_4128_; lean_object* v_res_4129_; 
v_danglingDot_boxed_4128_ = lean_unbox(v_danglingDot_4117_);
v_res_4129_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4114_, v___x_4115_, v_id_4116_, v_danglingDot_boxed_4128_, v_as_x27_4118_, v_b_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_id_4130_, uint8_t v_danglingDot_4131_, lean_object* v_a_4132_, lean_object* v___x_4133_, lean_object* v_as_4134_, lean_object* v_as_x27_4135_, lean_object* v_b_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_a_4146_; 
if (lean_obj_tag(v_as_x27_4135_) == 0)
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_dec_ref(v___x_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_id_4130_);
v___x_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_b_4136_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
return v___x_4150_;
}
else
{
lean_object* v_head_4151_; lean_object* v_tail_4152_; lean_object* v___x_4153_; 
v_head_4151_ = lean_ctor_get(v_as_x27_4135_, 0);
lean_inc(v_head_4151_);
v_tail_4152_ = lean_ctor_get(v_as_x27_4135_, 1);
lean_inc(v_tail_4152_);
lean_dec_ref(v_as_x27_4135_);
v___x_4153_ = lean_box(0);
if (lean_obj_tag(v_head_4151_) == 0)
{
lean_object* v_ns_4154_; lean_object* v___x_4155_; lean_object* v___f_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_ns_4154_ = lean_ctor_get(v_head_4151_, 0);
lean_inc(v_ns_4154_);
lean_dec_ref(v_head_4151_);
v___x_4155_ = lean_box(v_danglingDot_4131_);
lean_inc(v_id_4130_);
lean_inc_ref_n(v___x_4133_, 2);
lean_inc_ref(v_a_4132_);
v___f_4156_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4156_, 0, v___x_4153_);
lean_closure_set(v___f_4156_, 1, v_a_4132_);
lean_closure_set(v___f_4156_, 2, v___x_4133_);
lean_closure_set(v___f_4156_, 3, v_ns_4154_);
lean_closure_set(v___f_4156_, 4, v_id_4130_);
lean_closure_set(v___f_4156_, 5, v___x_4155_);
v___x_4157_ = l_Lean_getAliasState(v___x_4133_);
v___x_4158_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4157_, v___f_4156_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref(v___x_4158_);
if (lean_obj_tag(v_a_4159_) == 0)
{
lean_object* v_a_4160_; 
lean_dec(v_tail_4152_);
lean_dec_ref(v___x_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_id_4130_);
v_a_4160_ = lean_ctor_get(v_a_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v_a_4159_);
v_a_4146_ = v_a_4160_;
goto v___jp_4145_;
}
else
{
lean_object* v___x_4161_; 
lean_dec_ref(v_a_4159_);
v___x_4161_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4132_, v___x_4133_, v_id_4130_, v_danglingDot_4131_, v_tail_4152_, v___x_4153_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4161_;
}
}
else
{
lean_dec(v_tail_4152_);
lean_dec_ref(v___x_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_id_4130_);
return v___x_4158_;
}
}
else
{
lean_object* v_id_4162_; lean_object* v_declName_4163_; uint8_t v___x_4164_; 
v_id_4162_ = lean_ctor_get(v_head_4151_, 0);
lean_inc(v_id_4162_);
v_declName_4163_ = lean_ctor_get(v_head_4151_, 1);
lean_inc_n(v_declName_4163_, 2);
lean_dec_ref(v_head_4151_);
lean_inc_ref(v___x_4133_);
v___x_4164_ = l_Lean_Server_Completion_allowCompletion(v_a_4132_, v___x_4133_, v_declName_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
lean_dec(v_declName_4163_);
lean_dec(v_id_4162_);
v___x_4165_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4132_, v___x_4133_, v_id_4130_, v_danglingDot_4131_, v_tail_4152_, v___x_4153_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4165_;
}
else
{
uint8_t v___x_4166_; 
v___x_4166_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4130_, v_id_4162_, v_danglingDot_4131_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; 
lean_dec(v_declName_4163_);
lean_dec(v_id_4162_);
v___x_4167_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4132_, v___x_4133_, v_id_4130_, v_danglingDot_4131_, v_tail_4152_, v___x_4153_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4167_;
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4168_ = l_Lean_Name_getString_x21(v_id_4162_);
lean_dec(v_id_4162_);
v___x_4169_ = lean_box(0);
v___x_4170_ = l_Lean_Name_str___override(v___x_4169_, v___x_4168_);
v___x_4171_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4170_, v_declName_4163_, v___y_4137_, v___y_4138_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v___x_4171_);
v___x_4172_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4132_, v___x_4133_, v_id_4130_, v_danglingDot_4131_, v_tail_4152_, v___x_4153_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4172_;
}
else
{
lean_dec(v_tail_4152_);
lean_dec_ref(v___x_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_id_4130_);
return v___x_4171_;
}
}
}
}
}
v___jp_4145_:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_a_4146_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_id_4173_, lean_object* v_danglingDot_4174_, lean_object* v_a_4175_, lean_object* v___x_4176_, lean_object* v_as_4177_, lean_object* v_as_x27_4178_, lean_object* v_b_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v_danglingDot_boxed_4188_; lean_object* v_res_4189_; 
v_danglingDot_boxed_4188_ = lean_unbox(v_danglingDot_4174_);
v_res_4189_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4173_, v_danglingDot_boxed_4188_, v_a_4175_, v___x_4176_, v_as_4177_, v_as_x27_4178_, v_b_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v_as_4177_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4190_, lean_object* v_stx_4191_, lean_object* v_id_4192_, lean_object* v_hoverInfo_4193_, uint8_t v_danglingDot_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; uint8_t v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v_id_4255_; uint8_t v_danglingDot_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v_id_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; uint8_t v___x_4286_; 
v___x_4286_ = l_Lean_Name_hasMacroScopes(v_id_4192_);
if (v___x_4286_ == 0)
{
v_id_4275_ = v_id_4192_;
v___y_4276_ = v_a_4195_;
v___y_4277_ = v_a_4196_;
v___y_4278_ = v_a_4197_;
v___y_4279_ = v_a_4198_;
v___y_4280_ = v_a_4199_;
v___y_4281_ = v_a_4200_;
v___y_4282_ = v_a_4201_;
goto v___jp_4274_;
}
else
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Syntax_getHeadInfo(v_stx_4191_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_id_4288_; 
lean_dec_ref(v___x_4287_);
v_id_4288_ = lean_erase_macro_scopes(v_id_4192_);
v_id_4275_ = v_id_4288_;
v___y_4276_ = v_a_4195_;
v___y_4277_ = v_a_4196_;
v___y_4278_ = v_a_4197_;
v___y_4279_ = v_a_4198_;
v___y_4280_ = v_a_4199_;
v___y_4281_ = v_a_4200_;
v___y_4282_ = v_a_4201_;
goto v___jp_4274_;
}
else
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
lean_dec(v___x_4287_);
lean_dec(v_hoverInfo_4193_);
lean_dec(v_id_4192_);
lean_dec_ref(v_ctx_4190_);
v___x_4289_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
return v___x_4290_;
}
}
v___jp_4203_:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_st_ref_get(v___y_4206_);
v___x_4216_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4207_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
if (lean_obj_tag(v_a_4217_) == 0)
{
lean_dec_ref(v_a_4217_);
lean_dec(v___x_4215_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_ctx_4190_);
return v___x_4216_;
}
else
{
lean_object* v___x_4218_; lean_object* v_a_4219_; 
lean_dec_ref(v_a_4217_);
lean_dec_ref(v___x_4216_);
v___x_4218_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4214_);
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4219_);
if (lean_obj_tag(v_a_4219_) == 0)
{
lean_dec_ref(v_a_4219_);
lean_dec(v___x_4215_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_ctx_4190_);
return v___x_4218_;
}
else
{
lean_object* v_env_4220_; lean_object* v___x_4221_; 
lean_dec_ref(v_a_4219_);
lean_dec_ref(v___x_4218_);
v_env_4220_ = lean_ctor_get(v___x_4215_, 0);
lean_inc_ref_n(v_env_4220_, 2);
lean_dec(v___x_4215_);
v___x_4221_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4220_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_toCommandContextInfo_4222_; lean_object* v_a_4223_; lean_object* v_currNamespace_4224_; lean_object* v_openDecls_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_toCommandContextInfo_4222_ = lean_ctor_get(v_ctx_4190_, 0);
v_a_4223_ = lean_ctor_get(v___x_4221_, 0);
lean_inc_n(v_a_4223_, 2);
lean_dec_ref(v___x_4221_);
v_currNamespace_4224_ = lean_ctor_get(v_toCommandContextInfo_4222_, 5);
v_openDecls_4225_ = lean_ctor_get(v_toCommandContextInfo_4222_, 6);
v___x_4226_ = lean_box(0);
lean_inc(v_openDecls_4225_);
lean_inc_ref(v_env_4220_);
lean_inc(v___y_4208_);
v___x_4227_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___y_4208_, v___y_4211_, v_a_4223_, v_env_4220_, v_openDecls_4225_, v_openDecls_4225_, v___x_4226_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
if (lean_obj_tag(v_a_4228_) == 0)
{
lean_dec_ref(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec_ref(v_env_4220_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_ctx_4190_);
return v___x_4227_;
}
else
{
lean_object* v___f_4229_; lean_object* v___f_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
lean_dec_ref(v_a_4228_);
lean_dec_ref(v___x_4227_);
lean_inc_ref_n(v_env_4220_, 2);
v___f_4229_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4229_, 0, v_a_4223_);
lean_closure_set(v___f_4229_, 1, v_env_4220_);
lean_inc(v_currNamespace_4224_);
v___f_4230_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4230_, 0, v___y_4204_);
lean_closure_set(v___f_4230_, 1, v___f_4229_);
lean_closure_set(v___f_4230_, 2, v_currNamespace_4224_);
v___x_4231_ = l_Lean_getAliasState(v_env_4220_);
v___x_4232_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4231_, v___f_4230_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
if (lean_obj_tag(v_a_4233_) == 0)
{
lean_dec_ref(v_a_4233_);
lean_dec_ref(v_env_4220_);
lean_dec(v___y_4208_);
lean_dec_ref(v_ctx_4190_);
return v___x_4232_;
}
else
{
lean_dec_ref(v_a_4233_);
lean_dec_ref(v___x_4232_);
if (v___y_4211_ == 0)
{
if (lean_obj_tag(v___y_4208_) == 1)
{
lean_object* v_pre_4234_; 
v_pre_4234_ = lean_ctor_get(v___y_4208_, 0);
if (lean_obj_tag(v_pre_4234_) == 0)
{
lean_object* v_str_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; size_t v_sz_4238_; size_t v___x_4239_; lean_object* v___x_4240_; 
v_str_4235_ = lean_ctor_get(v___y_4208_, 1);
v___x_4236_ = l_Lean_Parser_getTokenTable(v_env_4220_);
v___x_4237_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4236_, v_str_4235_);
v_sz_4238_ = lean_array_size(v___x_4237_);
v___x_4239_ = ((size_t)0ULL);
v___x_4240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v___x_4237_, v_sz_4238_, v___x_4239_, v___x_4226_, v___y_4212_, v___y_4210_);
lean_dec_ref(v___x_4237_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
if (lean_obj_tag(v_a_4241_) == 0)
{
lean_dec_ref(v_a_4241_);
lean_dec_ref(v___y_4208_);
lean_dec_ref(v_ctx_4190_);
return v___x_4240_;
}
else
{
lean_object* v___x_4242_; 
lean_dec_ref(v_a_4241_);
lean_dec_ref(v___x_4240_);
v___x_4242_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4190_, v___y_4208_, v___y_4211_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
return v___x_4242_;
}
}
else
{
lean_dec_ref(v___y_4208_);
lean_dec_ref(v_ctx_4190_);
return v___x_4240_;
}
}
else
{
lean_object* v___x_4243_; 
lean_dec_ref(v_env_4220_);
v___x_4243_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4190_, v___y_4208_, v___y_4211_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
return v___x_4243_;
}
}
else
{
lean_object* v___x_4244_; 
lean_dec_ref(v_env_4220_);
v___x_4244_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4190_, v___y_4208_, v___y_4211_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
return v___x_4244_;
}
}
else
{
lean_object* v___x_4245_; 
lean_dec_ref(v_env_4220_);
v___x_4245_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4190_, v___y_4208_, v___y_4211_, v___y_4212_, v___y_4210_, v___y_4214_, v___y_4209_, v___y_4205_, v___y_4213_, v___y_4206_);
return v___x_4245_;
}
}
}
else
{
lean_dec_ref(v_env_4220_);
lean_dec(v___y_4208_);
lean_dec_ref(v_ctx_4190_);
return v___x_4232_;
}
}
}
else
{
lean_dec(v_a_4223_);
lean_dec_ref(v_env_4220_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_ctx_4190_);
return v___x_4227_;
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_env_4220_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_ctx_4190_);
v_a_4246_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4221_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4221_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4215_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_ctx_4190_);
return v___x_4216_;
}
}
v___jp_4254_:
{
lean_object* v___x_4264_; lean_object* v___f_4265_; lean_object* v___x_4266_; lean_object* v___f_4267_; uint8_t v___x_4268_; 
v___x_4264_ = lean_box(v_danglingDot_4256_);
lean_inc_n(v_id_4255_, 2);
lean_inc_ref(v_ctx_4190_);
v___f_4265_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4265_, 0, v_ctx_4190_);
lean_closure_set(v___f_4265_, 1, v_id_4255_);
lean_closure_set(v___f_4265_, 2, v___x_4264_);
v___x_4266_ = lean_box(v_danglingDot_4256_);
v___f_4267_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4267_, 0, v_id_4255_);
lean_closure_set(v___f_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_Name_isAtomic(v_id_4255_);
if (v___x_4268_ == 0)
{
v___y_4204_ = v___f_4267_;
v___y_4205_ = v___y_4261_;
v___y_4206_ = v___y_4263_;
v___y_4207_ = v___f_4265_;
v___y_4208_ = v_id_4255_;
v___y_4209_ = v___y_4260_;
v___y_4210_ = v___y_4258_;
v___y_4211_ = v_danglingDot_4256_;
v___y_4212_ = v___y_4257_;
v___y_4213_ = v___y_4262_;
v___y_4214_ = v___y_4259_;
goto v___jp_4203_;
}
else
{
lean_object* v_lctx_4269_; lean_object* v_decls_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v_lctx_4269_ = lean_ctor_get(v___y_4260_, 2);
v_decls_4270_ = lean_ctor_get(v_lctx_4269_, 1);
v___x_4271_ = lean_box(0);
lean_inc_ref(v_decls_4270_);
v___x_4272_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4255_, v_danglingDot_4256_, v_decls_4270_, v___x_4271_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
if (lean_obj_tag(v_a_4273_) == 0)
{
lean_dec_ref(v_a_4273_);
lean_dec_ref(v___f_4267_);
lean_dec_ref(v___f_4265_);
lean_dec(v_id_4255_);
lean_dec_ref(v_ctx_4190_);
return v___x_4272_;
}
else
{
lean_dec_ref(v_a_4273_);
lean_dec_ref(v___x_4272_);
v___y_4204_ = v___f_4267_;
v___y_4205_ = v___y_4261_;
v___y_4206_ = v___y_4263_;
v___y_4207_ = v___f_4265_;
v___y_4208_ = v_id_4255_;
v___y_4209_ = v___y_4260_;
v___y_4210_ = v___y_4258_;
v___y_4211_ = v_danglingDot_4256_;
v___y_4212_ = v___y_4257_;
v___y_4213_ = v___y_4262_;
v___y_4214_ = v___y_4259_;
goto v___jp_4203_;
}
}
else
{
lean_dec_ref(v___f_4267_);
lean_dec_ref(v___f_4265_);
lean_dec(v_id_4255_);
lean_dec_ref(v_ctx_4190_);
return v___x_4272_;
}
}
}
v___jp_4274_:
{
if (lean_obj_tag(v_hoverInfo_4193_) == 1)
{
lean_object* v_delta_4283_; lean_object* v_id_4284_; uint8_t v_danglingDot_4285_; 
v_delta_4283_ = lean_ctor_get(v_hoverInfo_4193_, 0);
lean_inc(v_delta_4283_);
lean_dec_ref(v_hoverInfo_4193_);
v_id_4284_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4275_, v_delta_4283_);
v_danglingDot_4285_ = 0;
v_id_4255_ = v_id_4284_;
v_danglingDot_4256_ = v_danglingDot_4285_;
v___y_4257_ = v___y_4276_;
v___y_4258_ = v___y_4277_;
v___y_4259_ = v___y_4278_;
v___y_4260_ = v___y_4279_;
v___y_4261_ = v___y_4280_;
v___y_4262_ = v___y_4281_;
v___y_4263_ = v___y_4282_;
goto v___jp_4254_;
}
else
{
lean_dec(v_hoverInfo_4193_);
v_id_4255_ = v_id_4275_;
v_danglingDot_4256_ = v_danglingDot_4194_;
v___y_4257_ = v___y_4276_;
v___y_4258_ = v___y_4277_;
v___y_4259_ = v___y_4278_;
v___y_4260_ = v___y_4279_;
v___y_4261_ = v___y_4280_;
v___y_4262_ = v___y_4281_;
v___y_4263_ = v___y_4282_;
goto v___jp_4254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4291_, lean_object* v_stx_4292_, lean_object* v_id_4293_, lean_object* v_hoverInfo_4294_, lean_object* v_danglingDot_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
uint8_t v_danglingDot_boxed_4304_; lean_object* v_res_4305_; 
v_danglingDot_boxed_4304_ = lean_unbox(v_danglingDot_4295_);
v_res_4305_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4291_, v_stx_4292_, v_id_4293_, v_hoverInfo_4294_, v_danglingDot_boxed_4304_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_stx_4292_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4306_, lean_object* v___x_4307_, lean_object* v_alias_4308_, lean_object* v_as_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4306_, v___x_4307_, v_alias_4308_, v_as_4309_, v___y_4310_, v___y_4311_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4319_, lean_object* v___x_4320_, lean_object* v_alias_4321_, lean_object* v_as_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4319_, v___x_4320_, v_alias_4321_, v_as_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v_alias_4321_);
lean_dec_ref(v_a_4319_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_00_u03b2_4332_, lean_object* v_s_4333_, lean_object* v_f_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_4333_, v_f_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_00_u03b2_4344_, lean_object* v_s_4345_, lean_object* v_f_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_00_u03b2_4344_, v_s_4345_, v_f_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_id_4356_, uint8_t v_danglingDot_4357_, lean_object* v_a_4358_, lean_object* v___x_4359_, lean_object* v_as_4360_, lean_object* v_as_x27_4361_, lean_object* v_b_4362_, lean_object* v_a_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4356_, v_danglingDot_4357_, v_a_4358_, v___x_4359_, v_as_4360_, v_as_x27_4361_, v_b_4362_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_id_4373_, lean_object* v_danglingDot_4374_, lean_object* v_a_4375_, lean_object* v___x_4376_, lean_object* v_as_4377_, lean_object* v_as_x27_4378_, lean_object* v_b_4379_, lean_object* v_a_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
uint8_t v_danglingDot_boxed_4389_; lean_object* v_res_4390_; 
v_danglingDot_boxed_4389_ = lean_unbox(v_danglingDot_4374_);
v_res_4390_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4373_, v_danglingDot_boxed_4389_, v_a_4375_, v___x_4376_, v_as_4377_, v_as_x27_4378_, v_b_4379_, v_a_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v_as_4377_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_as_4391_, size_t v_sz_4392_, size_t v_i_4393_, lean_object* v_b_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4391_, v_sz_4392_, v_i_4393_, v_b_4394_, v___y_4395_, v___y_4396_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_as_4404_, lean_object* v_sz_4405_, lean_object* v_i_4406_, lean_object* v_b_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
size_t v_sz_boxed_4416_; size_t v_i_boxed_4417_; lean_object* v_res_4418_; 
v_sz_boxed_4416_ = lean_unbox_usize(v_sz_4405_);
lean_dec(v_sz_4405_);
v_i_boxed_4417_ = lean_unbox_usize(v_i_4406_);
lean_dec(v_i_4406_);
v_res_4418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4404_, v_sz_boxed_4416_, v_i_boxed_4417_, v_b_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec_ref(v_as_4404_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_00_u03b2_4419_, lean_object* v_f_4420_, lean_object* v_x_4421_, lean_object* v_x_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_4420_, v_x_4421_, v_x_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4432_, lean_object* v_f_4433_, lean_object* v_x_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_00_u03b2_4432_, v_f_4433_, v_x_4434_, v_x_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object* v_00_u03b2_4445_, lean_object* v_map_4446_, lean_object* v_f_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_4446_, v_f_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4457_, lean_object* v_map_4458_, lean_object* v_f_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(v_00_u03b2_4457_, v_map_4458_, v_f_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_object* v_00_u03b2_4469_, lean_object* v_f_4470_, lean_object* v_as_4471_, size_t v_i_4472_, size_t v_stop_4473_, lean_object* v_b_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_4470_, v_as_4471_, v_i_4472_, v_stop_4473_, v_b_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4484_, lean_object* v_f_4485_, lean_object* v_as_4486_, lean_object* v_i_4487_, lean_object* v_stop_4488_, lean_object* v_b_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
size_t v_i_boxed_4498_; size_t v_stop_boxed_4499_; lean_object* v_res_4500_; 
v_i_boxed_4498_ = lean_unbox_usize(v_i_4487_);
lean_dec(v_i_4487_);
v_stop_boxed_4499_ = lean_unbox_usize(v_stop_4488_);
lean_dec(v_stop_4488_);
v_res_4500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(v_00_u03b2_4484_, v_f_4485_, v_as_4486_, v_i_boxed_4498_, v_stop_boxed_4499_, v_b_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec_ref(v_as_4486_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(lean_object* v_a_4501_, lean_object* v___x_4502_, lean_object* v_id_4503_, uint8_t v_danglingDot_4504_, lean_object* v_as_4505_, lean_object* v_as_x27_4506_, lean_object* v_b_4507_, lean_object* v_a_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4501_, v___x_4502_, v_id_4503_, v_danglingDot_4504_, v_as_x27_4506_, v_b_4507_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___boxed(lean_object* v_a_4518_, lean_object* v___x_4519_, lean_object* v_id_4520_, lean_object* v_danglingDot_4521_, lean_object* v_as_4522_, lean_object* v_as_x27_4523_, lean_object* v_b_4524_, lean_object* v_a_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v_danglingDot_boxed_4534_; lean_object* v_res_4535_; 
v_danglingDot_boxed_4534_ = lean_unbox(v_danglingDot_4521_);
v_res_4535_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(v_a_4518_, v___x_4519_, v_id_4520_, v_danglingDot_boxed_4534_, v_as_4522_, v_as_x27_4523_, v_b_4524_, v_a_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v_as_4522_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4536_, lean_object* v_map_4537_, lean_object* v_f_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4537_, v_f_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4549_, lean_object* v_map_4550_, lean_object* v_f_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4549_, v_map_4550_, v_f_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object* v_map_4562_, lean_object* v_f_4563_, lean_object* v_init_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4563_, v_map_4562_, v_init_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_map_4574_, lean_object* v_f_4575_, lean_object* v_init_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4574_, v_f_4575_, v_init_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_4586_, lean_object* v_00_u03b2_4587_, lean_object* v_map_4588_, lean_object* v_f_4589_, lean_object* v_init_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4589_, v_map_4588_, v_init_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_4600_, lean_object* v_00_u03b2_4601_, lean_object* v_map_4602_, lean_object* v_f_4603_, lean_object* v_init_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(v_00_u03c3_4600_, v_00_u03b2_4601_, v_map_4602_, v_f_4603_, v_init_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(lean_object* v_id_4614_, uint8_t v_danglingDot_4615_, lean_object* v_as_4616_, size_t v_sz_4617_, size_t v_i_4618_, lean_object* v_b_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_4614_, v_danglingDot_4615_, v_as_4616_, v_sz_4617_, v_i_4618_, v_b_4619_, v___y_4620_, v___y_4621_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___boxed(lean_object* v_id_4629_, lean_object* v_danglingDot_4630_, lean_object* v_as_4631_, lean_object* v_sz_4632_, lean_object* v_i_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
uint8_t v_danglingDot_boxed_4643_; size_t v_sz_boxed_4644_; size_t v_i_boxed_4645_; lean_object* v_res_4646_; 
v_danglingDot_boxed_4643_ = lean_unbox(v_danglingDot_4630_);
v_sz_boxed_4644_ = lean_unbox_usize(v_sz_4632_);
lean_dec(v_sz_4632_);
v_i_boxed_4645_ = lean_unbox_usize(v_i_4633_);
lean_dec(v_i_4633_);
v_res_4646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(v_id_4629_, v_danglingDot_boxed_4643_, v_as_4631_, v_sz_boxed_4644_, v_i_boxed_4645_, v_b_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec_ref(v_as_4631_);
lean_dec(v_id_4629_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_map_4647_, lean_object* v_f_4648_, lean_object* v_init_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4648_, v_map_4647_, v_init_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_map_4660_, lean_object* v_f_4661_, lean_object* v_init_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(v_map_4660_, v_f_4661_, v_init_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03c3_4673_, lean_object* v_00_u03b2_4674_, lean_object* v_map_4675_, lean_object* v_f_4676_, lean_object* v_init_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v___x_4687_; 
v___x_4687_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4676_, v_map_4675_, v_init_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_00_u03c3_4688_, lean_object* v_00_u03b2_4689_, lean_object* v_map_4690_, lean_object* v_f_4691_, lean_object* v_init_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(v_00_u03c3_4688_, v_00_u03b2_4689_, v_map_4690_, v_f_4691_, v_init_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_object* v_00_u03c3_4703_, lean_object* v_00_u03b1_4704_, lean_object* v_00_u03b2_4705_, lean_object* v_f_4706_, lean_object* v_x_4707_, lean_object* v_x_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4706_, v_x_4707_, v_x_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03c3_4718_, lean_object* v_00_u03b1_4719_, lean_object* v_00_u03b2_4720_, lean_object* v_f_4721_, lean_object* v_x_4722_, lean_object* v_x_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(v_00_u03c3_4718_, v_00_u03b1_4719_, v_00_u03b2_4720_, v_f_4721_, v_x_4722_, v_x_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(lean_object* v_id_4733_, uint8_t v_danglingDot_4734_, lean_object* v_as_4735_, size_t v_sz_4736_, size_t v_i_4737_, lean_object* v_b_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_4733_, v_danglingDot_4734_, v_as_4735_, v_sz_4736_, v_i_4737_, v_b_4738_, v___y_4739_, v___y_4740_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___boxed(lean_object* v_id_4748_, lean_object* v_danglingDot_4749_, lean_object* v_as_4750_, lean_object* v_sz_4751_, lean_object* v_i_4752_, lean_object* v_b_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
uint8_t v_danglingDot_boxed_4762_; size_t v_sz_boxed_4763_; size_t v_i_boxed_4764_; lean_object* v_res_4765_; 
v_danglingDot_boxed_4762_ = lean_unbox(v_danglingDot_4749_);
v_sz_boxed_4763_ = lean_unbox_usize(v_sz_4751_);
lean_dec(v_sz_4751_);
v_i_boxed_4764_ = lean_unbox_usize(v_i_4752_);
lean_dec(v_i_4752_);
v_res_4765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(v_id_4748_, v_danglingDot_boxed_4762_, v_as_4750_, v_sz_boxed_4763_, v_i_boxed_4764_, v_b_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec_ref(v_as_4750_);
lean_dec(v_id_4748_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_object* v_00_u03c3_4766_, lean_object* v_00_u03b1_4767_, lean_object* v_00_u03b2_4768_, lean_object* v_f_4769_, lean_object* v_x_4770_, lean_object* v_x_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v___x_4781_; 
v___x_4781_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4769_, v_x_4770_, v_x_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___boxed(lean_object* v_00_u03c3_4782_, lean_object* v_00_u03b1_4783_, lean_object* v_00_u03b2_4784_, lean_object* v_f_4785_, lean_object* v_x_4786_, lean_object* v_x_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(v_00_u03c3_4782_, v_00_u03b1_4783_, v_00_u03b2_4784_, v_f_4785_, v_x_4786_, v_x_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_object* v_00_u03b1_4798_, lean_object* v_00_u03b2_4799_, lean_object* v_00_u03c3_4800_, lean_object* v_f_4801_, lean_object* v_as_4802_, size_t v_i_4803_, size_t v_stop_4804_, lean_object* v_b_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v___x_4814_; 
v___x_4814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_4801_, v_as_4802_, v_i_4803_, v_stop_4804_, v_b_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___boxed(lean_object* v_00_u03b1_4815_, lean_object* v_00_u03b2_4816_, lean_object* v_00_u03c3_4817_, lean_object* v_f_4818_, lean_object* v_as_4819_, lean_object* v_i_4820_, lean_object* v_stop_4821_, lean_object* v_b_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
size_t v_i_boxed_4831_; size_t v_stop_boxed_4832_; lean_object* v_res_4833_; 
v_i_boxed_4831_ = lean_unbox_usize(v_i_4820_);
lean_dec(v_i_4820_);
v_stop_boxed_4832_ = lean_unbox_usize(v_stop_4821_);
lean_dec(v_stop_4821_);
v_res_4833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(v_00_u03b1_4815_, v_00_u03b2_4816_, v_00_u03c3_4817_, v_f_4818_, v_as_4819_, v_i_boxed_4831_, v_stop_boxed_4832_, v_b_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec_ref(v_as_4819_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_object* v_00_u03c3_4834_, lean_object* v_00_u03b1_4835_, lean_object* v_00_u03b2_4836_, lean_object* v_f_4837_, lean_object* v_keys_4838_, lean_object* v_vals_4839_, lean_object* v_heq_4840_, lean_object* v_i_4841_, lean_object* v_acc_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_4837_, v_keys_4838_, v_vals_4839_, v_i_4841_, v_acc_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___boxed(lean_object** _args){
lean_object* v_00_u03c3_4852_ = _args[0];
lean_object* v_00_u03b1_4853_ = _args[1];
lean_object* v_00_u03b2_4854_ = _args[2];
lean_object* v_f_4855_ = _args[3];
lean_object* v_keys_4856_ = _args[4];
lean_object* v_vals_4857_ = _args[5];
lean_object* v_heq_4858_ = _args[6];
lean_object* v_i_4859_ = _args[7];
lean_object* v_acc_4860_ = _args[8];
lean_object* v___y_4861_ = _args[9];
lean_object* v___y_4862_ = _args[10];
lean_object* v___y_4863_ = _args[11];
lean_object* v___y_4864_ = _args[12];
lean_object* v___y_4865_ = _args[13];
lean_object* v___y_4866_ = _args[14];
lean_object* v___y_4867_ = _args[15];
lean_object* v___y_4868_ = _args[16];
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(v_00_u03c3_4852_, v_00_u03b1_4853_, v_00_u03b2_4854_, v_f_4855_, v_keys_4856_, v_vals_4857_, v_heq_4858_, v_i_4859_, v_acc_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec_ref(v_vals_4857_);
lean_dec_ref(v_keys_4856_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_object* v_00_u03b1_4870_, lean_object* v_00_u03b2_4871_, lean_object* v_00_u03c3_4872_, lean_object* v_f_4873_, lean_object* v_as_4874_, size_t v_i_4875_, size_t v_stop_4876_, lean_object* v_b_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_4873_, v_as_4874_, v_i_4875_, v_stop_4876_, v_b_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___boxed(lean_object** _args){
lean_object* v_00_u03b1_4888_ = _args[0];
lean_object* v_00_u03b2_4889_ = _args[1];
lean_object* v_00_u03c3_4890_ = _args[2];
lean_object* v_f_4891_ = _args[3];
lean_object* v_as_4892_ = _args[4];
lean_object* v_i_4893_ = _args[5];
lean_object* v_stop_4894_ = _args[6];
lean_object* v_b_4895_ = _args[7];
lean_object* v___y_4896_ = _args[8];
lean_object* v___y_4897_ = _args[9];
lean_object* v___y_4898_ = _args[10];
lean_object* v___y_4899_ = _args[11];
lean_object* v___y_4900_ = _args[12];
lean_object* v___y_4901_ = _args[13];
lean_object* v___y_4902_ = _args[14];
lean_object* v___y_4903_ = _args[15];
lean_object* v___y_4904_ = _args[16];
_start:
{
size_t v_i_boxed_4905_; size_t v_stop_boxed_4906_; lean_object* v_res_4907_; 
v_i_boxed_4905_ = lean_unbox_usize(v_i_4893_);
lean_dec(v_i_4893_);
v_stop_boxed_4906_ = lean_unbox_usize(v_stop_4894_);
lean_dec(v_stop_4894_);
v_res_4907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(v_00_u03b1_4888_, v_00_u03b2_4889_, v_00_u03c3_4890_, v_f_4891_, v_as_4892_, v_i_boxed_4905_, v_stop_boxed_4906_, v_b_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec_ref(v___y_4899_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec_ref(v_as_4892_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_object* v_00_u03c3_4908_, lean_object* v_00_u03b1_4909_, lean_object* v_00_u03b2_4910_, lean_object* v_f_4911_, lean_object* v_keys_4912_, lean_object* v_vals_4913_, lean_object* v_heq_4914_, lean_object* v_i_4915_, lean_object* v_acc_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_4911_, v_keys_4912_, v_vals_4913_, v_i_4915_, v_acc_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_00_u03c3_4927_ = _args[0];
lean_object* v_00_u03b1_4928_ = _args[1];
lean_object* v_00_u03b2_4929_ = _args[2];
lean_object* v_f_4930_ = _args[3];
lean_object* v_keys_4931_ = _args[4];
lean_object* v_vals_4932_ = _args[5];
lean_object* v_heq_4933_ = _args[6];
lean_object* v_i_4934_ = _args[7];
lean_object* v_acc_4935_ = _args[8];
lean_object* v___y_4936_ = _args[9];
lean_object* v___y_4937_ = _args[10];
lean_object* v___y_4938_ = _args[11];
lean_object* v___y_4939_ = _args[12];
lean_object* v___y_4940_ = _args[13];
lean_object* v___y_4941_ = _args[14];
lean_object* v___y_4942_ = _args[15];
lean_object* v___y_4943_ = _args[16];
lean_object* v___y_4944_ = _args[17];
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(v_00_u03c3_4927_, v_00_u03b1_4928_, v_00_u03b2_4929_, v_f_4930_, v_keys_4931_, v_vals_4932_, v_heq_4933_, v_i_4934_, v_acc_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v___y_4939_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_vals_4932_);
lean_dec_ref(v_keys_4931_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4946_, lean_object* v_pos_4947_, lean_object* v_completionInfoPos_4948_, lean_object* v_ctx_4949_, lean_object* v_lctx_4950_, lean_object* v_stx_4951_, lean_object* v_id_4952_, lean_object* v_hoverInfo_4953_, uint8_t v_danglingDot_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4957_ = lean_box(v_danglingDot_4954_);
lean_inc_ref(v_ctx_4949_);
v___x_4958_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_4958_, 0, v_ctx_4949_);
lean_closure_set(v___x_4958_, 1, v_stx_4951_);
lean_closure_set(v___x_4958_, 2, v_id_4952_);
lean_closure_set(v___x_4958_, 3, v_hoverInfo_4953_);
lean_closure_set(v___x_4958_, 4, v___x_4957_);
v___x_4959_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4946_, v_pos_4947_, v_completionInfoPos_4948_, v_ctx_4949_, v_lctx_4950_, v___x_4958_, v_a_4955_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_4960_, lean_object* v_pos_4961_, lean_object* v_completionInfoPos_4962_, lean_object* v_ctx_4963_, lean_object* v_lctx_4964_, lean_object* v_stx_4965_, lean_object* v_id_4966_, lean_object* v_hoverInfo_4967_, lean_object* v_danglingDot_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
uint8_t v_danglingDot_boxed_4971_; lean_object* v_res_4972_; 
v_danglingDot_boxed_4971_ = lean_unbox(v_danglingDot_4968_);
v_res_4972_ = l_Lean_Server_Completion_idCompletion(v_uri_4960_, v_pos_4961_, v_completionInfoPos_4962_, v_ctx_4963_, v_lctx_4964_, v_stx_4965_, v_id_4966_, v_hoverInfo_4967_, v_danglingDot_boxed_4971_, v_a_4969_);
lean_dec_ref(v_a_4969_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_4973_, lean_object* v___y_4974_){
_start:
{
uint8_t v___x_4976_; 
v___x_4976_ = l_Lean_Expr_hasMVar(v_e_4973_);
if (v___x_4976_ == 0)
{
lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4977_, 0, v_e_4973_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
return v___x_4978_;
}
else
{
lean_object* v___x_4979_; lean_object* v_mctx_4980_; lean_object* v___x_4981_; lean_object* v_fst_4982_; lean_object* v_snd_4983_; lean_object* v___x_4984_; lean_object* v_cache_4985_; lean_object* v_zetaDeltaFVarIds_4986_; lean_object* v_postponed_4987_; lean_object* v_diag_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4998_; 
v___x_4979_ = lean_st_ref_get(v___y_4974_);
v_mctx_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc_ref(v_mctx_4980_);
lean_dec(v___x_4979_);
v___x_4981_ = l_Lean_instantiateMVarsCore(v_mctx_4980_, v_e_4973_);
v_fst_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_fst_4982_);
v_snd_4983_ = lean_ctor_get(v___x_4981_, 1);
lean_inc(v_snd_4983_);
lean_dec_ref(v___x_4981_);
v___x_4984_ = lean_st_ref_take(v___y_4974_);
v_cache_4985_ = lean_ctor_get(v___x_4984_, 1);
v_zetaDeltaFVarIds_4986_ = lean_ctor_get(v___x_4984_, 2);
v_postponed_4987_ = lean_ctor_get(v___x_4984_, 3);
v_diag_4988_ = lean_ctor_get(v___x_4984_, 4);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_4998_ == 0)
{
lean_object* v_unused_4999_; 
v_unused_4999_ = lean_ctor_get(v___x_4984_, 0);
lean_dec(v_unused_4999_);
v___x_4990_ = v___x_4984_;
v_isShared_4991_ = v_isSharedCheck_4998_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_diag_4988_);
lean_inc(v_postponed_4987_);
lean_inc(v_zetaDeltaFVarIds_4986_);
lean_inc(v_cache_4985_);
lean_dec(v___x_4984_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4998_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_snd_4983_);
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_snd_4983_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_cache_4985_);
lean_ctor_set(v_reuseFailAlloc_4997_, 2, v_zetaDeltaFVarIds_4986_);
lean_ctor_set(v_reuseFailAlloc_4997_, 3, v_postponed_4987_);
lean_ctor_set(v_reuseFailAlloc_4997_, 4, v_diag_4988_);
v___x_4993_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = lean_st_ref_set(v___y_4974_, v___x_4993_);
v___x_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4995_, 0, v_fst_4982_);
v___x_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
return v___x_4996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_5000_, v___y_5001_);
lean_dec(v___y_5001_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_5004_, v___y_5009_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_5024_, lean_object* v_declName_5025_, lean_object* v_decl_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_unnormedTypeName_5035_; uint8_t v___x_5036_; 
v_unnormedTypeName_5035_ = l_Lean_Name_getPrefix(v_declName_5025_);
v___x_5036_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_5035_, v_a_5024_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref(v_decl_5026_);
lean_dec(v_declName_5025_);
v___x_5037_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
return v___x_5038_;
}
else
{
lean_object* v___x_5039_; lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5105_; 
v___x_5039_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5025_, v___y_5033_);
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5105_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5105_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
if (lean_obj_tag(v_a_5040_) == 1)
{
lean_object* v_val_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5100_; 
lean_del_object(v___x_5042_);
v_val_5044_ = lean_ctor_get(v_a_5040_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v_a_5040_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5046_ = v_a_5040_;
v_isShared_5047_ = v_isSharedCheck_5100_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_val_5044_);
lean_dec(v_a_5040_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5100_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v_info_5048_; lean_object* v_kind_5049_; lean_object* v_tags_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v_info_5048_ = lean_ctor_get(v_decl_5026_, 0);
lean_inc_ref(v_info_5048_);
v_kind_5049_ = lean_ctor_get(v_decl_5026_, 1);
lean_inc_ref(v_kind_5049_);
v_tags_5050_ = lean_ctor_get(v_decl_5026_, 2);
lean_inc_ref(v_tags_5050_);
lean_dec_ref(v_decl_5026_);
v___x_5051_ = l_Lean_Name_getPrefix(v_val_5044_);
lean_dec(v_val_5044_);
v___x_5052_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_5051_, v_info_5048_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v_a_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5091_; 
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5055_ = v___x_5052_;
v_isShared_5056_ = v_isSharedCheck_5091_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_a_5053_);
lean_dec(v___x_5052_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5091_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
uint8_t v___x_5057_; 
v___x_5057_ = lean_unbox(v_a_5053_);
lean_dec(v_a_5053_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; lean_object* v___x_5060_; 
lean_dec_ref(v_tags_5050_);
lean_dec_ref(v_kind_5049_);
lean_dec_ref(v_info_5048_);
lean_del_object(v___x_5046_);
v___x_5058_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 0, v___x_5058_);
v___x_5060_ = v___x_5055_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
else
{
lean_object* v___x_5062_; 
lean_del_object(v___x_5055_);
lean_inc(v___y_5033_);
lean_inc_ref(v___y_5032_);
lean_inc(v___y_5031_);
lean_inc_ref(v___y_5030_);
v___x_5062_ = lean_apply_5(v_kind_5049_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, lean_box(0));
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref(v___x_5062_);
lean_inc(v___y_5033_);
lean_inc_ref(v___y_5032_);
lean_inc(v___y_5031_);
lean_inc_ref(v___y_5030_);
v___x_5064_ = lean_apply_5(v_tags_5050_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, lean_box(0));
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5071_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref(v___x_5064_);
v___x_5066_ = l_Lean_ConstantInfo_name(v_info_5048_);
lean_dec_ref(v_info_5048_);
v___x_5067_ = l_Lean_Name_getString_x21(v___x_5066_);
v___x_5068_ = lean_box(0);
v___x_5069_ = l_Lean_Name_str___override(v___x_5068_, v___x_5067_);
if (v_isShared_5047_ == 0)
{
lean_ctor_set_tag(v___x_5046_, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5066_);
v___x_5071_ = v___x_5046_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5066_);
v___x_5071_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
uint8_t v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = lean_unbox(v_a_5063_);
lean_dec(v_a_5063_);
v___x_5073_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5069_, v___x_5071_, v___x_5072_, v_a_5065_, v___y_5027_, v___y_5028_);
return v___x_5073_;
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_dec(v_a_5063_);
lean_dec_ref(v_info_5048_);
lean_del_object(v___x_5046_);
v_a_5075_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5064_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5064_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
else
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_dec_ref(v_tags_5050_);
lean_dec_ref(v_info_5048_);
lean_del_object(v___x_5046_);
v_a_5083_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5062_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5062_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
}
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_dec_ref(v_tags_5050_);
lean_dec_ref(v_kind_5049_);
lean_dec_ref(v_info_5048_);
lean_del_object(v___x_5046_);
v_a_5092_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5052_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5052_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5103_; 
lean_dec(v_a_5040_);
lean_dec_ref(v_decl_5026_);
v___x_5101_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5101_);
v___x_5103_ = v___x_5042_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5101_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_5106_, lean_object* v_declName_5107_, lean_object* v_decl_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5106_, v_declName_5107_, v_decl_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v_a_5131_; lean_object* v___y_5135_; uint8_t v___y_5136_; lean_object* v___y_5146_; lean_object* v_a_5147_; lean_object* v___x_5150_; 
lean_inc(v___y_5125_);
lean_inc_ref(v___y_5124_);
lean_inc(v___y_5123_);
lean_inc_ref(v___y_5122_);
v___x_5150_ = lean_infer_type(v_expr_5118_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; lean_object* v___x_5152_; lean_object* v_a_5153_; lean_object* v_a_5154_; lean_object* v___x_5155_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_a_5151_);
lean_dec_ref(v___x_5150_);
v___x_5152_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_5151_, v___y_5123_);
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_a_5153_);
lean_dec_ref(v___x_5152_);
v_a_5154_ = lean_ctor_get(v_a_5153_, 0);
lean_inc(v_a_5154_);
lean_dec(v_a_5153_);
v___x_5155_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_5154_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
lean_dec_ref(v___x_5155_);
v_a_5131_ = v_a_5156_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
v_a_5157_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5155_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5155_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
lean_inc(v_a_5157_);
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
v___y_5146_ = v___x_5162_;
v_a_5147_ = v_a_5157_;
goto v___jp_5145_;
}
}
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
v_a_5165_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5150_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5150_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
lean_inc(v_a_5165_);
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
v___y_5146_ = v___x_5170_;
v_a_5147_ = v_a_5165_;
goto v___jp_5145_;
}
}
}
v___jp_5127_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5128_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
return v___x_5129_;
}
v___jp_5130_:
{
if (lean_obj_tag(v_a_5131_) == 0)
{
lean_object* v___f_5132_; lean_object* v___x_5133_; 
v___f_5132_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5132_, 0, v_a_5131_);
v___x_5133_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5132_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
return v___x_5133_;
}
else
{
goto v___jp_5127_;
}
}
v___jp_5134_:
{
if (v___y_5136_ == 0)
{
lean_dec_ref(v___y_5135_);
goto v___jp_5127_;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_a_5137_ = lean_ctor_get(v___y_5135_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___y_5135_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___y_5135_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___y_5135_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
v___jp_5145_:
{
uint8_t v___x_5148_; 
v___x_5148_ = l_Lean_Exception_isInterrupt(v_a_5147_);
if (v___x_5148_ == 0)
{
uint8_t v___x_5149_; 
v___x_5149_ = l_Lean_Exception_isRuntime(v_a_5147_);
v___y_5135_ = v___y_5146_;
v___y_5136_ = v___x_5149_;
goto v___jp_5134_;
}
else
{
lean_dec_ref(v_a_5147_);
v___y_5135_ = v___y_5146_;
v___y_5136_ = v___x_5148_;
goto v___jp_5134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5183_, lean_object* v_pos_5184_, lean_object* v_completionInfoPos_5185_, lean_object* v_ctx_5186_, lean_object* v_info_5187_, lean_object* v_a_5188_){
_start:
{
lean_object* v_lctx_5190_; lean_object* v_expr_5191_; lean_object* v___f_5192_; lean_object* v___x_5193_; 
v_lctx_5190_ = lean_ctor_get(v_info_5187_, 1);
lean_inc_ref(v_lctx_5190_);
v_expr_5191_ = lean_ctor_get(v_info_5187_, 3);
lean_inc_ref(v_expr_5191_);
lean_dec_ref(v_info_5187_);
v___f_5192_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5192_, 0, v_expr_5191_);
v___x_5193_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5183_, v_pos_5184_, v_completionInfoPos_5185_, v_ctx_5186_, v_lctx_5190_, v___f_5192_, v_a_5188_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5194_, lean_object* v_pos_5195_, lean_object* v_completionInfoPos_5196_, lean_object* v_ctx_5197_, lean_object* v_info_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Lean_Server_Completion_dotCompletion(v_uri_5194_, v_pos_5195_, v_completionInfoPos_5196_, v_ctx_5197_, v_info_5198_, v_a_5199_);
lean_dec_ref(v_a_5199_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5202_, uint8_t v___x_5203_, lean_object* v_id_5204_, lean_object* v_declName_5205_, lean_object* v_decl_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5218_; uint8_t v___x_5219_; 
v___x_5218_ = l_Lean_Name_getPrefix(v_declName_5205_);
lean_inc(v___x_5202_);
v___x_5219_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5218_, v___x_5202_);
if (v___x_5219_ == 0)
{
lean_dec_ref(v_decl_5206_);
lean_dec(v_declName_5205_);
lean_dec(v___x_5202_);
goto v___jp_5215_;
}
else
{
if (v___x_5203_ == 0)
{
lean_object* v___x_5220_; lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5317_; 
v___x_5220_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5205_, v___y_5213_);
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5223_ = v___x_5220_;
v_isShared_5224_ = v_isSharedCheck_5317_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5220_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5317_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
if (lean_obj_tag(v_a_5221_) == 1)
{
lean_object* v_val_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5312_; 
lean_del_object(v___x_5223_);
v_val_5225_ = lean_ctor_get(v_a_5221_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v_a_5221_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5227_ = v_a_5221_;
v_isShared_5228_ = v_isSharedCheck_5312_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_val_5225_);
lean_dec(v_a_5221_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5312_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v_info_5229_; lean_object* v_kind_5230_; lean_object* v_tags_5231_; lean_object* v___x_5232_; 
v_info_5229_ = lean_ctor_get(v_decl_5206_, 0);
lean_inc_ref(v_info_5229_);
v_kind_5230_ = lean_ctor_get(v_decl_5206_, 1);
lean_inc_ref(v_kind_5230_);
v_tags_5231_ = lean_ctor_get(v_decl_5206_, 2);
lean_inc_ref(v_tags_5231_);
lean_dec_ref(v_decl_5206_);
v___x_5232_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5202_, v_info_5229_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5303_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5235_ = v___x_5232_;
v_isShared_5236_ = v_isSharedCheck_5303_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5232_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5303_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
uint8_t v___x_5237_; 
v___x_5237_ = lean_unbox(v_a_5233_);
lean_dec(v_a_5233_);
if (v___x_5237_ == 0)
{
lean_object* v___x_5238_; lean_object* v___x_5240_; 
lean_dec_ref(v_tags_5231_);
lean_dec_ref(v_kind_5230_);
lean_dec_ref(v_info_5229_);
lean_del_object(v___x_5227_);
lean_dec(v_val_5225_);
v___x_5238_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5236_ == 0)
{
lean_ctor_set(v___x_5235_, 0, v___x_5238_);
v___x_5240_ = v___x_5235_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
else
{
lean_object* v___x_5242_; 
lean_del_object(v___x_5235_);
lean_inc(v___y_5213_);
lean_inc_ref(v___y_5212_);
lean_inc(v___y_5211_);
lean_inc_ref(v___y_5210_);
v___x_5242_ = lean_apply_5(v_kind_5230_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, lean_box(0));
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5244_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc(v_a_5243_);
lean_dec_ref(v___x_5242_);
lean_inc(v___y_5213_);
lean_inc_ref(v___y_5212_);
lean_inc(v___y_5211_);
lean_inc_ref(v___y_5210_);
v___x_5244_ = lean_apply_5(v_tags_5231_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, lean_box(0));
if (lean_obj_tag(v___x_5244_) == 0)
{
lean_object* v_a_5245_; uint8_t v___x_5246_; 
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
lean_inc(v_a_5245_);
lean_dec_ref(v___x_5244_);
v___x_5246_ = l_Lean_Name_isAnonymous(v_id_5204_);
if (v___x_5246_ == 0)
{
lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5268_; 
lean_del_object(v___x_5227_);
v___x_5247_ = l_Lean_Name_getPrefix(v_val_5225_);
v___x_5248_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5247_, v_id_5204_, v___x_5246_, v_val_5225_, v___y_5213_);
lean_dec(v___x_5247_);
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5251_ = v___x_5248_;
v_isShared_5252_ = v_isSharedCheck_5268_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5248_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5268_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
if (lean_obj_tag(v_a_5249_) == 1)
{
lean_object* v_val_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5263_; 
lean_del_object(v___x_5251_);
v_val_5253_ = lean_ctor_get(v_a_5249_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v_a_5249_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5255_ = v_a_5249_;
v_isShared_5256_ = v_isSharedCheck_5263_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_val_5253_);
lean_dec(v_a_5249_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5263_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5257_; lean_object* v___x_5259_; 
v___x_5257_ = l_Lean_ConstantInfo_name(v_info_5229_);
lean_dec_ref(v_info_5229_);
if (v_isShared_5256_ == 0)
{
lean_ctor_set_tag(v___x_5255_, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5257_);
v___x_5259_ = v___x_5255_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5257_);
v___x_5259_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
uint8_t v___x_5260_; lean_object* v___x_5261_; 
v___x_5260_ = lean_unbox(v_a_5243_);
lean_dec(v_a_5243_);
v___x_5261_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5253_, v___x_5259_, v___x_5260_, v_a_5245_, v___y_5207_, v___y_5208_);
return v___x_5261_;
}
}
}
else
{
lean_object* v___x_5264_; lean_object* v___x_5266_; 
lean_dec(v_a_5249_);
lean_dec(v_a_5245_);
lean_dec(v_a_5243_);
lean_dec_ref(v_info_5229_);
v___x_5264_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 0, v___x_5264_);
v___x_5266_ = v___x_5251_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5264_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5274_; 
lean_dec(v_val_5225_);
v___x_5269_ = l_Lean_ConstantInfo_name(v_info_5229_);
lean_dec_ref(v_info_5229_);
v___x_5270_ = l_Lean_Name_getString_x21(v___x_5269_);
v___x_5271_ = lean_box(0);
v___x_5272_ = l_Lean_Name_str___override(v___x_5271_, v___x_5270_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set_tag(v___x_5227_, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5269_);
v___x_5274_ = v___x_5227_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5269_);
v___x_5274_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
uint8_t v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5284_; 
v___x_5275_ = lean_unbox(v_a_5243_);
lean_dec(v_a_5243_);
v___x_5276_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5272_, v___x_5274_, v___x_5275_, v_a_5245_, v___y_5207_, v___y_5208_);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5284_ == 0)
{
lean_object* v_unused_5285_; 
v_unused_5285_ = lean_ctor_get(v___x_5276_, 0);
lean_dec(v_unused_5285_);
v___x_5278_ = v___x_5276_;
v_isShared_5279_ = v_isSharedCheck_5284_;
goto v_resetjp_5277_;
}
else
{
lean_dec(v___x_5276_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5284_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5280_; lean_object* v___x_5282_; 
v___x_5280_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 0, v___x_5280_);
v___x_5282_ = v___x_5278_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
lean_dec(v_a_5243_);
lean_dec_ref(v_info_5229_);
lean_del_object(v___x_5227_);
lean_dec(v_val_5225_);
v_a_5287_ = lean_ctor_get(v___x_5244_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5244_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5244_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5244_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
lean_dec_ref(v_tags_5231_);
lean_dec_ref(v_info_5229_);
lean_del_object(v___x_5227_);
lean_dec(v_val_5225_);
v_a_5295_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5242_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5242_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec_ref(v_tags_5231_);
lean_dec_ref(v_kind_5230_);
lean_dec_ref(v_info_5229_);
lean_del_object(v___x_5227_);
lean_dec(v_val_5225_);
v_a_5304_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5232_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5232_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
}
}
else
{
lean_object* v___x_5313_; lean_object* v___x_5315_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_decl_5206_);
lean_dec(v___x_5202_);
v___x_5313_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 0, v___x_5313_);
v___x_5315_ = v___x_5223_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
else
{
lean_dec_ref(v_decl_5206_);
lean_dec(v_declName_5205_);
lean_dec(v___x_5202_);
goto v___jp_5215_;
}
}
v___jp_5215_:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5216_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5216_);
return v___x_5217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5318_, lean_object* v___x_5319_, lean_object* v_id_5320_, lean_object* v_declName_5321_, lean_object* v_decl_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
uint8_t v___x_21334__boxed_5331_; lean_object* v_res_5332_; 
v___x_21334__boxed_5331_ = lean_unbox(v___x_5319_);
v_res_5332_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5318_, v___x_21334__boxed_5331_, v_id_5320_, v_declName_5321_, v_decl_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v_id_5320_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5333_, lean_object* v_id_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5333_) == 1)
{
lean_object* v_val_5343_; lean_object* v___x_5344_; 
v_val_5343_ = lean_ctor_get(v_expectedType_x3f_5333_, 0);
lean_inc(v_val_5343_);
lean_dec_ref(v_expectedType_x3f_5333_);
v___x_5344_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5343_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5360_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5347_ = v___x_5344_;
v_isShared_5348_ = v_isSharedCheck_5360_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5344_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5360_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; uint8_t v___x_5351_; 
v___x_5349_ = lean_array_get_size(v_a_5345_);
v___x_5350_ = lean_unsigned_to_nat(0u);
v___x_5351_ = lean_nat_dec_eq(v___x_5349_, v___x_5350_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___f_5354_; lean_object* v___x_5355_; 
lean_del_object(v___x_5347_);
v___x_5352_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5345_);
lean_dec(v_a_5345_);
v___x_5353_ = lean_box(v___x_5351_);
v___f_5354_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 13, 3);
lean_closure_set(v___f_5354_, 0, v___x_5352_);
lean_closure_set(v___f_5354_, 1, v___x_5353_);
lean_closure_set(v___f_5354_, 2, v_id_5334_);
v___x_5355_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5354_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
return v___x_5355_;
}
else
{
lean_object* v___x_5356_; lean_object* v___x_5358_; 
lean_dec(v_a_5345_);
lean_dec(v_id_5334_);
v___x_5356_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 0, v___x_5356_);
v___x_5358_ = v___x_5347_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec(v_id_5334_);
v_a_5361_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5344_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5344_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5366_; 
if (v_isShared_5364_ == 0)
{
v___x_5366_ = v___x_5363_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5370_; 
lean_dec(v_id_5334_);
lean_dec(v_expectedType_x3f_5333_);
v___x_5369_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5369_);
return v___x_5370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5371_, lean_object* v_id_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5371_, v_id_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec_ref(v___y_5375_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5382_, lean_object* v_pos_5383_, lean_object* v_completionInfoPos_5384_, lean_object* v_ctx_5385_, lean_object* v_lctx_5386_, lean_object* v_id_5387_, lean_object* v_expectedType_x3f_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v___y_5391_; lean_object* v___x_5392_; 
v___y_5391_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5391_, 0, v_expectedType_x3f_5388_);
lean_closure_set(v___y_5391_, 1, v_id_5387_);
v___x_5392_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5382_, v_pos_5383_, v_completionInfoPos_5384_, v_ctx_5385_, v_lctx_5386_, v___y_5391_, v_a_5389_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5393_, lean_object* v_pos_5394_, lean_object* v_completionInfoPos_5395_, lean_object* v_ctx_5396_, lean_object* v_lctx_5397_, lean_object* v_id_5398_, lean_object* v_expectedType_x3f_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5393_, v_pos_5394_, v_completionInfoPos_5395_, v_ctx_5396_, v_lctx_5397_, v_id_5398_, v_expectedType_x3f_5399_, v_a_5400_);
lean_dec_ref(v_a_5400_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5409_, lean_object* v_as_5410_, size_t v_sz_5411_, size_t v_i_5412_, lean_object* v_b_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v_a_5418_; uint8_t v___x_5422_; 
v___x_5422_ = lean_usize_dec_lt(v_i_5412_, v_sz_5411_);
if (v___x_5422_ == 0)
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5423_, 0, v_b_5413_);
v___x_5424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5424_, 0, v___x_5423_);
return v___x_5424_;
}
else
{
lean_object* v___x_5425_; lean_object* v_a_5426_; 
v___x_5425_ = lean_box(0);
v_a_5426_ = lean_array_uget_borrowed(v_as_5410_, v_i_5412_);
if (lean_obj_tag(v_a_5426_) == 1)
{
lean_object* v_str_5427_; uint8_t v___x_5428_; 
v_str_5427_ = lean_ctor_get(v_a_5426_, 1);
v___x_5428_ = l_String_charactersIn(v___y_5409_, v_str_5427_);
if (v___x_5428_ == 0)
{
v_a_5418_ = v___x_5425_;
goto v___jp_5417_;
}
else
{
lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5430_ = lean_box(0);
v___x_5431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5427_);
v___x_5432_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5432_, 0, v_str_5427_);
lean_ctor_set(v___x_5432_, 1, v___x_5429_);
lean_ctor_set(v___x_5432_, 2, v___x_5430_);
lean_ctor_set(v___x_5432_, 3, v___x_5431_);
lean_ctor_set(v___x_5432_, 4, v___x_5430_);
lean_ctor_set(v___x_5432_, 5, v___x_5430_);
lean_ctor_set(v___x_5432_, 6, v___x_5430_);
lean_ctor_set(v___x_5432_, 7, v___x_5430_);
v___x_5433_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5432_, v___x_5430_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_a_5434_);
if (lean_obj_tag(v_a_5434_) == 0)
{
lean_dec_ref(v_a_5434_);
return v___x_5433_;
}
else
{
lean_dec_ref(v_a_5434_);
lean_dec_ref(v___x_5433_);
v_a_5418_ = v___x_5425_;
goto v___jp_5417_;
}
}
else
{
return v___x_5433_;
}
}
}
else
{
v_a_5418_ = v___x_5425_;
goto v___jp_5417_;
}
}
v___jp_5417_:
{
size_t v___x_5419_; size_t v___x_5420_; 
v___x_5419_ = ((size_t)1ULL);
v___x_5420_ = lean_usize_add(v_i_5412_, v___x_5419_);
v_i_5412_ = v___x_5420_;
v_b_5413_ = v_a_5418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5435_, lean_object* v_as_5436_, lean_object* v_sz_5437_, lean_object* v_i_5438_, lean_object* v_b_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
size_t v_sz_boxed_5443_; size_t v_i_boxed_5444_; lean_object* v_res_5445_; 
v_sz_boxed_5443_ = lean_unbox_usize(v_sz_5437_);
lean_dec(v_sz_5437_);
v_i_boxed_5444_ = lean_unbox_usize(v_i_5438_);
lean_dec(v_i_5438_);
v_res_5445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5435_, v_as_5436_, v_sz_boxed_5443_, v_i_boxed_5444_, v_b_5439_, v___y_5440_, v___y_5441_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec_ref(v_as_5436_);
lean_dec_ref(v___y_5435_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v___x_5456_; lean_object* v_env_5457_; uint8_t v___x_5458_; lean_object* v_fieldNames_5459_; lean_object* v___x_5460_; size_t v_sz_5461_; size_t v___x_5462_; lean_object* v___x_5463_; 
v___x_5456_ = lean_st_ref_get(v___y_5454_);
v_env_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc_ref(v_env_5457_);
lean_dec(v___x_5456_);
v___x_5458_ = 0;
v_fieldNames_5459_ = l_Lean_getStructureFieldsFlattened(v_env_5457_, v_structName_5446_, v___x_5458_);
v___x_5460_ = lean_box(0);
v_sz_5461_ = lean_array_size(v_fieldNames_5459_);
v___x_5462_ = ((size_t)0ULL);
v___x_5463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5447_, v_fieldNames_5459_, v_sz_5461_, v___x_5462_, v___x_5460_, v___y_5448_, v___y_5449_);
lean_dec_ref(v_fieldNames_5459_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
if (lean_obj_tag(v_a_5464_) == 0)
{
lean_dec_ref(v_a_5464_);
return v___x_5463_;
}
else
{
lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5472_; 
lean_dec_ref(v_a_5464_);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5472_ == 0)
{
lean_object* v_unused_5473_; 
v_unused_5473_ = lean_ctor_get(v___x_5463_, 0);
lean_dec(v_unused_5473_);
v___x_5466_ = v___x_5463_;
v_isShared_5467_ = v_isSharedCheck_5472_;
goto v_resetjp_5465_;
}
else
{
lean_dec(v___x_5463_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5472_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5468_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 0, v___x_5468_);
v___x_5470_ = v___x_5466_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
else
{
return v___x_5463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v_res_5484_; 
v_res_5484_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec_ref(v___y_5475_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5486_, lean_object* v_pos_5487_, lean_object* v_completionInfoPos_5488_, lean_object* v_ctx_5489_, lean_object* v_lctx_5490_, lean_object* v_id_5491_, lean_object* v_structName_5492_, lean_object* v_a_5493_){
_start:
{
lean_object* v___y_5496_; 
if (lean_obj_tag(v_id_5491_) == 0)
{
lean_object* v___x_5499_; 
v___x_5499_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5496_ = v___x_5499_;
goto v___jp_5495_;
}
else
{
lean_object* v_val_5500_; uint8_t v___x_5501_; lean_object* v___x_5502_; 
v_val_5500_ = lean_ctor_get(v_id_5491_, 0);
lean_inc(v_val_5500_);
lean_dec_ref(v_id_5491_);
v___x_5501_ = 1;
v___x_5502_ = l_Lean_Name_toString(v_val_5500_, v___x_5501_);
v___y_5496_ = v___x_5502_;
goto v___jp_5495_;
}
v___jp_5495_:
{
lean_object* v___f_5497_; lean_object* v___x_5498_; 
v___f_5497_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5497_, 0, v_structName_5492_);
lean_closure_set(v___f_5497_, 1, v___y_5496_);
v___x_5498_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5486_, v_pos_5487_, v_completionInfoPos_5488_, v_ctx_5489_, v_lctx_5490_, v___f_5497_, v_a_5493_);
return v___x_5498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5503_, lean_object* v_pos_5504_, lean_object* v_completionInfoPos_5505_, lean_object* v_ctx_5506_, lean_object* v_lctx_5507_, lean_object* v_id_5508_, lean_object* v_structName_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_){
_start:
{
lean_object* v_res_5512_; 
v_res_5512_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5503_, v_pos_5504_, v_completionInfoPos_5505_, v_ctx_5506_, v_lctx_5507_, v_id_5508_, v_structName_5509_, v_a_5510_);
lean_dec_ref(v_a_5510_);
return v_res_5512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5513_, lean_object* v_as_5514_, size_t v_sz_5515_, size_t v_i_5516_, lean_object* v_b_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v___x_5526_; 
v___x_5526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5513_, v_as_5514_, v_sz_5515_, v_i_5516_, v_b_5517_, v___y_5518_, v___y_5519_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5527_, lean_object* v_as_5528_, lean_object* v_sz_5529_, lean_object* v_i_5530_, lean_object* v_b_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
size_t v_sz_boxed_5540_; size_t v_i_boxed_5541_; lean_object* v_res_5542_; 
v_sz_boxed_5540_ = lean_unbox_usize(v_sz_5529_);
lean_dec(v_sz_5529_);
v_i_boxed_5541_ = lean_unbox_usize(v_i_5530_);
lean_dec(v_i_5530_);
v_res_5542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5527_, v_as_5528_, v_sz_boxed_5540_, v_i_boxed_5541_, v_b_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec_ref(v___y_5534_);
lean_dec(v___y_5533_);
lean_dec_ref(v___y_5532_);
lean_dec_ref(v_as_5528_);
lean_dec_ref(v___y_5527_);
return v_res_5542_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0(void){
_start:
{
uint32_t v___x_5543_; lean_object* v___x_5544_; 
v___x_5543_ = 32;
v___x_5544_ = l_Char_utf8Size(v___x_5543_);
return v___x_5544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5545_, lean_object* v_caps_5546_, lean_object* v_mkItem_5547_, lean_object* v_ctx_5548_, lean_object* v_stx_5549_, uint8_t v_snd_5550_, lean_object* v_x_5551_, lean_object* v_____s_5552_){
_start:
{
lean_object* v_fst_5553_; lean_object* v_snd_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5607_; 
v_fst_5553_ = lean_ctor_get(v_x_5551_, 0);
v_snd_5554_ = lean_ctor_get(v_x_5551_, 1);
v_isSharedCheck_5607_ = !lean_is_exclusive(v_x_5551_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5556_ = v_x_5551_;
v_isShared_5557_ = v_isSharedCheck_5607_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_snd_5554_);
lean_inc(v_fst_5553_);
lean_dec(v_x_5551_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5607_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___y_5559_; uint8_t v___x_5563_; lean_object* v___x_5564_; lean_object* v___y_5566_; lean_object* v___y_5567_; uint8_t v___x_5596_; 
v___x_5563_ = 1;
lean_inc(v_fst_5553_);
v___x_5564_ = l_Lean_Name_toString(v_fst_5553_, v___x_5563_);
v___x_5596_ = l_String_charactersIn(v_fst_5545_, v___x_5564_);
if (v___x_5596_ == 0)
{
lean_object* v___x_5599_; 
lean_dec_ref(v___x_5564_);
lean_del_object(v___x_5556_);
lean_dec(v_snd_5554_);
lean_dec(v_fst_5553_);
lean_dec_ref(v_ctx_5548_);
lean_dec_ref(v_mkItem_5547_);
v___x_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5599_, 0, v_____s_5552_);
return v___x_5599_;
}
else
{
lean_object* v_textDocument_x3f_5600_; 
v_textDocument_x3f_5600_ = lean_ctor_get(v_caps_5546_, 0);
if (lean_obj_tag(v_textDocument_x3f_5600_) == 0)
{
goto v___jp_5597_;
}
else
{
lean_object* v_val_5601_; lean_object* v_completion_x3f_5602_; 
v_val_5601_ = lean_ctor_get(v_textDocument_x3f_5600_, 0);
v_completion_x3f_5602_ = lean_ctor_get(v_val_5601_, 0);
if (lean_obj_tag(v_completion_x3f_5602_) == 0)
{
goto v___jp_5597_;
}
else
{
lean_object* v_val_5603_; 
v_val_5603_ = lean_ctor_get(v_completion_x3f_5602_, 0);
if (lean_obj_tag(v_val_5603_) == 0)
{
goto v___jp_5597_;
}
else
{
lean_object* v_val_5604_; 
v_val_5604_ = lean_ctor_get(v_val_5603_, 0);
if (lean_obj_tag(v_val_5604_) == 0)
{
goto v___jp_5597_;
}
else
{
lean_object* v_val_5605_; uint8_t v___x_5606_; 
v_val_5605_ = lean_ctor_get(v_val_5604_, 0);
v___x_5606_ = lean_unbox(v_val_5605_);
if (v___x_5606_ == 0)
{
goto v___jp_5597_;
}
else
{
goto v___jp_5585_;
}
}
}
}
}
}
v___jp_5558_:
{
lean_object* v___x_5560_; lean_object* v_items_5561_; lean_object* v___x_5562_; 
v___x_5560_ = lean_apply_3(v_mkItem_5547_, v_fst_5553_, v_snd_5554_, v___y_5559_);
v_items_5561_ = lean_array_push(v_____s_5552_, v___x_5560_);
v___x_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5562_, 0, v_items_5561_);
return v___x_5562_;
}
v___jp_5565_:
{
lean_object* v_toCommandContextInfo_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5582_; 
v_toCommandContextInfo_5568_ = lean_ctor_get(v_ctx_5548_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v_ctx_5548_);
if (v_isSharedCheck_5582_ == 0)
{
lean_object* v_unused_5583_; lean_object* v_unused_5584_; 
v_unused_5583_ = lean_ctor_get(v_ctx_5548_, 2);
lean_dec(v_unused_5583_);
v_unused_5584_ = lean_ctor_get(v_ctx_5548_, 1);
lean_dec(v_unused_5584_);
v___x_5570_ = v_ctx_5548_;
v_isShared_5571_ = v_isSharedCheck_5582_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_toCommandContextInfo_5568_);
lean_dec(v_ctx_5548_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5582_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v_fileMap_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v_range_5576_; 
v_fileMap_5572_ = lean_ctor_get(v_toCommandContextInfo_5568_, 2);
lean_inc_ref_n(v_fileMap_5572_, 2);
lean_dec_ref(v_toCommandContextInfo_5568_);
v___x_5573_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5572_, v___y_5566_);
lean_dec(v___y_5566_);
v___x_5574_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5572_, v___y_5567_);
lean_dec(v___y_5567_);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 1, v___x_5574_);
lean_ctor_set(v___x_5556_, 0, v___x_5573_);
v_range_5576_ = v___x_5556_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5581_, 1, v___x_5574_);
v_range_5576_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
lean_object* v___x_5578_; 
lean_inc_ref(v_range_5576_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 2, v_range_5576_);
lean_ctor_set(v___x_5570_, 1, v_range_5576_);
lean_ctor_set(v___x_5570_, 0, v___x_5564_);
v___x_5578_ = v___x_5570_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_range_5576_);
lean_ctor_set(v_reuseFailAlloc_5580_, 2, v_range_5576_);
v___x_5578_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
lean_object* v___x_5579_; 
v___x_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
v___y_5559_ = v___x_5579_;
goto v___jp_5558_;
}
}
}
}
v___jp_5585_:
{
uint8_t v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = 0;
v___x_5587_ = l_Lean_Syntax_getRange_x3f(v_stx_5549_, v___x_5586_);
if (lean_obj_tag(v___x_5587_) == 1)
{
lean_object* v_val_5588_; 
v_val_5588_ = lean_ctor_get(v___x_5587_, 0);
lean_inc(v_val_5588_);
lean_dec_ref(v___x_5587_);
if (v_snd_5550_ == 0)
{
lean_object* v_start_5589_; lean_object* v_stop_5590_; 
v_start_5589_ = lean_ctor_get(v_val_5588_, 0);
lean_inc(v_start_5589_);
v_stop_5590_ = lean_ctor_get(v_val_5588_, 1);
lean_inc(v_stop_5590_);
lean_dec(v_val_5588_);
v___y_5566_ = v_start_5589_;
v___y_5567_ = v_stop_5590_;
goto v___jp_5565_;
}
else
{
lean_object* v_start_5591_; lean_object* v_stop_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v_start_5591_ = lean_ctor_get(v_val_5588_, 0);
lean_inc(v_start_5591_);
v_stop_5592_ = lean_ctor_get(v_val_5588_, 1);
lean_inc(v_stop_5592_);
lean_dec(v_val_5588_);
v___x_5593_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5594_ = lean_nat_add(v_stop_5592_, v___x_5593_);
lean_dec(v_stop_5592_);
v___y_5566_ = v_start_5591_;
v___y_5567_ = v___x_5594_;
goto v___jp_5565_;
}
}
else
{
lean_object* v___x_5595_; 
lean_dec(v___x_5587_);
lean_dec_ref(v___x_5564_);
lean_del_object(v___x_5556_);
lean_dec_ref(v_ctx_5548_);
v___x_5595_ = lean_box(0);
v___y_5559_ = v___x_5595_;
goto v___jp_5558_;
}
}
v___jp_5597_:
{
if (v___x_5596_ == 0)
{
goto v___jp_5585_;
}
else
{
lean_object* v___x_5598_; 
lean_dec_ref(v___x_5564_);
lean_del_object(v___x_5556_);
lean_dec_ref(v_ctx_5548_);
v___x_5598_ = lean_box(0);
v___y_5559_ = v___x_5598_;
goto v___jp_5558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5608_, lean_object* v_caps_5609_, lean_object* v_mkItem_5610_, lean_object* v_ctx_5611_, lean_object* v_stx_5612_, lean_object* v_snd_5613_, lean_object* v_x_5614_, lean_object* v_____s_5615_){
_start:
{
uint8_t v_snd_1079__boxed_5616_; lean_object* v_res_5617_; 
v_snd_1079__boxed_5616_ = lean_unbox(v_snd_5613_);
v_res_5617_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5608_, v_caps_5609_, v_mkItem_5610_, v_ctx_5611_, v_stx_5612_, v_snd_1079__boxed_5616_, v_x_5614_, v_____s_5615_);
lean_dec(v_stx_5612_);
lean_dec_ref(v_caps_5609_);
lean_dec_ref(v_fst_5608_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5619_, lean_object* v_entries_5620_, lean_object* v_stx_5621_, lean_object* v_caps_5622_, lean_object* v_ctx_5623_, lean_object* v_mkItem_5624_){
_start:
{
lean_object* v_fst_5626_; uint8_t v_snd_5627_; uint8_t v___x_5632_; lean_object* v___x_5633_; 
v___x_5632_ = 0;
v___x_5633_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5621_, v___x_5632_, v___x_5632_);
if (lean_obj_tag(v___x_5633_) == 0)
{
lean_object* v___x_5634_; 
v___x_5634_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5626_ = v___x_5634_;
v_snd_5627_ = v___x_5632_;
goto v___jp_5625_;
}
else
{
lean_object* v_val_5635_; lean_object* v_str_5636_; lean_object* v_startPos_5637_; lean_object* v_stopPos_5638_; uint8_t v___y_5640_; uint8_t v___x_5642_; 
v_val_5635_ = lean_ctor_get(v___x_5633_, 0);
lean_inc(v_val_5635_);
lean_dec_ref(v___x_5633_);
v_str_5636_ = lean_ctor_get(v_val_5635_, 0);
lean_inc_ref(v_str_5636_);
v_startPos_5637_ = lean_ctor_get(v_val_5635_, 1);
lean_inc(v_startPos_5637_);
v_stopPos_5638_ = lean_ctor_get(v_val_5635_, 2);
lean_inc(v_stopPos_5638_);
lean_dec(v_val_5635_);
v___x_5642_ = lean_string_utf8_at_end(v_str_5636_, v_stopPos_5638_);
if (v___x_5642_ == 0)
{
uint32_t v___x_5643_; uint32_t v___x_5644_; uint8_t v___x_5645_; 
v___x_5643_ = lean_string_utf8_get(v_str_5636_, v_stopPos_5638_);
v___x_5644_ = 46;
v___x_5645_ = lean_uint32_dec_eq(v___x_5643_, v___x_5644_);
if (v___x_5645_ == 0)
{
v___y_5640_ = v___x_5645_;
goto v___jp_5639_;
}
else
{
lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5646_ = lean_string_utf8_extract(v_str_5636_, v_startPos_5637_, v_stopPos_5638_);
lean_dec(v_stopPos_5638_);
lean_dec(v_startPos_5637_);
lean_dec_ref(v_str_5636_);
v___x_5647_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5648_ = lean_string_append(v___x_5646_, v___x_5647_);
v_fst_5626_ = v___x_5648_;
v_snd_5627_ = v___x_5645_;
goto v___jp_5625_;
}
}
else
{
v___y_5640_ = v___x_5632_;
goto v___jp_5639_;
}
v___jp_5639_:
{
lean_object* v___x_5641_; 
v___x_5641_ = lean_string_utf8_extract(v_str_5636_, v_startPos_5637_, v_stopPos_5638_);
lean_dec(v_stopPos_5638_);
lean_dec(v_startPos_5637_);
lean_dec_ref(v_str_5636_);
v_fst_5626_ = v___x_5641_;
v_snd_5627_ = v___y_5640_;
goto v___jp_5625_;
}
}
v___jp_5625_:
{
lean_object* v___x_5628_; lean_object* v___f_5629_; lean_object* v_items_5630_; lean_object* v___x_5631_; 
v___x_5628_ = lean_box(v_snd_5627_);
v___f_5629_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5629_, 0, v_fst_5626_);
lean_closure_set(v___f_5629_, 1, v_caps_5622_);
lean_closure_set(v___f_5629_, 2, v_mkItem_5624_);
lean_closure_set(v___f_5629_, 3, v_ctx_5623_);
lean_closure_set(v___f_5629_, 4, v_stx_5621_);
lean_closure_set(v___f_5629_, 5, v___x_5628_);
v_items_5630_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5631_ = lean_apply_4(v_inst_5619_, lean_box(0), v_entries_5620_, v_items_5630_, v___f_5629_);
return v___x_5631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5649_, lean_object* v_00_u03b1_5650_, lean_object* v_inst_5651_, lean_object* v_entries_5652_, lean_object* v_stx_5653_, lean_object* v_caps_5654_, lean_object* v_ctx_5655_, lean_object* v_mkItem_5656_){
_start:
{
lean_object* v___x_5657_; 
v___x_5657_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5651_, v_entries_5652_, v_stx_5653_, v_caps_5654_, v_ctx_5655_, v_mkItem_5656_);
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v_options_5663_, lean_object* v_completionInfoPos_5664_, lean_object* v_uri_5665_, lean_object* v_pos_5666_, lean_object* v_name_5667_, lean_object* v_decl_5668_, lean_object* v_textEdit_x3f_5669_){
_start:
{
lean_object* v_defValue_5670_; lean_object* v_descr_5671_; lean_object* v_map_5672_; uint8_t v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___y_5677_; lean_object* v___x_5690_; 
v_defValue_5670_ = lean_ctor_get(v_decl_5668_, 2);
lean_inc_ref(v_defValue_5670_);
v_descr_5671_ = lean_ctor_get(v_decl_5668_, 3);
lean_inc_ref(v_descr_5671_);
lean_dec_ref(v_decl_5668_);
v_map_5672_ = lean_ctor_get(v_options_5663_, 0);
v___x_5673_ = 1;
lean_inc(v_name_5667_);
v___x_5674_ = l_Lean_Name_toString(v_name_5667_, v___x_5673_);
v___x_5675_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5690_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5672_, v_name_5667_);
lean_dec(v_name_5667_);
if (lean_obj_tag(v___x_5690_) == 0)
{
v___y_5677_ = v_defValue_5670_;
goto v___jp_5676_;
}
else
{
if (lean_obj_tag(v___x_5690_) == 0)
{
v___y_5677_ = v_defValue_5670_;
goto v___jp_5676_;
}
else
{
lean_object* v_val_5691_; 
lean_dec_ref(v_defValue_5670_);
v_val_5691_ = lean_ctor_get(v___x_5690_, 0);
lean_inc(v_val_5691_);
lean_dec_ref(v___x_5690_);
v___y_5677_ = v_val_5691_;
goto v___jp_5676_;
}
}
v___jp_5676_:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5678_ = lean_data_value_to_string(v___y_5677_);
v___x_5679_ = lean_string_append(v___x_5675_, v___x_5678_);
lean_dec_ref(v___x_5678_);
v___x_5680_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5681_ = lean_string_append(v___x_5679_, v___x_5680_);
v___x_5682_ = lean_string_append(v___x_5681_, v_descr_5671_);
lean_dec_ref(v_descr_5671_);
v___x_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
v___x_5684_ = lean_box(0);
v___x_5685_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5686_, 0, v_completionInfoPos_5664_);
v___x_5687_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5687_, 0, v_uri_5665_);
lean_ctor_set(v___x_5687_, 1, v_pos_5666_);
lean_ctor_set(v___x_5687_, 2, v___x_5686_);
lean_ctor_set(v___x_5687_, 3, v___x_5684_);
v___x_5688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
v___x_5689_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5674_);
lean_ctor_set(v___x_5689_, 1, v___x_5683_);
lean_ctor_set(v___x_5689_, 2, v___x_5684_);
lean_ctor_set(v___x_5689_, 3, v___x_5685_);
lean_ctor_set(v___x_5689_, 4, v_textEdit_x3f_5669_);
lean_ctor_set(v___x_5689_, 5, v___x_5684_);
lean_ctor_set(v___x_5689_, 6, v___x_5688_);
lean_ctor_set(v___x_5689_, 7, v___x_5684_);
return v___x_5689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v_options_5692_, lean_object* v_completionInfoPos_5693_, lean_object* v_uri_5694_, lean_object* v_pos_5695_, lean_object* v_name_5696_, lean_object* v_decl_5697_, lean_object* v_textEdit_x3f_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l_Lean_Server_Completion_optionCompletion___lam__0(v_options_5692_, v_completionInfoPos_5693_, v_uri_5694_, v_pos_5695_, v_name_5696_, v_decl_5697_, v_textEdit_x3f_5698_);
lean_dec_ref(v_options_5692_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5700_, lean_object* v_stx_5701_, lean_object* v_ctx_5702_, uint8_t v_snd_5703_, lean_object* v_fst_5704_, lean_object* v_caps_5705_, lean_object* v_init_5706_, lean_object* v_x_5707_){
_start:
{
if (lean_obj_tag(v_x_5707_) == 0)
{
lean_object* v_k_5708_; lean_object* v_v_5709_; lean_object* v_l_5710_; lean_object* v_r_5711_; lean_object* v___x_5712_; lean_object* v_a_5713_; lean_object* v___y_5715_; uint8_t v___x_5719_; lean_object* v___x_5720_; lean_object* v___y_5722_; lean_object* v___y_5723_; uint8_t v___x_5742_; 
v_k_5708_ = lean_ctor_get(v_x_5707_, 1);
lean_inc_n(v_k_5708_, 2);
v_v_5709_ = lean_ctor_get(v_x_5707_, 2);
lean_inc(v_v_5709_);
v_l_5710_ = lean_ctor_get(v_x_5707_, 3);
lean_inc(v_l_5710_);
v_r_5711_ = lean_ctor_get(v_x_5707_, 4);
lean_inc(v_r_5711_);
lean_dec_ref(v_x_5707_);
lean_inc_ref(v_ctx_5702_);
lean_inc_ref(v_mkItem_5700_);
v___x_5712_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5700_, v_stx_5701_, v_ctx_5702_, v_snd_5703_, v_fst_5704_, v_caps_5705_, v_init_5706_, v_l_5710_);
v_a_5713_ = lean_ctor_get(v___x_5712_, 0);
lean_inc(v_a_5713_);
v___x_5719_ = 1;
v___x_5720_ = l_Lean_Name_toString(v_k_5708_, v___x_5719_);
v___x_5742_ = l_String_charactersIn(v_fst_5704_, v___x_5720_);
if (v___x_5742_ == 0)
{
lean_object* v_a_5745_; 
lean_dec_ref(v___x_5720_);
lean_dec(v_a_5713_);
lean_dec(v_v_5709_);
lean_dec(v_k_5708_);
v_a_5745_ = lean_ctor_get(v___x_5712_, 0);
lean_inc(v_a_5745_);
lean_dec_ref(v___x_5712_);
v_init_5706_ = v_a_5745_;
v_x_5707_ = v_r_5711_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5747_; 
lean_dec_ref(v___x_5712_);
v_textDocument_x3f_5747_ = lean_ctor_get(v_caps_5705_, 0);
if (lean_obj_tag(v_textDocument_x3f_5747_) == 0)
{
goto v___jp_5743_;
}
else
{
lean_object* v_val_5748_; lean_object* v_completion_x3f_5749_; 
v_val_5748_ = lean_ctor_get(v_textDocument_x3f_5747_, 0);
v_completion_x3f_5749_ = lean_ctor_get(v_val_5748_, 0);
if (lean_obj_tag(v_completion_x3f_5749_) == 0)
{
goto v___jp_5743_;
}
else
{
lean_object* v_val_5750_; 
v_val_5750_ = lean_ctor_get(v_completion_x3f_5749_, 0);
if (lean_obj_tag(v_val_5750_) == 0)
{
goto v___jp_5743_;
}
else
{
lean_object* v_val_5751_; 
v_val_5751_ = lean_ctor_get(v_val_5750_, 0);
if (lean_obj_tag(v_val_5751_) == 0)
{
goto v___jp_5743_;
}
else
{
lean_object* v_val_5752_; uint8_t v___x_5753_; 
v_val_5752_ = lean_ctor_get(v_val_5751_, 0);
v___x_5753_ = lean_unbox(v_val_5752_);
if (v___x_5753_ == 0)
{
goto v___jp_5743_;
}
else
{
goto v___jp_5731_;
}
}
}
}
}
}
v___jp_5714_:
{
lean_object* v___x_5716_; lean_object* v_items_5717_; 
lean_inc_ref(v_mkItem_5700_);
v___x_5716_ = lean_apply_3(v_mkItem_5700_, v_k_5708_, v_v_5709_, v___y_5715_);
v_items_5717_ = lean_array_push(v_a_5713_, v___x_5716_);
v_init_5706_ = v_items_5717_;
v_x_5707_ = v_r_5711_;
goto _start;
}
v___jp_5721_:
{
lean_object* v_toCommandContextInfo_5724_; lean_object* v_fileMap_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v_range_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; 
v_toCommandContextInfo_5724_ = lean_ctor_get(v_ctx_5702_, 0);
v_fileMap_5725_ = lean_ctor_get(v_toCommandContextInfo_5724_, 2);
lean_inc_ref_n(v_fileMap_5725_, 2);
v___x_5726_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5725_, v___y_5722_);
lean_dec(v___y_5722_);
v___x_5727_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5725_, v___y_5723_);
lean_dec(v___y_5723_);
v_range_5728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5728_, 0, v___x_5726_);
lean_ctor_set(v_range_5728_, 1, v___x_5727_);
lean_inc_ref(v_range_5728_);
v___x_5729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5720_);
lean_ctor_set(v___x_5729_, 1, v_range_5728_);
lean_ctor_set(v___x_5729_, 2, v_range_5728_);
v___x_5730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5729_);
v___y_5715_ = v___x_5730_;
goto v___jp_5714_;
}
v___jp_5731_:
{
uint8_t v___x_5732_; lean_object* v___x_5733_; 
v___x_5732_ = 0;
v___x_5733_ = l_Lean_Syntax_getRange_x3f(v_stx_5701_, v___x_5732_);
if (lean_obj_tag(v___x_5733_) == 1)
{
lean_object* v_val_5734_; 
v_val_5734_ = lean_ctor_get(v___x_5733_, 0);
lean_inc(v_val_5734_);
lean_dec_ref(v___x_5733_);
if (v_snd_5703_ == 0)
{
lean_object* v_start_5735_; lean_object* v_stop_5736_; 
v_start_5735_ = lean_ctor_get(v_val_5734_, 0);
lean_inc(v_start_5735_);
v_stop_5736_ = lean_ctor_get(v_val_5734_, 1);
lean_inc(v_stop_5736_);
lean_dec(v_val_5734_);
v___y_5722_ = v_start_5735_;
v___y_5723_ = v_stop_5736_;
goto v___jp_5721_;
}
else
{
lean_object* v_start_5737_; lean_object* v_stop_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
v_start_5737_ = lean_ctor_get(v_val_5734_, 0);
lean_inc(v_start_5737_);
v_stop_5738_ = lean_ctor_get(v_val_5734_, 1);
lean_inc(v_stop_5738_);
lean_dec(v_val_5734_);
v___x_5739_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5740_ = lean_nat_add(v_stop_5738_, v___x_5739_);
lean_dec(v_stop_5738_);
v___y_5722_ = v_start_5737_;
v___y_5723_ = v___x_5740_;
goto v___jp_5721_;
}
}
else
{
lean_object* v___x_5741_; 
lean_dec(v___x_5733_);
lean_dec_ref(v___x_5720_);
v___x_5741_ = lean_box(0);
v___y_5715_ = v___x_5741_;
goto v___jp_5714_;
}
}
v___jp_5743_:
{
if (v___x_5742_ == 0)
{
goto v___jp_5731_;
}
else
{
lean_object* v___x_5744_; 
lean_dec_ref(v___x_5720_);
v___x_5744_ = lean_box(0);
v___y_5715_ = v___x_5744_;
goto v___jp_5714_;
}
}
}
else
{
lean_object* v___x_5754_; 
lean_dec_ref(v_ctx_5702_);
lean_dec_ref(v_mkItem_5700_);
v___x_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5754_, 0, v_init_5706_);
return v___x_5754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5755_, lean_object* v_stx_5756_, lean_object* v_ctx_5757_, lean_object* v_snd_5758_, lean_object* v_fst_5759_, lean_object* v_caps_5760_, lean_object* v_init_5761_, lean_object* v_x_5762_){
_start:
{
uint8_t v_snd_1415__boxed_5763_; lean_object* v_res_5764_; 
v_snd_1415__boxed_5763_ = lean_unbox(v_snd_5758_);
v_res_5764_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5755_, v_stx_5756_, v_ctx_5757_, v_snd_1415__boxed_5763_, v_fst_5759_, v_caps_5760_, v_init_5761_, v_x_5762_);
lean_dec_ref(v_caps_5760_);
lean_dec_ref(v_fst_5759_);
lean_dec(v_stx_5756_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5765_, lean_object* v_stx_5766_, lean_object* v_caps_5767_, lean_object* v_ctx_5768_, lean_object* v_mkItem_5769_){
_start:
{
lean_object* v_fst_5771_; uint8_t v_snd_5772_; uint8_t v___x_5776_; lean_object* v___x_5777_; 
v___x_5776_ = 0;
v___x_5777_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5766_, v___x_5776_, v___x_5776_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v___x_5778_; 
v___x_5778_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5771_ = v___x_5778_;
v_snd_5772_ = v___x_5776_;
goto v___jp_5770_;
}
else
{
lean_object* v_val_5779_; lean_object* v_str_5780_; lean_object* v_startPos_5781_; lean_object* v_stopPos_5782_; uint8_t v___y_5784_; uint8_t v___x_5786_; 
v_val_5779_ = lean_ctor_get(v___x_5777_, 0);
lean_inc(v_val_5779_);
lean_dec_ref(v___x_5777_);
v_str_5780_ = lean_ctor_get(v_val_5779_, 0);
lean_inc_ref(v_str_5780_);
v_startPos_5781_ = lean_ctor_get(v_val_5779_, 1);
lean_inc(v_startPos_5781_);
v_stopPos_5782_ = lean_ctor_get(v_val_5779_, 2);
lean_inc(v_stopPos_5782_);
lean_dec(v_val_5779_);
v___x_5786_ = lean_string_utf8_at_end(v_str_5780_, v_stopPos_5782_);
if (v___x_5786_ == 0)
{
uint32_t v___x_5787_; uint32_t v___x_5788_; uint8_t v___x_5789_; 
v___x_5787_ = lean_string_utf8_get(v_str_5780_, v_stopPos_5782_);
v___x_5788_ = 46;
v___x_5789_ = lean_uint32_dec_eq(v___x_5787_, v___x_5788_);
if (v___x_5789_ == 0)
{
v___y_5784_ = v___x_5789_;
goto v___jp_5783_;
}
else
{
lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; 
v___x_5790_ = lean_string_utf8_extract(v_str_5780_, v_startPos_5781_, v_stopPos_5782_);
lean_dec(v_stopPos_5782_);
lean_dec(v_startPos_5781_);
lean_dec_ref(v_str_5780_);
v___x_5791_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5792_ = lean_string_append(v___x_5790_, v___x_5791_);
v_fst_5771_ = v___x_5792_;
v_snd_5772_ = v___x_5789_;
goto v___jp_5770_;
}
}
else
{
v___y_5784_ = v___x_5776_;
goto v___jp_5783_;
}
v___jp_5783_:
{
lean_object* v___x_5785_; 
v___x_5785_ = lean_string_utf8_extract(v_str_5780_, v_startPos_5781_, v_stopPos_5782_);
lean_dec(v_stopPos_5782_);
lean_dec(v_startPos_5781_);
lean_dec_ref(v_str_5780_);
v_fst_5771_ = v___x_5785_;
v_snd_5772_ = v___y_5784_;
goto v___jp_5770_;
}
}
v___jp_5770_:
{
lean_object* v_items_5773_; lean_object* v___x_5774_; lean_object* v_a_5775_; 
v_items_5773_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5774_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5769_, v_stx_5766_, v_ctx_5768_, v_snd_5772_, v_fst_5771_, v_caps_5767_, v_items_5773_, v_entries_5765_);
lean_dec_ref(v_fst_5771_);
v_a_5775_ = lean_ctor_get(v___x_5774_, 0);
lean_inc(v_a_5775_);
lean_dec_ref(v___x_5774_);
return v_a_5775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object* v_entries_5793_, lean_object* v_stx_5794_, lean_object* v_caps_5795_, lean_object* v_ctx_5796_, lean_object* v_mkItem_5797_){
_start:
{
lean_object* v_res_5798_; 
v_res_5798_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_entries_5793_, v_stx_5794_, v_caps_5795_, v_ctx_5796_, v_mkItem_5797_);
lean_dec_ref(v_caps_5795_);
lean_dec(v_stx_5794_);
return v_res_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object* v_completionInfoPos_5799_, lean_object* v_uri_5800_, lean_object* v_pos_5801_, lean_object* v_stx_5802_, lean_object* v_caps_5803_, lean_object* v_ctx_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v___x_5810_; 
v___x_5810_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5823_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5823_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5823_ == 0)
{
v___x_5813_ = v___x_5810_;
v_isShared_5814_ = v_isSharedCheck_5823_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_a_5811_);
lean_dec(v___x_5810_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5823_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v_options_5815_; lean_object* v___f_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5821_; 
v_options_5815_ = lean_ctor_get(v___y_5807_, 2);
lean_inc_ref(v_options_5815_);
lean_dec_ref(v___y_5807_);
v___f_5816_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5816_, 0, v_options_5815_);
lean_closure_set(v___f_5816_, 1, v_completionInfoPos_5799_);
lean_closure_set(v___f_5816_, 2, v_uri_5800_);
lean_closure_set(v___f_5816_, 3, v_pos_5801_);
v___x_5817_ = lean_unsigned_to_nat(1u);
v___x_5818_ = l_Lean_Syntax_getArg(v_stx_5802_, v___x_5817_);
v___x_5819_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_a_5811_, v___x_5818_, v_caps_5803_, v_ctx_5804_, v___f_5816_);
lean_dec(v___x_5818_);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 0, v___x_5819_);
v___x_5821_ = v___x_5813_;
goto v_reusejp_5820_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5819_);
v___x_5821_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5820_;
}
v_reusejp_5820_:
{
return v___x_5821_;
}
}
}
else
{
lean_object* v_a_5824_; lean_object* v___x_5826_; uint8_t v_isShared_5827_; uint8_t v_isSharedCheck_5836_; 
lean_dec_ref(v_ctx_5804_);
lean_dec_ref(v_pos_5801_);
lean_dec_ref(v_uri_5800_);
lean_dec(v_completionInfoPos_5799_);
v_a_5824_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5836_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5836_ == 0)
{
v___x_5826_ = v___x_5810_;
v_isShared_5827_ = v_isSharedCheck_5836_;
goto v_resetjp_5825_;
}
else
{
lean_inc(v_a_5824_);
lean_dec(v___x_5810_);
v___x_5826_ = lean_box(0);
v_isShared_5827_ = v_isSharedCheck_5836_;
goto v_resetjp_5825_;
}
v_resetjp_5825_:
{
lean_object* v_ref_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5834_; 
v_ref_5828_ = lean_ctor_get(v___y_5807_, 5);
lean_inc(v_ref_5828_);
lean_dec_ref(v___y_5807_);
v___x_5829_ = lean_io_error_to_string(v_a_5824_);
v___x_5830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5829_);
v___x_5831_ = l_Lean_MessageData_ofFormat(v___x_5830_);
v___x_5832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5832_, 0, v_ref_5828_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
if (v_isShared_5827_ == 0)
{
lean_ctor_set(v___x_5826_, 0, v___x_5832_);
v___x_5834_ = v___x_5826_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v___x_5832_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object* v_completionInfoPos_5837_, lean_object* v_uri_5838_, lean_object* v_pos_5839_, lean_object* v_stx_5840_, lean_object* v_caps_5841_, lean_object* v_ctx_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5837_, v_uri_5838_, v_pos_5839_, v_stx_5840_, v_caps_5841_, v_ctx_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
lean_dec(v___y_5846_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec_ref(v_caps_5841_);
lean_dec(v_stx_5840_);
return v_res_5848_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__0(void){
_start:
{
lean_object* v___x_5849_; 
v___x_5849_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5849_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1(void){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__0, &l_Lean_Server_Completion_optionCompletion___closed__0_once, _init_l_Lean_Server_Completion_optionCompletion___closed__0);
v___x_5851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5850_);
return v___x_5851_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2(void){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5852_ = lean_unsigned_to_nat(32u);
v___x_5853_ = lean_mk_empty_array_with_capacity(v___x_5852_);
v___x_5854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5853_);
return v___x_5854_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3(void){
_start:
{
size_t v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5855_ = ((size_t)5ULL);
v___x_5856_ = lean_unsigned_to_nat(0u);
v___x_5857_ = lean_unsigned_to_nat(32u);
v___x_5858_ = lean_mk_empty_array_with_capacity(v___x_5857_);
v___x_5859_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__2, &l_Lean_Server_Completion_optionCompletion___closed__2_once, _init_l_Lean_Server_Completion_optionCompletion___closed__2);
v___x_5860_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5860_, 0, v___x_5859_);
lean_ctor_set(v___x_5860_, 1, v___x_5858_);
lean_ctor_set(v___x_5860_, 2, v___x_5856_);
lean_ctor_set(v___x_5860_, 3, v___x_5856_);
lean_ctor_set_usize(v___x_5860_, 4, v___x_5855_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5861_ = lean_box(1);
v___x_5862_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__3, &l_Lean_Server_Completion_optionCompletion___closed__3_once, _init_l_Lean_Server_Completion_optionCompletion___closed__3);
v___x_5863_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__1, &l_Lean_Server_Completion_optionCompletion___closed__1_once, _init_l_Lean_Server_Completion_optionCompletion___closed__1);
v___x_5864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5863_);
lean_ctor_set(v___x_5864_, 1, v___x_5862_);
lean_ctor_set(v___x_5864_, 2, v___x_5861_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* v_uri_5865_, lean_object* v_pos_5866_, lean_object* v_completionInfoPos_5867_, lean_object* v_ctx_5868_, lean_object* v_stx_5869_, lean_object* v_caps_5870_){
_start:
{
lean_object* v___f_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; 
lean_inc_ref(v_ctx_5868_);
v___f_5872_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__1___boxed), 11, 6);
lean_closure_set(v___f_5872_, 0, v_completionInfoPos_5867_);
lean_closure_set(v___f_5872_, 1, v_uri_5865_);
lean_closure_set(v___f_5872_, 2, v_pos_5866_);
lean_closure_set(v___f_5872_, 3, v_stx_5869_);
lean_closure_set(v___f_5872_, 4, v_caps_5870_);
lean_closure_set(v___f_5872_, 5, v_ctx_5868_);
v___x_5873_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5874_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5868_, v___x_5873_, v___f_5872_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* v_uri_5875_, lean_object* v_pos_5876_, lean_object* v_completionInfoPos_5877_, lean_object* v_ctx_5878_, lean_object* v_stx_5879_, lean_object* v_caps_5880_, lean_object* v_a_5881_){
_start:
{
lean_object* v_res_5882_; 
v_res_5882_ = l_Lean_Server_Completion_optionCompletion(v_uri_5875_, v_pos_5876_, v_completionInfoPos_5877_, v_ctx_5878_, v_stx_5879_, v_caps_5880_);
return v_res_5882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object* v_completionInfoPos_5892_, lean_object* v_uri_5893_, lean_object* v_pos_5894_, lean_object* v_name_5895_, lean_object* v_explan_5896_, lean_object* v_textEdit_x3f_5897_){
_start:
{
lean_object* v_metadata_5898_; lean_object* v_removedVersion_x3f_5899_; uint8_t v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; uint8_t v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v_metadata_5898_ = lean_ctor_get(v_explan_5896_, 1);
v_removedVersion_x3f_5899_ = lean_ctor_get(v_metadata_5898_, 2);
v___x_5900_ = 1;
v___x_5901_ = l_Lean_Name_toString(v_name_5895_, v___x_5900_);
v___x_5902_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1));
v___x_5903_ = 1;
v___x_5904_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_5896_);
v___x_5905_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5905_, 0, v___x_5904_);
lean_ctor_set_uint8(v___x_5905_, sizeof(void*)*1, v___x_5903_);
v___x_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5905_);
v___x_5907_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5908_ = lean_box(0);
v___x_5909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5909_, 0, v_completionInfoPos_5892_);
v___x_5910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5910_, 0, v_uri_5893_);
lean_ctor_set(v___x_5910_, 1, v_pos_5894_);
lean_ctor_set(v___x_5910_, 2, v___x_5909_);
lean_ctor_set(v___x_5910_, 3, v___x_5908_);
v___x_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
if (lean_obj_tag(v_removedVersion_x3f_5899_) == 0)
{
lean_object* v___x_5912_; 
v___x_5912_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5901_);
lean_ctor_set(v___x_5912_, 1, v___x_5902_);
lean_ctor_set(v___x_5912_, 2, v___x_5906_);
lean_ctor_set(v___x_5912_, 3, v___x_5907_);
lean_ctor_set(v___x_5912_, 4, v_textEdit_x3f_5897_);
lean_ctor_set(v___x_5912_, 5, v___x_5908_);
lean_ctor_set(v___x_5912_, 6, v___x_5911_);
lean_ctor_set(v___x_5912_, 7, v___x_5908_);
return v___x_5912_;
}
else
{
lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5913_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3));
v___x_5914_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5901_);
lean_ctor_set(v___x_5914_, 1, v___x_5902_);
lean_ctor_set(v___x_5914_, 2, v___x_5906_);
lean_ctor_set(v___x_5914_, 3, v___x_5907_);
lean_ctor_set(v___x_5914_, 4, v_textEdit_x3f_5897_);
lean_ctor_set(v___x_5914_, 5, v___x_5908_);
lean_ctor_set(v___x_5914_, 6, v___x_5911_);
lean_ctor_set(v___x_5914_, 7, v___x_5913_);
return v___x_5914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object* v_completionInfoPos_5915_, lean_object* v_uri_5916_, lean_object* v_pos_5917_, lean_object* v_name_5918_, lean_object* v_explan_5919_, lean_object* v_textEdit_x3f_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l_Lean_Server_Completion_errorNameCompletion___lam__0(v_completionInfoPos_5915_, v_uri_5916_, v_pos_5917_, v_name_5918_, v_explan_5919_, v_textEdit_x3f_5920_);
lean_dec_ref(v_explan_5919_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object* v_init_5922_, lean_object* v_x_5923_){
_start:
{
if (lean_obj_tag(v_x_5923_) == 0)
{
lean_object* v_k_5924_; lean_object* v_v_5925_; lean_object* v_l_5926_; lean_object* v_r_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; 
v_k_5924_ = lean_ctor_get(v_x_5923_, 1);
v_v_5925_ = lean_ctor_get(v_x_5923_, 2);
v_l_5926_ = lean_ctor_get(v_x_5923_, 3);
v_r_5927_ = lean_ctor_get(v_x_5923_, 4);
v___x_5928_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5922_, v_l_5926_);
lean_inc(v_v_5925_);
lean_inc(v_k_5924_);
v___x_5929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5929_, 0, v_k_5924_);
lean_ctor_set(v___x_5929_, 1, v_v_5925_);
v___x_5930_ = lean_array_push(v___x_5928_, v___x_5929_);
v_init_5922_ = v___x_5930_;
v_x_5923_ = v_r_5927_;
goto _start;
}
else
{
return v_init_5922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5932_, lean_object* v_x_5933_){
_start:
{
lean_object* v_res_5934_; 
v_res_5934_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5932_, v_x_5933_);
lean_dec(v_x_5933_);
return v_res_5934_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_5935_, lean_object* v_e_5936_, lean_object* v_e_x27_5937_){
_start:
{
lean_object* v_fst_5938_; lean_object* v_fst_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; uint8_t v___x_5942_; 
v_fst_5938_ = lean_ctor_get(v_e_5936_, 0);
lean_inc(v_fst_5938_);
lean_dec_ref(v_e_5936_);
v_fst_5939_ = lean_ctor_get(v_e_x27_5937_, 0);
lean_inc(v_fst_5939_);
lean_dec_ref(v_e_x27_5937_);
v___x_5940_ = l_Lean_Name_toString(v_fst_5938_, v___x_5935_);
v___x_5941_ = l_Lean_Name_toString(v_fst_5939_, v___x_5935_);
v___x_5942_ = lean_string_dec_lt(v___x_5940_, v___x_5941_);
lean_dec_ref(v___x_5941_);
lean_dec_ref(v___x_5940_);
return v___x_5942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_5943_, lean_object* v_e_5944_, lean_object* v_e_x27_5945_){
_start:
{
uint8_t v___x_1462__boxed_5946_; uint8_t v_res_5947_; lean_object* v_r_5948_; 
v___x_1462__boxed_5946_ = lean_unbox(v___x_5943_);
v_res_5947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1462__boxed_5946_, v_e_5944_, v_e_x27_5945_);
v_r_5948_ = lean_box(v_res_5947_);
return v_r_5948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_as_5949_, lean_object* v_lo_5950_, lean_object* v_hi_5951_){
_start:
{
uint8_t v___x_5952_; 
v___x_5952_ = lean_nat_dec_lt(v_lo_5950_, v_hi_5951_);
if (v___x_5952_ == 0)
{
lean_dec(v_lo_5950_);
return v_as_5949_;
}
else
{
lean_object* v___x_5953_; lean_object* v___f_5954_; lean_object* v___x_5955_; lean_object* v_fst_5956_; lean_object* v_snd_5957_; uint8_t v___x_5958_; 
v___x_5953_ = lean_box(v___x_5952_);
v___f_5954_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5954_, 0, v___x_5953_);
lean_inc(v_lo_5950_);
v___x_5955_ = l_Array_qpartition___redArg(v_as_5949_, v___f_5954_, v_lo_5950_, v_hi_5951_);
v_fst_5956_ = lean_ctor_get(v___x_5955_, 0);
lean_inc(v_fst_5956_);
v_snd_5957_ = lean_ctor_get(v___x_5955_, 1);
lean_inc(v_snd_5957_);
lean_dec_ref(v___x_5955_);
v___x_5958_ = lean_nat_dec_le(v_hi_5951_, v_fst_5956_);
if (v___x_5958_ == 0)
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5959_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_snd_5957_, v_lo_5950_, v_fst_5956_);
v___x_5960_ = lean_unsigned_to_nat(1u);
v___x_5961_ = lean_nat_add(v_fst_5956_, v___x_5960_);
lean_dec(v_fst_5956_);
v_as_5949_ = v___x_5959_;
v_lo_5950_ = v___x_5961_;
goto _start;
}
else
{
lean_dec(v_fst_5956_);
lean_dec(v_lo_5950_);
return v_snd_5957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_as_5963_, lean_object* v_lo_5964_, lean_object* v_hi_5965_){
_start:
{
lean_object* v_res_5966_; 
v_res_5966_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_as_5963_, v_lo_5964_, v_hi_5965_);
lean_dec(v_hi_5965_);
return v_res_5966_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_5969_){
_start:
{
lean_object* v___x_5971_; lean_object* v_env_5972_; lean_object* v___x_5973_; lean_object* v_toEnvExtension_5974_; lean_object* v_asyncMode_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___y_5983_; lean_object* v___y_5984_; lean_object* v___x_5987_; uint8_t v___x_5988_; 
v___x_5971_ = lean_st_ref_get(v___y_5969_);
v_env_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc_ref(v_env_5972_);
lean_dec(v___x_5971_);
v___x_5973_ = l_Lean_errorExplanationExt;
v_toEnvExtension_5974_ = lean_ctor_get(v___x_5973_, 0);
v_asyncMode_5975_ = lean_ctor_get(v_toEnvExtension_5974_, 2);
v___x_5976_ = lean_box(1);
v___x_5977_ = lean_box(0);
v___x_5978_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5976_, v___x_5973_, v_env_5972_, v_asyncMode_5975_, v___x_5977_);
v___x_5979_ = lean_unsigned_to_nat(0u);
v___x_5980_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_5981_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_5980_, v___x_5978_);
lean_dec(v___x_5978_);
v___x_5987_ = lean_array_get_size(v___x_5981_);
v___x_5988_ = lean_nat_dec_eq(v___x_5987_, v___x_5979_);
if (v___x_5988_ == 0)
{
lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___y_5992_; uint8_t v___x_5994_; 
v___x_5989_ = lean_unsigned_to_nat(1u);
v___x_5990_ = lean_nat_sub(v___x_5987_, v___x_5989_);
v___x_5994_ = lean_nat_dec_le(v___x_5979_, v___x_5990_);
if (v___x_5994_ == 0)
{
lean_inc(v___x_5990_);
v___y_5992_ = v___x_5990_;
goto v___jp_5991_;
}
else
{
v___y_5992_ = v___x_5979_;
goto v___jp_5991_;
}
v___jp_5991_:
{
uint8_t v___x_5993_; 
v___x_5993_ = lean_nat_dec_le(v___y_5992_, v___x_5990_);
if (v___x_5993_ == 0)
{
lean_dec(v___x_5990_);
lean_inc(v___y_5992_);
v___y_5983_ = v___y_5992_;
v___y_5984_ = v___y_5992_;
goto v___jp_5982_;
}
else
{
v___y_5983_ = v___y_5992_;
v___y_5984_ = v___x_5990_;
goto v___jp_5982_;
}
}
}
else
{
lean_object* v___x_5995_; 
v___x_5995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5981_);
return v___x_5995_;
}
v___jp_5982_:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; 
v___x_5985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_5981_, v___y_5983_, v___y_5984_);
lean_dec(v___y_5984_);
v___x_5986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5985_);
return v___x_5986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_5996_, lean_object* v___y_5997_){
_start:
{
lean_object* v_res_5998_; 
v_res_5998_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_5996_);
lean_dec(v___y_5996_);
return v_res_5998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_5999_, lean_object* v_stx_6000_, lean_object* v_ctx_6001_, uint8_t v_snd_6002_, lean_object* v_fst_6003_, lean_object* v_caps_6004_, lean_object* v_as_6005_, size_t v_sz_6006_, size_t v_i_6007_, lean_object* v_b_6008_){
_start:
{
lean_object* v_a_6010_; uint8_t v___x_6014_; 
v___x_6014_ = lean_usize_dec_lt(v_i_6007_, v_sz_6006_);
if (v___x_6014_ == 0)
{
lean_dec_ref(v_ctx_6001_);
lean_dec_ref(v_mkItem_5999_);
return v_b_6008_;
}
else
{
lean_object* v_a_6015_; lean_object* v_fst_6016_; lean_object* v_snd_6017_; lean_object* v___x_6019_; uint8_t v_isShared_6020_; uint8_t v_isSharedCheck_6059_; 
v_a_6015_ = lean_array_uget(v_as_6005_, v_i_6007_);
v_fst_6016_ = lean_ctor_get(v_a_6015_, 0);
v_snd_6017_ = lean_ctor_get(v_a_6015_, 1);
v_isSharedCheck_6059_ = !lean_is_exclusive(v_a_6015_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6019_ = v_a_6015_;
v_isShared_6020_ = v_isSharedCheck_6059_;
goto v_resetjp_6018_;
}
else
{
lean_inc(v_snd_6017_);
lean_inc(v_fst_6016_);
lean_dec(v_a_6015_);
v___x_6019_ = lean_box(0);
v_isShared_6020_ = v_isSharedCheck_6059_;
goto v_resetjp_6018_;
}
v_resetjp_6018_:
{
lean_object* v___y_6022_; lean_object* v___x_6025_; lean_object* v___y_6027_; lean_object* v___y_6028_; uint8_t v___x_6049_; 
lean_inc(v_fst_6016_);
v___x_6025_ = l_Lean_Name_toString(v_fst_6016_, v___x_6014_);
v___x_6049_ = l_String_charactersIn(v_fst_6003_, v___x_6025_);
if (v___x_6049_ == 0)
{
lean_dec_ref(v___x_6025_);
lean_del_object(v___x_6019_);
lean_dec(v_snd_6017_);
lean_dec(v_fst_6016_);
v_a_6010_ = v_b_6008_;
goto v___jp_6009_;
}
else
{
lean_object* v_textDocument_x3f_6052_; 
v_textDocument_x3f_6052_ = lean_ctor_get(v_caps_6004_, 0);
if (lean_obj_tag(v_textDocument_x3f_6052_) == 0)
{
goto v___jp_6050_;
}
else
{
lean_object* v_val_6053_; lean_object* v_completion_x3f_6054_; 
v_val_6053_ = lean_ctor_get(v_textDocument_x3f_6052_, 0);
v_completion_x3f_6054_ = lean_ctor_get(v_val_6053_, 0);
if (lean_obj_tag(v_completion_x3f_6054_) == 0)
{
goto v___jp_6050_;
}
else
{
lean_object* v_val_6055_; 
v_val_6055_ = lean_ctor_get(v_completion_x3f_6054_, 0);
if (lean_obj_tag(v_val_6055_) == 0)
{
goto v___jp_6050_;
}
else
{
lean_object* v_val_6056_; 
v_val_6056_ = lean_ctor_get(v_val_6055_, 0);
if (lean_obj_tag(v_val_6056_) == 0)
{
goto v___jp_6050_;
}
else
{
lean_object* v_val_6057_; uint8_t v___x_6058_; 
v_val_6057_ = lean_ctor_get(v_val_6056_, 0);
v___x_6058_ = lean_unbox(v_val_6057_);
if (v___x_6058_ == 0)
{
goto v___jp_6050_;
}
else
{
goto v___jp_6038_;
}
}
}
}
}
}
v___jp_6021_:
{
lean_object* v___x_6023_; lean_object* v_items_6024_; 
lean_inc_ref(v_mkItem_5999_);
v___x_6023_ = lean_apply_3(v_mkItem_5999_, v_fst_6016_, v_snd_6017_, v___y_6022_);
v_items_6024_ = lean_array_push(v_b_6008_, v___x_6023_);
v_a_6010_ = v_items_6024_;
goto v___jp_6009_;
}
v___jp_6026_:
{
lean_object* v_toCommandContextInfo_6029_; lean_object* v_fileMap_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v_range_6034_; 
v_toCommandContextInfo_6029_ = lean_ctor_get(v_ctx_6001_, 0);
v_fileMap_6030_ = lean_ctor_get(v_toCommandContextInfo_6029_, 2);
lean_inc_ref_n(v_fileMap_6030_, 2);
v___x_6031_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6030_, v___y_6027_);
lean_dec(v___y_6027_);
v___x_6032_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6030_, v___y_6028_);
lean_dec(v___y_6028_);
if (v_isShared_6020_ == 0)
{
lean_ctor_set(v___x_6019_, 1, v___x_6032_);
lean_ctor_set(v___x_6019_, 0, v___x_6031_);
v_range_6034_ = v___x_6019_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6037_; 
v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6031_);
lean_ctor_set(v_reuseFailAlloc_6037_, 1, v___x_6032_);
v_range_6034_ = v_reuseFailAlloc_6037_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; 
lean_inc_ref(v_range_6034_);
v___x_6035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6025_);
lean_ctor_set(v___x_6035_, 1, v_range_6034_);
lean_ctor_set(v___x_6035_, 2, v_range_6034_);
v___x_6036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
v___y_6022_ = v___x_6036_;
goto v___jp_6021_;
}
}
v___jp_6038_:
{
uint8_t v___x_6039_; lean_object* v___x_6040_; 
v___x_6039_ = 0;
v___x_6040_ = l_Lean_Syntax_getRange_x3f(v_stx_6000_, v___x_6039_);
if (lean_obj_tag(v___x_6040_) == 1)
{
lean_object* v_val_6041_; 
v_val_6041_ = lean_ctor_get(v___x_6040_, 0);
lean_inc(v_val_6041_);
lean_dec_ref(v___x_6040_);
if (v_snd_6002_ == 0)
{
lean_object* v_start_6042_; lean_object* v_stop_6043_; 
v_start_6042_ = lean_ctor_get(v_val_6041_, 0);
lean_inc(v_start_6042_);
v_stop_6043_ = lean_ctor_get(v_val_6041_, 1);
lean_inc(v_stop_6043_);
lean_dec(v_val_6041_);
v___y_6027_ = v_start_6042_;
v___y_6028_ = v_stop_6043_;
goto v___jp_6026_;
}
else
{
lean_object* v_start_6044_; lean_object* v_stop_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v_start_6044_ = lean_ctor_get(v_val_6041_, 0);
lean_inc(v_start_6044_);
v_stop_6045_ = lean_ctor_get(v_val_6041_, 1);
lean_inc(v_stop_6045_);
lean_dec(v_val_6041_);
v___x_6046_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_6047_ = lean_nat_add(v_stop_6045_, v___x_6046_);
lean_dec(v_stop_6045_);
v___y_6027_ = v_start_6044_;
v___y_6028_ = v___x_6047_;
goto v___jp_6026_;
}
}
else
{
lean_object* v___x_6048_; 
lean_dec(v___x_6040_);
lean_dec_ref(v___x_6025_);
lean_del_object(v___x_6019_);
v___x_6048_ = lean_box(0);
v___y_6022_ = v___x_6048_;
goto v___jp_6021_;
}
}
v___jp_6050_:
{
if (v___x_6049_ == 0)
{
goto v___jp_6038_;
}
else
{
lean_object* v___x_6051_; 
lean_dec_ref(v___x_6025_);
lean_del_object(v___x_6019_);
v___x_6051_ = lean_box(0);
v___y_6022_ = v___x_6051_;
goto v___jp_6021_;
}
}
}
}
v___jp_6009_:
{
size_t v___x_6011_; size_t v___x_6012_; 
v___x_6011_ = ((size_t)1ULL);
v___x_6012_ = lean_usize_add(v_i_6007_, v___x_6011_);
v_i_6007_ = v___x_6012_;
v_b_6008_ = v_a_6010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_6060_, lean_object* v_stx_6061_, lean_object* v_ctx_6062_, lean_object* v_snd_6063_, lean_object* v_fst_6064_, lean_object* v_caps_6065_, lean_object* v_as_6066_, lean_object* v_sz_6067_, lean_object* v_i_6068_, lean_object* v_b_6069_){
_start:
{
uint8_t v_snd_1551__boxed_6070_; size_t v_sz_boxed_6071_; size_t v_i_boxed_6072_; lean_object* v_res_6073_; 
v_snd_1551__boxed_6070_ = lean_unbox(v_snd_6063_);
v_sz_boxed_6071_ = lean_unbox_usize(v_sz_6067_);
lean_dec(v_sz_6067_);
v_i_boxed_6072_ = lean_unbox_usize(v_i_6068_);
lean_dec(v_i_6068_);
v_res_6073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6060_, v_stx_6061_, v_ctx_6062_, v_snd_1551__boxed_6070_, v_fst_6064_, v_caps_6065_, v_as_6066_, v_sz_boxed_6071_, v_i_boxed_6072_, v_b_6069_);
lean_dec_ref(v_as_6066_);
lean_dec_ref(v_caps_6065_);
lean_dec_ref(v_fst_6064_);
lean_dec(v_stx_6061_);
return v_res_6073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_6074_, lean_object* v_stx_6075_, lean_object* v_caps_6076_, lean_object* v_ctx_6077_, lean_object* v_mkItem_6078_){
_start:
{
lean_object* v_fst_6080_; uint8_t v_snd_6081_; uint8_t v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = 0;
v___x_6087_ = l_Lean_Syntax_getSubstring_x3f(v_stx_6075_, v___x_6086_, v___x_6086_);
if (lean_obj_tag(v___x_6087_) == 0)
{
lean_object* v___x_6088_; 
v___x_6088_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_6080_ = v___x_6088_;
v_snd_6081_ = v___x_6086_;
goto v___jp_6079_;
}
else
{
lean_object* v_val_6089_; lean_object* v_str_6090_; lean_object* v_startPos_6091_; lean_object* v_stopPos_6092_; uint8_t v___y_6094_; uint8_t v___x_6096_; 
v_val_6089_ = lean_ctor_get(v___x_6087_, 0);
lean_inc(v_val_6089_);
lean_dec_ref(v___x_6087_);
v_str_6090_ = lean_ctor_get(v_val_6089_, 0);
lean_inc_ref(v_str_6090_);
v_startPos_6091_ = lean_ctor_get(v_val_6089_, 1);
lean_inc(v_startPos_6091_);
v_stopPos_6092_ = lean_ctor_get(v_val_6089_, 2);
lean_inc(v_stopPos_6092_);
lean_dec(v_val_6089_);
v___x_6096_ = lean_string_utf8_at_end(v_str_6090_, v_stopPos_6092_);
if (v___x_6096_ == 0)
{
uint32_t v___x_6097_; uint32_t v___x_6098_; uint8_t v___x_6099_; 
v___x_6097_ = lean_string_utf8_get(v_str_6090_, v_stopPos_6092_);
v___x_6098_ = 46;
v___x_6099_ = lean_uint32_dec_eq(v___x_6097_, v___x_6098_);
if (v___x_6099_ == 0)
{
v___y_6094_ = v___x_6099_;
goto v___jp_6093_;
}
else
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6100_ = lean_string_utf8_extract(v_str_6090_, v_startPos_6091_, v_stopPos_6092_);
lean_dec(v_stopPos_6092_);
lean_dec(v_startPos_6091_);
lean_dec_ref(v_str_6090_);
v___x_6101_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6102_ = lean_string_append(v___x_6100_, v___x_6101_);
v_fst_6080_ = v___x_6102_;
v_snd_6081_ = v___x_6099_;
goto v___jp_6079_;
}
}
else
{
v___y_6094_ = v___x_6086_;
goto v___jp_6093_;
}
v___jp_6093_:
{
lean_object* v___x_6095_; 
v___x_6095_ = lean_string_utf8_extract(v_str_6090_, v_startPos_6091_, v_stopPos_6092_);
lean_dec(v_stopPos_6092_);
lean_dec(v_startPos_6091_);
lean_dec_ref(v_str_6090_);
v_fst_6080_ = v___x_6095_;
v_snd_6081_ = v___y_6094_;
goto v___jp_6079_;
}
}
v___jp_6079_:
{
lean_object* v_items_6082_; size_t v_sz_6083_; size_t v___x_6084_; lean_object* v___x_6085_; 
v_items_6082_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_6083_ = lean_array_size(v_entries_6074_);
v___x_6084_ = ((size_t)0ULL);
v___x_6085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6078_, v_stx_6075_, v_ctx_6077_, v_snd_6081_, v_fst_6080_, v_caps_6076_, v_entries_6074_, v_sz_6083_, v___x_6084_, v_items_6082_);
lean_dec_ref(v_fst_6080_);
return v___x_6085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_6103_, lean_object* v_stx_6104_, lean_object* v_caps_6105_, lean_object* v_ctx_6106_, lean_object* v_mkItem_6107_){
_start:
{
lean_object* v_res_6108_; 
v_res_6108_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_6103_, v_stx_6104_, v_caps_6105_, v_ctx_6106_, v_mkItem_6107_);
lean_dec_ref(v_caps_6105_);
lean_dec(v_stx_6104_);
lean_dec_ref(v_entries_6103_);
return v_res_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_6109_, lean_object* v_caps_6110_, lean_object* v_ctx_6111_, lean_object* v___f_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v___x_6118_; lean_object* v_a_6119_; lean_object* v___x_6121_; uint8_t v_isShared_6122_; uint8_t v_isSharedCheck_6127_; 
v___x_6118_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6116_);
v_a_6119_ = lean_ctor_get(v___x_6118_, 0);
v_isSharedCheck_6127_ = !lean_is_exclusive(v___x_6118_);
if (v_isSharedCheck_6127_ == 0)
{
v___x_6121_ = v___x_6118_;
v_isShared_6122_ = v_isSharedCheck_6127_;
goto v_resetjp_6120_;
}
else
{
lean_inc(v_a_6119_);
lean_dec(v___x_6118_);
v___x_6121_ = lean_box(0);
v_isShared_6122_ = v_isSharedCheck_6127_;
goto v_resetjp_6120_;
}
v_resetjp_6120_:
{
lean_object* v___x_6123_; lean_object* v___x_6125_; 
v___x_6123_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_6119_, v_partialId_6109_, v_caps_6110_, v_ctx_6111_, v___f_6112_);
lean_dec(v_a_6119_);
if (v_isShared_6122_ == 0)
{
lean_ctor_set(v___x_6121_, 0, v___x_6123_);
v___x_6125_ = v___x_6121_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v___x_6123_);
v___x_6125_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
return v___x_6125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_6128_, lean_object* v_caps_6129_, lean_object* v_ctx_6130_, lean_object* v___f_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
lean_object* v_res_6137_; 
v_res_6137_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6128_, v_caps_6129_, v_ctx_6130_, v___f_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec_ref(v_caps_6129_);
lean_dec(v_partialId_6128_);
return v_res_6137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_6138_, lean_object* v_pos_6139_, lean_object* v_completionInfoPos_6140_, lean_object* v_ctx_6141_, lean_object* v_partialId_6142_, lean_object* v_caps_6143_){
_start:
{
lean_object* v___f_6145_; lean_object* v___f_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___f_6145_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6145_, 0, v_completionInfoPos_6140_);
lean_closure_set(v___f_6145_, 1, v_uri_6138_);
lean_closure_set(v___f_6145_, 2, v_pos_6139_);
lean_inc_ref(v_ctx_6141_);
v___f_6146_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_6146_, 0, v_partialId_6142_);
lean_closure_set(v___f_6146_, 1, v_caps_6143_);
lean_closure_set(v___f_6146_, 2, v_ctx_6141_);
lean_closure_set(v___f_6146_, 3, v___f_6145_);
v___x_6147_ = lean_unsigned_to_nat(32u);
v___x_6148_ = lean_mk_empty_array_with_capacity(v___x_6147_);
lean_dec_ref(v___x_6148_);
v___x_6149_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_6150_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6141_, v___x_6149_, v___f_6146_);
return v___x_6150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_6151_, lean_object* v_pos_6152_, lean_object* v_completionInfoPos_6153_, lean_object* v_ctx_6154_, lean_object* v_partialId_6155_, lean_object* v_caps_6156_, lean_object* v_a_6157_){
_start:
{
lean_object* v_res_6158_; 
v_res_6158_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6151_, v_pos_6152_, v_completionInfoPos_6153_, v_ctx_6154_, v_partialId_6155_, v_caps_6156_);
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_){
_start:
{
lean_object* v___x_6164_; 
v___x_6164_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6162_);
return v___x_6164_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
lean_object* v_res_6170_; 
v_res_6170_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6171_, lean_object* v_t_6172_){
_start:
{
lean_object* v___x_6173_; 
v___x_6173_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6171_, v_t_6172_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6174_, lean_object* v_t_6175_){
_start:
{
lean_object* v_res_6176_; 
v_res_6176_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6174_, v_t_6175_);
lean_dec(v_t_6175_);
return v_res_6176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6177_, lean_object* v_as_6178_, lean_object* v_lo_6179_, lean_object* v_hi_6180_, lean_object* v_w_6181_, lean_object* v_hlo_6182_, lean_object* v_hhi_6183_){
_start:
{
lean_object* v___x_6184_; 
v___x_6184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_as_6178_, v_lo_6179_, v_hi_6180_);
return v___x_6184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6185_, lean_object* v_as_6186_, lean_object* v_lo_6187_, lean_object* v_hi_6188_, lean_object* v_w_6189_, lean_object* v_hlo_6190_, lean_object* v_hhi_6191_){
_start:
{
lean_object* v_res_6192_; 
v_res_6192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6185_, v_as_6186_, v_lo_6187_, v_hi_6188_, v_w_6189_, v_hlo_6190_, v_hhi_6191_);
lean_dec(v_hi_6188_);
lean_dec(v_n_6185_);
return v_res_6192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6193_, lean_object* v_uri_6194_, lean_object* v_pos_6195_, size_t v_sz_6196_, size_t v_i_6197_, lean_object* v_bs_6198_){
_start:
{
uint8_t v___x_6199_; 
v___x_6199_ = lean_usize_dec_lt(v_i_6197_, v_sz_6196_);
if (v___x_6199_ == 0)
{
lean_dec_ref(v_pos_6195_);
lean_dec_ref(v_uri_6194_);
lean_dec(v_completionInfoPos_6193_);
return v_bs_6198_;
}
else
{
lean_object* v_v_6200_; lean_object* v_userName_6201_; lean_object* v_docString_6202_; lean_object* v___x_6203_; lean_object* v_bs_x27_6204_; lean_object* v___x_6205_; lean_object* v___y_6207_; 
v_v_6200_ = lean_array_uget_borrowed(v_bs_6198_, v_i_6197_);
v_userName_6201_ = lean_ctor_get(v_v_6200_, 1);
lean_inc_ref(v_userName_6201_);
v_docString_6202_ = lean_ctor_get(v_v_6200_, 3);
lean_inc(v_docString_6202_);
v___x_6203_ = lean_unsigned_to_nat(0u);
v_bs_x27_6204_ = lean_array_uset(v_bs_6198_, v_i_6197_, v___x_6203_);
v___x_6205_ = lean_box(0);
if (lean_obj_tag(v_docString_6202_) == 0)
{
v___y_6207_ = v___x_6205_;
goto v___jp_6206_;
}
else
{
lean_object* v_val_6217_; lean_object* v___x_6219_; uint8_t v_isShared_6220_; uint8_t v_isSharedCheck_6226_; 
v_val_6217_ = lean_ctor_get(v_docString_6202_, 0);
v_isSharedCheck_6226_ = !lean_is_exclusive(v_docString_6202_);
if (v_isSharedCheck_6226_ == 0)
{
v___x_6219_ = v_docString_6202_;
v_isShared_6220_ = v_isSharedCheck_6226_;
goto v_resetjp_6218_;
}
else
{
lean_inc(v_val_6217_);
lean_dec(v_docString_6202_);
v___x_6219_ = lean_box(0);
v_isShared_6220_ = v_isSharedCheck_6226_;
goto v_resetjp_6218_;
}
v_resetjp_6218_:
{
uint8_t v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6224_; 
v___x_6221_ = 1;
v___x_6222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6222_, 0, v_val_6217_);
lean_ctor_set_uint8(v___x_6222_, sizeof(void*)*1, v___x_6221_);
if (v_isShared_6220_ == 0)
{
lean_ctor_set(v___x_6219_, 0, v___x_6222_);
v___x_6224_ = v___x_6219_;
goto v_reusejp_6223_;
}
else
{
lean_object* v_reuseFailAlloc_6225_; 
v_reuseFailAlloc_6225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6225_, 0, v___x_6222_);
v___x_6224_ = v_reuseFailAlloc_6225_;
goto v_reusejp_6223_;
}
v_reusejp_6223_:
{
v___y_6207_ = v___x_6224_;
goto v___jp_6206_;
}
}
}
v___jp_6206_:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; size_t v___x_6213_; size_t v___x_6214_; lean_object* v___x_6215_; 
v___x_6208_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6193_);
v___x_6209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6209_, 0, v_completionInfoPos_6193_);
lean_inc_ref(v_pos_6195_);
lean_inc_ref(v_uri_6194_);
v___x_6210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6210_, 0, v_uri_6194_);
lean_ctor_set(v___x_6210_, 1, v_pos_6195_);
lean_ctor_set(v___x_6210_, 2, v___x_6209_);
lean_ctor_set(v___x_6210_, 3, v___x_6205_);
v___x_6211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
v___x_6212_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6212_, 0, v_userName_6201_);
lean_ctor_set(v___x_6212_, 1, v___x_6205_);
lean_ctor_set(v___x_6212_, 2, v___y_6207_);
lean_ctor_set(v___x_6212_, 3, v___x_6208_);
lean_ctor_set(v___x_6212_, 4, v___x_6205_);
lean_ctor_set(v___x_6212_, 5, v___x_6205_);
lean_ctor_set(v___x_6212_, 6, v___x_6211_);
lean_ctor_set(v___x_6212_, 7, v___x_6205_);
v___x_6213_ = ((size_t)1ULL);
v___x_6214_ = lean_usize_add(v_i_6197_, v___x_6213_);
v___x_6215_ = lean_array_uset(v_bs_x27_6204_, v_i_6197_, v___x_6212_);
v_i_6197_ = v___x_6214_;
v_bs_6198_ = v___x_6215_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6227_, lean_object* v_uri_6228_, lean_object* v_pos_6229_, lean_object* v_sz_6230_, lean_object* v_i_6231_, lean_object* v_bs_6232_){
_start:
{
size_t v_sz_boxed_6233_; size_t v_i_boxed_6234_; lean_object* v_res_6235_; 
v_sz_boxed_6233_ = lean_unbox_usize(v_sz_6230_);
lean_dec(v_sz_6230_);
v_i_boxed_6234_ = lean_unbox_usize(v_i_6231_);
lean_dec(v_i_6231_);
v_res_6235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6227_, v_uri_6228_, v_pos_6229_, v_sz_boxed_6233_, v_i_boxed_6234_, v_bs_6232_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6236_, lean_object* v_completionInfoPos_6237_, lean_object* v_uri_6238_, lean_object* v_pos_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_){
_start:
{
lean_object* v___x_6245_; 
v___x_6245_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6236_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_);
if (lean_obj_tag(v___x_6245_) == 0)
{
lean_object* v_a_6246_; lean_object* v___x_6248_; uint8_t v_isShared_6249_; uint8_t v_isSharedCheck_6256_; 
v_a_6246_ = lean_ctor_get(v___x_6245_, 0);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6245_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6248_ = v___x_6245_;
v_isShared_6249_ = v_isSharedCheck_6256_;
goto v_resetjp_6247_;
}
else
{
lean_inc(v_a_6246_);
lean_dec(v___x_6245_);
v___x_6248_ = lean_box(0);
v_isShared_6249_ = v_isSharedCheck_6256_;
goto v_resetjp_6247_;
}
v_resetjp_6247_:
{
size_t v_sz_6250_; size_t v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6254_; 
v_sz_6250_ = lean_array_size(v_a_6246_);
v___x_6251_ = ((size_t)0ULL);
v___x_6252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6237_, v_uri_6238_, v_pos_6239_, v_sz_6250_, v___x_6251_, v_a_6246_);
if (v_isShared_6249_ == 0)
{
lean_ctor_set(v___x_6248_, 0, v___x_6252_);
v___x_6254_ = v___x_6248_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v___x_6252_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
else
{
lean_object* v_a_6257_; lean_object* v___x_6259_; uint8_t v_isShared_6260_; uint8_t v_isSharedCheck_6264_; 
lean_dec_ref(v_pos_6239_);
lean_dec_ref(v_uri_6238_);
lean_dec(v_completionInfoPos_6237_);
v_a_6257_ = lean_ctor_get(v___x_6245_, 0);
v_isSharedCheck_6264_ = !lean_is_exclusive(v___x_6245_);
if (v_isSharedCheck_6264_ == 0)
{
v___x_6259_ = v___x_6245_;
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
else
{
lean_inc(v_a_6257_);
lean_dec(v___x_6245_);
v___x_6259_ = lean_box(0);
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
v_resetjp_6258_:
{
lean_object* v___x_6262_; 
if (v_isShared_6260_ == 0)
{
v___x_6262_ = v___x_6259_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6263_; 
v_reuseFailAlloc_6263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
v___x_6262_ = v_reuseFailAlloc_6263_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
return v___x_6262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6265_, lean_object* v_completionInfoPos_6266_, lean_object* v_uri_6267_, lean_object* v_pos_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
uint8_t v___x_495__boxed_6274_; lean_object* v_res_6275_; 
v___x_495__boxed_6274_ = lean_unbox(v___x_6265_);
v_res_6275_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_495__boxed_6274_, v_completionInfoPos_6266_, v_uri_6267_, v_pos_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
return v_res_6275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6276_, lean_object* v_pos_6277_, lean_object* v_completionInfoPos_6278_, lean_object* v_ctx_6279_){
_start:
{
lean_object* v___x_6281_; uint8_t v___x_6282_; lean_object* v___x_6283_; lean_object* v___f_6284_; lean_object* v___x_6285_; 
v___x_6281_ = l_Lean_LocalContext_empty;
v___x_6282_ = 0;
v___x_6283_ = lean_box(v___x_6282_);
v___f_6284_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6284_, 0, v___x_6283_);
lean_closure_set(v___f_6284_, 1, v_completionInfoPos_6278_);
lean_closure_set(v___f_6284_, 2, v_uri_6276_);
lean_closure_set(v___f_6284_, 3, v_pos_6277_);
v___x_6285_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6279_, v___x_6281_, v___f_6284_);
return v___x_6285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6286_, lean_object* v_pos_6287_, lean_object* v_completionInfoPos_6288_, lean_object* v_ctx_6289_, lean_object* v_a_6290_){
_start:
{
lean_object* v_res_6291_; 
v_res_6291_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6286_, v_pos_6287_, v_completionInfoPos_6288_, v_ctx_6289_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6292_, lean_object* v_b_6293_){
_start:
{
lean_object* v_array_6294_; lean_object* v_start_6295_; lean_object* v_stop_6296_; lean_object* v___x_6298_; uint8_t v_isShared_6299_; uint8_t v_isSharedCheck_6309_; 
v_array_6294_ = lean_ctor_get(v_a_6292_, 0);
v_start_6295_ = lean_ctor_get(v_a_6292_, 1);
v_stop_6296_ = lean_ctor_get(v_a_6292_, 2);
v_isSharedCheck_6309_ = !lean_is_exclusive(v_a_6292_);
if (v_isSharedCheck_6309_ == 0)
{
v___x_6298_ = v_a_6292_;
v_isShared_6299_ = v_isSharedCheck_6309_;
goto v_resetjp_6297_;
}
else
{
lean_inc(v_stop_6296_);
lean_inc(v_start_6295_);
lean_inc(v_array_6294_);
lean_dec(v_a_6292_);
v___x_6298_ = lean_box(0);
v_isShared_6299_ = v_isSharedCheck_6309_;
goto v_resetjp_6297_;
}
v_resetjp_6297_:
{
uint8_t v___x_6300_; 
v___x_6300_ = lean_nat_dec_lt(v_start_6295_, v_stop_6296_);
if (v___x_6300_ == 0)
{
lean_del_object(v___x_6298_);
lean_dec(v_stop_6296_);
lean_dec(v_start_6295_);
lean_dec_ref(v_array_6294_);
return v_b_6293_;
}
else
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6304_; 
v___x_6301_ = lean_unsigned_to_nat(1u);
v___x_6302_ = lean_nat_add(v_start_6295_, v___x_6301_);
lean_inc_ref(v_array_6294_);
if (v_isShared_6299_ == 0)
{
lean_ctor_set(v___x_6298_, 1, v___x_6302_);
v___x_6304_ = v___x_6298_;
goto v_reusejp_6303_;
}
else
{
lean_object* v_reuseFailAlloc_6308_; 
v_reuseFailAlloc_6308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6308_, 0, v_array_6294_);
lean_ctor_set(v_reuseFailAlloc_6308_, 1, v___x_6302_);
lean_ctor_set(v_reuseFailAlloc_6308_, 2, v_stop_6296_);
v___x_6304_ = v_reuseFailAlloc_6308_;
goto v_reusejp_6303_;
}
v_reusejp_6303_:
{
lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6305_ = lean_array_fget(v_array_6294_, v_start_6295_);
lean_dec(v_start_6295_);
lean_dec_ref(v_array_6294_);
v___x_6306_ = lean_array_push(v_b_6293_, v___x_6305_);
v_a_6292_ = v___x_6304_;
v_b_6293_ = v___x_6306_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6312_, lean_object* v_idx_6313_){
_start:
{
lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; 
v___x_6314_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6315_ = lean_array_get_size(v_scopeNames_6312_);
v___x_6316_ = l_Array_toSubarray___redArg(v_scopeNames_6312_, v_idx_6313_, v___x_6315_);
v___x_6317_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6318_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6316_, v___x_6317_);
v___x_6319_ = lean_array_to_list(v___x_6318_);
v___x_6320_ = l_String_intercalate(v___x_6314_, v___x_6319_);
return v___x_6320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6321_, lean_object* v_R_6322_, lean_object* v_a_6323_, lean_object* v_b_6324_){
_start:
{
lean_object* v___x_6325_; 
v___x_6325_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6323_, v_b_6324_);
return v___x_6325_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6326_, lean_object* v_next_6327_, lean_object* v_scopeNames_6328_, lean_object* v_idComponents_6329_, lean_object* v_a_6330_, uint8_t v_b_6331_){
_start:
{
uint8_t v___x_6332_; 
v___x_6332_ = lean_nat_dec_lt(v_a_6330_, v_upperBound_6326_);
if (v___x_6332_ == 0)
{
lean_dec(v_a_6330_);
return v_b_6331_;
}
else
{
uint8_t v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; uint8_t v___x_6336_; 
v___x_6333_ = 0;
v___x_6334_ = lean_nat_add(v_next_6327_, v_a_6330_);
v___x_6335_ = lean_array_get_size(v_scopeNames_6328_);
v___x_6336_ = lean_nat_dec_lt(v___x_6334_, v___x_6335_);
if (v___x_6336_ == 0)
{
lean_dec(v___x_6334_);
lean_dec(v_a_6330_);
return v___x_6333_;
}
else
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; uint8_t v___x_6340_; 
v___x_6337_ = lean_array_fget_borrowed(v_scopeNames_6328_, v___x_6334_);
lean_dec(v___x_6334_);
v___x_6338_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6339_ = lean_array_get_borrowed(v___x_6338_, v_idComponents_6329_, v_a_6330_);
v___x_6340_ = lean_string_dec_eq(v___x_6339_, v___x_6337_);
if (v___x_6340_ == 0)
{
lean_dec(v_a_6330_);
return v___x_6333_;
}
else
{
lean_object* v___x_6341_; lean_object* v___x_6342_; 
v___x_6341_ = lean_unsigned_to_nat(1u);
v___x_6342_ = lean_nat_add(v_a_6330_, v___x_6341_);
lean_dec(v_a_6330_);
v_a_6330_ = v___x_6342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6344_, lean_object* v_next_6345_, lean_object* v_scopeNames_6346_, lean_object* v_idComponents_6347_, lean_object* v_a_6348_, lean_object* v_b_6349_){
_start:
{
uint8_t v_b_boxed_6350_; uint8_t v_res_6351_; lean_object* v_r_6352_; 
v_b_boxed_6350_ = lean_unbox(v_b_6349_);
v_res_6351_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6344_, v_next_6345_, v_scopeNames_6346_, v_idComponents_6347_, v_a_6348_, v_b_boxed_6350_);
lean_dec_ref(v_idComponents_6347_);
lean_dec_ref(v_scopeNames_6346_);
lean_dec(v_next_6345_);
lean_dec(v_upperBound_6344_);
v_r_6352_ = lean_box(v_res_6351_);
return v_r_6352_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6353_, lean_object* v_idComponents_6354_, lean_object* v_scopeNames_6355_, lean_object* v_a_6356_, lean_object* v_b_6357_){
_start:
{
lean_object* v_a_6359_; uint8_t v___x_6363_; 
v___x_6363_ = lean_nat_dec_lt(v_a_6356_, v_upperBound_6353_);
if (v___x_6363_ == 0)
{
lean_dec(v_a_6356_);
lean_dec_ref(v_scopeNames_6355_);
return v_b_6357_;
}
else
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; uint8_t v___x_6367_; 
v___x_6364_ = lean_array_get_size(v_idComponents_6354_);
v___x_6365_ = lean_unsigned_to_nat(1u);
v___x_6366_ = lean_nat_sub(v___x_6364_, v___x_6365_);
v___x_6367_ = lean_nat_dec_lt(v___x_6366_, v___x_6364_);
if (v___x_6367_ == 0)
{
lean_object* v___x_6368_; lean_object* v___x_6369_; 
lean_dec(v___x_6366_);
lean_inc(v_a_6356_);
lean_inc_ref(v_scopeNames_6355_);
v___x_6368_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6355_, v_a_6356_);
v___x_6369_ = lean_array_push(v_b_6357_, v___x_6368_);
v_a_6359_ = v___x_6369_;
goto v___jp_6358_;
}
else
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; uint8_t v___x_6373_; 
v___x_6370_ = lean_nat_add(v_a_6356_, v___x_6364_);
v___x_6371_ = lean_nat_sub(v___x_6370_, v___x_6365_);
lean_dec(v___x_6370_);
v___x_6372_ = lean_array_get_size(v_scopeNames_6355_);
v___x_6373_ = lean_nat_dec_lt(v___x_6371_, v___x_6372_);
if (v___x_6373_ == 0)
{
lean_dec(v___x_6371_);
lean_dec(v___x_6366_);
v_a_6359_ = v_b_6357_;
goto v___jp_6358_;
}
else
{
lean_object* v___x_6374_; lean_object* v___x_6375_; uint8_t v___x_6376_; 
v___x_6374_ = lean_array_fget_borrowed(v_idComponents_6354_, v___x_6366_);
v___x_6375_ = lean_array_fget_borrowed(v_scopeNames_6355_, v___x_6371_);
v___x_6376_ = l_String_charactersIn(v___x_6374_, v___x_6375_);
if (v___x_6376_ == 0)
{
lean_dec(v___x_6371_);
lean_dec(v___x_6366_);
v_a_6359_ = v_b_6357_;
goto v___jp_6358_;
}
else
{
lean_object* v___x_6377_; uint8_t v___x_6378_; 
v___x_6377_ = lean_unsigned_to_nat(0u);
v___x_6378_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6366_, v_a_6356_, v_scopeNames_6355_, v_idComponents_6354_, v___x_6377_, v___x_6376_);
lean_dec(v___x_6366_);
if (v___x_6378_ == 0)
{
lean_dec(v___x_6371_);
v_a_6359_ = v_b_6357_;
goto v___jp_6358_;
}
else
{
lean_object* v___x_6379_; lean_object* v___x_6380_; 
lean_inc_ref(v_scopeNames_6355_);
v___x_6379_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6355_, v___x_6371_);
v___x_6380_ = lean_array_push(v_b_6357_, v___x_6379_);
v_a_6359_ = v___x_6380_;
goto v___jp_6358_;
}
}
}
}
}
v___jp_6358_:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6360_ = lean_unsigned_to_nat(1u);
v___x_6361_ = lean_nat_add(v_a_6356_, v___x_6360_);
lean_dec(v_a_6356_);
v_a_6356_ = v___x_6361_;
v_b_6357_ = v_a_6359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6381_, lean_object* v_idComponents_6382_, lean_object* v_scopeNames_6383_, lean_object* v_a_6384_, lean_object* v_b_6385_){
_start:
{
lean_object* v_res_6386_; 
v_res_6386_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6381_, v_idComponents_6382_, v_scopeNames_6383_, v_a_6384_, v_b_6385_);
lean_dec_ref(v_idComponents_6382_);
lean_dec(v_upperBound_6381_);
return v_res_6386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6387_, lean_object* v_scopeNames_6388_){
_start:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v_r_6391_; lean_object* v___x_6392_; 
v___x_6389_ = lean_unsigned_to_nat(0u);
v___x_6390_ = lean_array_get_size(v_scopeNames_6388_);
v_r_6391_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6390_, v_idComponents_6387_, v_scopeNames_6388_, v___x_6389_, v_r_6391_);
return v___x_6392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6393_, lean_object* v_scopeNames_6394_){
_start:
{
lean_object* v_res_6395_; 
v_res_6395_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6393_, v_scopeNames_6394_);
lean_dec_ref(v_idComponents_6393_);
return v_res_6395_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6396_, lean_object* v_next_6397_, lean_object* v_scopeNames_6398_, lean_object* v_idComponents_6399_, lean_object* v_inst_6400_, lean_object* v_R_6401_, lean_object* v_a_6402_, uint8_t v_b_6403_, lean_object* v_c_6404_){
_start:
{
uint8_t v___x_6405_; 
v___x_6405_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6396_, v_next_6397_, v_scopeNames_6398_, v_idComponents_6399_, v_a_6402_, v_b_6403_);
return v___x_6405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6406_, lean_object* v_next_6407_, lean_object* v_scopeNames_6408_, lean_object* v_idComponents_6409_, lean_object* v_inst_6410_, lean_object* v_R_6411_, lean_object* v_a_6412_, lean_object* v_b_6413_, lean_object* v_c_6414_){
_start:
{
uint8_t v_b_boxed_6415_; uint8_t v_res_6416_; lean_object* v_r_6417_; 
v_b_boxed_6415_ = lean_unbox(v_b_6413_);
v_res_6416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6406_, v_next_6407_, v_scopeNames_6408_, v_idComponents_6409_, v_inst_6410_, v_R_6411_, v_a_6412_, v_b_boxed_6415_, v_c_6414_);
lean_dec_ref(v_idComponents_6409_);
lean_dec_ref(v_scopeNames_6408_);
lean_dec(v_next_6407_);
lean_dec(v_upperBound_6406_);
v_r_6417_ = lean_box(v_res_6416_);
return v_r_6417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6418_, lean_object* v_idComponents_6419_, lean_object* v_scopeNames_6420_, lean_object* v_inst_6421_, lean_object* v_R_6422_, lean_object* v_a_6423_, lean_object* v_b_6424_, lean_object* v_c_6425_){
_start:
{
lean_object* v___x_6426_; 
v___x_6426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6418_, v_idComponents_6419_, v_scopeNames_6420_, v_a_6423_, v_b_6424_);
return v___x_6426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6427_, lean_object* v_idComponents_6428_, lean_object* v_scopeNames_6429_, lean_object* v_inst_6430_, lean_object* v_R_6431_, lean_object* v_a_6432_, lean_object* v_b_6433_, lean_object* v_c_6434_){
_start:
{
lean_object* v_res_6435_; 
v_res_6435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6427_, v_idComponents_6428_, v_scopeNames_6429_, v_inst_6430_, v_R_6431_, v_a_6432_, v_b_6433_, v_c_6434_);
lean_dec_ref(v_idComponents_6428_);
lean_dec(v_upperBound_6427_);
return v_res_6435_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6436_){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; uint8_t v___x_6439_; 
v___x_6437_ = lean_string_utf8_byte_size(v_x_6436_);
v___x_6438_ = lean_unsigned_to_nat(0u);
v___x_6439_ = lean_nat_dec_eq(v___x_6437_, v___x_6438_);
if (v___x_6439_ == 0)
{
uint8_t v___x_6440_; 
v___x_6440_ = 1;
return v___x_6440_;
}
else
{
uint8_t v___x_6441_; 
v___x_6441_ = 0;
return v___x_6441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6442_){
_start:
{
uint8_t v_res_6443_; lean_object* v_r_6444_; 
v_res_6443_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6442_);
lean_dec_ref(v_x_6442_);
v_r_6444_ = lean_box(v_res_6443_);
return v_r_6444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6445_, size_t v_i_6446_, lean_object* v_bs_6447_){
_start:
{
uint8_t v___x_6448_; 
v___x_6448_ = lean_usize_dec_lt(v_i_6446_, v_sz_6445_);
if (v___x_6448_ == 0)
{
return v_bs_6447_;
}
else
{
lean_object* v_v_6449_; lean_object* v___x_6450_; lean_object* v_bs_x27_6451_; lean_object* v___x_6452_; size_t v___x_6453_; size_t v___x_6454_; lean_object* v___x_6455_; 
v_v_6449_ = lean_array_uget(v_bs_6447_, v_i_6446_);
v___x_6450_ = lean_unsigned_to_nat(0u);
v_bs_x27_6451_ = lean_array_uset(v_bs_6447_, v_i_6446_, v___x_6450_);
v___x_6452_ = l_Lean_Name_toString(v_v_6449_, v___x_6448_);
v___x_6453_ = ((size_t)1ULL);
v___x_6454_ = lean_usize_add(v_i_6446_, v___x_6453_);
v___x_6455_ = lean_array_uset(v_bs_x27_6451_, v_i_6446_, v___x_6452_);
v_i_6446_ = v___x_6454_;
v_bs_6447_ = v___x_6455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6457_, lean_object* v_i_6458_, lean_object* v_bs_6459_){
_start:
{
size_t v_sz_boxed_6460_; size_t v_i_boxed_6461_; lean_object* v_res_6462_; 
v_sz_boxed_6460_ = lean_unbox_usize(v_sz_6457_);
lean_dec(v_sz_6457_);
v_i_boxed_6461_ = lean_unbox_usize(v_i_6458_);
lean_dec(v_i_6458_);
v_res_6462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6460_, v_i_boxed_6461_, v_bs_6459_);
return v_res_6462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6463_, lean_object* v_uri_6464_, lean_object* v_pos_6465_, size_t v_sz_6466_, size_t v_i_6467_, lean_object* v_bs_6468_){
_start:
{
uint8_t v___x_6469_; 
v___x_6469_ = lean_usize_dec_lt(v_i_6467_, v_sz_6466_);
if (v___x_6469_ == 0)
{
lean_dec_ref(v_pos_6465_);
lean_dec_ref(v_uri_6464_);
lean_dec(v_completionInfoPos_6463_);
return v_bs_6468_;
}
else
{
lean_object* v_v_6470_; lean_object* v___x_6471_; lean_object* v_bs_x27_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; size_t v___x_6479_; size_t v___x_6480_; lean_object* v___x_6481_; 
v_v_6470_ = lean_array_uget(v_bs_6468_, v_i_6467_);
v___x_6471_ = lean_unsigned_to_nat(0u);
v_bs_x27_6472_ = lean_array_uset(v_bs_6468_, v_i_6467_, v___x_6471_);
v___x_6473_ = lean_box(0);
v___x_6474_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6463_);
v___x_6475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6475_, 0, v_completionInfoPos_6463_);
lean_inc_ref(v_pos_6465_);
lean_inc_ref(v_uri_6464_);
v___x_6476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6476_, 0, v_uri_6464_);
lean_ctor_set(v___x_6476_, 1, v_pos_6465_);
lean_ctor_set(v___x_6476_, 2, v___x_6475_);
lean_ctor_set(v___x_6476_, 3, v___x_6473_);
v___x_6477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6477_, 0, v___x_6476_);
v___x_6478_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6478_, 0, v_v_6470_);
lean_ctor_set(v___x_6478_, 1, v___x_6473_);
lean_ctor_set(v___x_6478_, 2, v___x_6473_);
lean_ctor_set(v___x_6478_, 3, v___x_6474_);
lean_ctor_set(v___x_6478_, 4, v___x_6473_);
lean_ctor_set(v___x_6478_, 5, v___x_6473_);
lean_ctor_set(v___x_6478_, 6, v___x_6477_);
lean_ctor_set(v___x_6478_, 7, v___x_6473_);
v___x_6479_ = ((size_t)1ULL);
v___x_6480_ = lean_usize_add(v_i_6467_, v___x_6479_);
v___x_6481_ = lean_array_uset(v_bs_x27_6472_, v_i_6467_, v___x_6478_);
v_i_6467_ = v___x_6480_;
v_bs_6468_ = v___x_6481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6483_, lean_object* v_uri_6484_, lean_object* v_pos_6485_, lean_object* v_sz_6486_, lean_object* v_i_6487_, lean_object* v_bs_6488_){
_start:
{
size_t v_sz_boxed_6489_; size_t v_i_boxed_6490_; lean_object* v_res_6491_; 
v_sz_boxed_6489_ = lean_unbox_usize(v_sz_6486_);
lean_dec(v_sz_6486_);
v_i_boxed_6490_ = lean_unbox_usize(v_i_6487_);
lean_dec(v_i_6487_);
v_res_6491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6483_, v_uri_6484_, v_pos_6485_, v_sz_boxed_6489_, v_i_boxed_6490_, v_bs_6488_);
return v_res_6491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6493_, lean_object* v_pos_6494_, lean_object* v_completionInfoPos_6495_, lean_object* v_id_x3f_6496_, uint8_t v_danglingDot_6497_, lean_object* v_scopeNames_6498_){
_start:
{
lean_object* v___f_6500_; lean_object* v_idComponents_6502_; lean_object* v___y_6513_; 
v___f_6500_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6496_) == 0)
{
lean_object* v___x_6516_; 
v___x_6516_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6513_ = v___x_6516_;
goto v___jp_6512_;
}
else
{
lean_object* v_val_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; size_t v_sz_6520_; size_t v___x_6521_; lean_object* v___x_6522_; 
v_val_6517_ = lean_ctor_get(v_id_x3f_6496_, 0);
lean_inc(v_val_6517_);
lean_dec_ref(v_id_x3f_6496_);
v___x_6518_ = l_Lean_Name_components(v_val_6517_);
v___x_6519_ = lean_array_mk(v___x_6518_);
v_sz_6520_ = lean_array_size(v___x_6519_);
v___x_6521_ = ((size_t)0ULL);
v___x_6522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6520_, v___x_6521_, v___x_6519_);
v___y_6513_ = v___x_6522_;
goto v___jp_6512_;
}
v___jp_6501_:
{
lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v_scopeNames_6506_; lean_object* v_candidates_6507_; size_t v_sz_6508_; size_t v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; 
v___x_6503_ = lean_array_mk(v_scopeNames_6498_);
v___x_6504_ = lean_array_pop(v___x_6503_);
v___x_6505_ = l_Array_takeWhile___redArg(v___f_6500_, v___x_6504_);
lean_dec_ref(v___x_6504_);
v_scopeNames_6506_ = l_Array_reverse___redArg(v___x_6505_);
v_candidates_6507_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6502_, v_scopeNames_6506_);
lean_dec_ref(v_idComponents_6502_);
v_sz_6508_ = lean_array_size(v_candidates_6507_);
v___x_6509_ = ((size_t)0ULL);
v___x_6510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6495_, v_uri_6493_, v_pos_6494_, v_sz_6508_, v___x_6509_, v_candidates_6507_);
v___x_6511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6511_, 0, v___x_6510_);
return v___x_6511_;
}
v___jp_6512_:
{
if (v_danglingDot_6497_ == 0)
{
v_idComponents_6502_ = v___y_6513_;
goto v___jp_6501_;
}
else
{
lean_object* v___x_6514_; lean_object* v_idComponents_6515_; 
v___x_6514_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6515_ = lean_array_push(v___y_6513_, v___x_6514_);
v_idComponents_6502_ = v_idComponents_6515_;
goto v___jp_6501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6523_, lean_object* v_pos_6524_, lean_object* v_completionInfoPos_6525_, lean_object* v_id_x3f_6526_, lean_object* v_danglingDot_6527_, lean_object* v_scopeNames_6528_, lean_object* v_a_6529_){
_start:
{
uint8_t v_danglingDot_boxed_6530_; lean_object* v_res_6531_; 
v_danglingDot_boxed_6530_ = lean_unbox(v_danglingDot_6527_);
v_res_6531_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6523_, v_pos_6524_, v_completionInfoPos_6525_, v_id_x3f_6526_, v_danglingDot_boxed_6530_, v_scopeNames_6528_);
return v_res_6531_;
}
}
lean_object* runtime_initialize_Lean_Data_FuzzyMatching(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_EligibleHeaderDecls(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_FuzzyMatching(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_EligibleHeaderDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_FuzzyMatching(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_EligibleHeaderDecls(uint8_t builtin);
lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_FuzzyMatching(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_EligibleHeaderDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionCollectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion_CompletionCollectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion_CompletionCollectors(builtin);
}
#ifdef __cplusplus
}
#endif
