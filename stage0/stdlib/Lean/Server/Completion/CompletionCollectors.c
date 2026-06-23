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
uint8_t lean_string_compare(lean_object*, lean_object*);
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
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_131_, 1);
lean_inc(v_declName_115_);
v___x_133_ = l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(v_declName_115_, v_a_121_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
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
lean_dec_ref_known(v_a_347_, 1);
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
lean_dec_ref_known(v___x_448_, 2);
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
lean_dec_ref_known(v___x_448_, 2);
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
lean_dec_ref_known(v___x_448_, 2);
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
lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_450__overap_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
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
v___x_450__overap_660_ = l_Lean_Server_Completion_forEligibleDeclsM___redArg(v___x_644_, v___x_654_, v___f_657_, v___f_656_);
v___x_661_ = lean_apply_1(v___x_450__overap_660_, v___x_659_);
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
lean_dec_ref_known(v_id_703_, 2);
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
lean_dec_ref_known(v_id_703_, 2);
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
lean_dec_ref_known(v_id_703_, 2);
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
lean_dec_ref_known(v_a_747_, 1);
lean_dec(v_pre_745_);
lean_dec_ref(v_matchUsingNamespace_734_);
return v___x_746_;
}
else
{
lean_object* v_a_748_; lean_object* v_snd_749_; 
lean_dec_ref_known(v___x_746_, 1);
v_a_748_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v_a_747_, 1);
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
lean_dec_ref_known(v_a_781_, 1);
v___y_788_ = v___y_771_;
goto v___jp_787_;
}
else
{
lean_dec_ref_known(v___y_771_, 1);
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
lean_dec_ref_known(v_a_847_, 1);
v_as_x27_832_ = v_tail_841_;
v_b_833_ = v___x_842_;
goto _start;
}
else
{
lean_dec_ref_known(v___y_834_, 1);
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
lean_dec_ref_known(v_a_892_, 1);
v___x_897_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_867_, v_id_868_, v_danglingDot_869_, v_tail_886_, v___x_887_, v___y_873_, v___y_880_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; 
lean_dec_ref_known(v___y_873_, 1);
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
lean_dec_ref_known(v_a_976_, 1);
lean_dec(v_openDecls_971_);
lean_dec(v_id_921_);
lean_dec(v_declName_920_);
v___y_932_ = v___x_975_;
goto v___jp_931_;
}
else
{
lean_object* v_a_977_; lean_object* v_snd_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref_known(v___x_975_, 1);
v_a_977_ = lean_ctor_get(v_a_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v_a_976_, 1);
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
lean_dec_ref_known(v___x_980_, 1);
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
lean_dec_ref_known(v_val_1164_, 3);
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
lean_dec_ref_known(v_a_1074_, 1);
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
lean_dec_ref_known(v___x_1212_, 2);
v_it_1123_ = v_z_1211_;
v_fst_1124_ = v_key_1213_;
goto v___jp_1122_;
}
case 1:
{
lean_object* v_node_1214_; lean_object* v___x_1215_; 
v_node_1214_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_node_1214_);
lean_dec_ref_known(v___x_1212_, 1);
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
lean_dec_ref_known(v___x_1097_, 1);
if (lean_obj_tag(v_a_1098_) == 0)
{
lean_object* v_a_1099_; 
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v_a_1099_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v_a_1098_, 1);
v_a_1089_ = v_a_1099_;
goto v___jp_1088_;
}
else
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v_a_1098_, 1);
if (lean_obj_tag(v_a_1100_) == 1)
{
lean_object* v_val_1101_; lean_object* v___x_1102_; 
v_val_1101_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v_a_1100_, 1);
v___x_1102_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_val_1101_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
if (lean_obj_tag(v_a_1103_) == 0)
{
lean_object* v_a_1104_; 
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v_a_1104_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v_a_1103_, 1);
v_a_1089_ = v_a_1104_;
goto v___jp_1088_;
}
else
{
lean_dec_ref_known(v_a_1103_, 1);
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
lean_dec_ref_known(v_a_1269_, 1);
return v___x_1268_;
}
else
{
lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v_a_1269_, 1);
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
lean_dec_ref_known(v_n_u2081_1339_, 2);
v_pre_1345_ = lean_ctor_get(v_n_u2082_1340_, 0);
lean_inc(v_pre_1345_);
v_str_1346_ = lean_ctor_get(v_n_u2082_1340_, 1);
lean_inc_ref(v_str_1346_);
lean_dec_ref_known(v_n_u2082_1340_, 2);
v___x_1347_ = lean_string_compare(v_str_1344_, v_str_1346_);
lean_dec_ref(v_str_1346_);
lean_dec_ref(v_str_1344_);
if (v___x_1347_ == 1)
{
v_n_u2081_1337_ = v_pre_1343_;
v_n_u2082_1338_ = v_pre_1345_;
goto _start;
}
else
{
lean_dec(v_pre_1345_);
lean_dec(v_pre_1343_);
return v___x_1347_;
}
}
else
{
uint8_t v___x_1349_; 
lean_dec_ref_known(v_n_u2081_1339_, 2);
lean_dec(v_n_u2082_1340_);
v___x_1349_ = 2;
return v___x_1349_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1340_))
{
case 0:
{
uint8_t v___x_1350_; 
lean_dec_ref_known(v_n_u2081_1339_, 2);
v___x_1350_ = 2;
return v___x_1350_;
}
case 1:
{
uint8_t v___x_1351_; 
lean_dec_ref_known(v_n_u2082_1340_, 2);
lean_dec_ref_known(v_n_u2081_1339_, 2);
v___x_1351_ = 0;
return v___x_1351_;
}
default: 
{
lean_object* v_pre_1352_; lean_object* v_i_1353_; lean_object* v_pre_1354_; lean_object* v_i_1355_; uint8_t v___x_1356_; 
v_pre_1352_ = lean_ctor_get(v_n_u2081_1339_, 0);
lean_inc(v_pre_1352_);
v_i_1353_ = lean_ctor_get(v_n_u2081_1339_, 1);
lean_inc(v_i_1353_);
lean_dec_ref_known(v_n_u2081_1339_, 2);
v_pre_1354_ = lean_ctor_get(v_n_u2082_1340_, 0);
lean_inc(v_pre_1354_);
v_i_1355_ = lean_ctor_get(v_n_u2082_1340_, 1);
lean_inc(v_i_1355_);
lean_dec_ref_known(v_n_u2082_1340_, 2);
v___x_1356_ = lean_nat_dec_lt(v_i_1353_, v_i_1355_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_nat_dec_eq(v_i_1353_, v_i_1355_);
lean_dec(v_i_1355_);
lean_dec(v_i_1353_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; 
lean_dec(v_pre_1354_);
lean_dec(v_pre_1352_);
v___x_1358_ = 2;
return v___x_1358_;
}
else
{
v_n_u2081_1337_ = v_pre_1352_;
v_n_u2082_1338_ = v_pre_1354_;
goto _start;
}
}
else
{
uint8_t v___x_1360_; 
lean_dec(v_i_1355_);
lean_dec(v_pre_1354_);
lean_dec(v_i_1353_);
lean_dec(v_pre_1352_);
v___x_1360_ = 0;
return v___x_1360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1361_, lean_object* v_n_u2082_1362_){
_start:
{
uint8_t v_res_1363_; lean_object* v_r_1364_; 
v_res_1363_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1361_, v_n_u2082_1362_);
v_r_1364_ = lean_box(v_res_1363_);
return v_r_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1368_ = l_Std_TreeSet_ofArray___redArg(v_names_1366_, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1369_);
lean_dec_ref(v_names_1369_);
return v_res_1370_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1371_, lean_object* v_t_1372_){
_start:
{
if (lean_obj_tag(v_t_1372_) == 0)
{
lean_object* v_k_1373_; lean_object* v_l_1374_; lean_object* v_r_1375_; uint8_t v___x_1376_; 
v_k_1373_ = lean_ctor_get(v_t_1372_, 1);
lean_inc(v_k_1373_);
v_l_1374_ = lean_ctor_get(v_t_1372_, 3);
lean_inc(v_l_1374_);
v_r_1375_ = lean_ctor_get(v_t_1372_, 4);
lean_inc(v_r_1375_);
lean_dec_ref_known(v_t_1372_, 5);
lean_inc(v_k_1371_);
v___x_1376_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1371_, v_k_1373_);
switch(v___x_1376_)
{
case 0:
{
lean_dec(v_r_1375_);
v_t_1372_ = v_l_1374_;
goto _start;
}
case 1:
{
uint8_t v___x_1378_; 
lean_dec(v_r_1375_);
lean_dec(v_l_1374_);
lean_dec(v_k_1371_);
v___x_1378_ = 1;
return v___x_1378_;
}
default: 
{
lean_dec(v_l_1374_);
v_t_1372_ = v_r_1375_;
goto _start;
}
}
}
else
{
uint8_t v___x_1380_; 
lean_dec(v_k_1371_);
v___x_1380_ = 0;
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1381_, lean_object* v_t_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1381_, v_t_1382_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1385_, lean_object* v_v_1386_, lean_object* v_t_1387_){
_start:
{
if (lean_obj_tag(v_t_1387_) == 0)
{
lean_object* v_size_1388_; lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v_l_1391_; lean_object* v_r_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1672_; 
v_size_1388_ = lean_ctor_get(v_t_1387_, 0);
v_k_1389_ = lean_ctor_get(v_t_1387_, 1);
v_v_1390_ = lean_ctor_get(v_t_1387_, 2);
v_l_1391_ = lean_ctor_get(v_t_1387_, 3);
v_r_1392_ = lean_ctor_get(v_t_1387_, 4);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_t_1387_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1394_ = v_t_1387_;
v_isShared_1395_ = v_isSharedCheck_1672_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_r_1392_);
lean_inc(v_l_1391_);
lean_inc(v_v_1390_);
lean_inc(v_k_1389_);
lean_inc(v_size_1388_);
lean_dec(v_t_1387_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1672_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
uint8_t v___x_1396_; 
lean_inc(v_k_1389_);
lean_inc(v_k_1385_);
v___x_1396_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1385_, v_k_1389_);
switch(v___x_1396_)
{
case 0:
{
lean_object* v_impl_1397_; lean_object* v___x_1398_; 
lean_dec(v_size_1388_);
v_impl_1397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1385_, v_v_1386_, v_l_1391_);
v___x_1398_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1392_) == 0)
{
lean_object* v_size_1399_; lean_object* v_size_1400_; lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v_l_1403_; lean_object* v_r_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_size_1399_ = lean_ctor_get(v_r_1392_, 0);
v_size_1400_ = lean_ctor_get(v_impl_1397_, 0);
lean_inc(v_size_1400_);
v_k_1401_ = lean_ctor_get(v_impl_1397_, 1);
lean_inc(v_k_1401_);
v_v_1402_ = lean_ctor_get(v_impl_1397_, 2);
lean_inc(v_v_1402_);
v_l_1403_ = lean_ctor_get(v_impl_1397_, 3);
lean_inc(v_l_1403_);
v_r_1404_ = lean_ctor_get(v_impl_1397_, 4);
lean_inc(v_r_1404_);
v___x_1405_ = lean_unsigned_to_nat(3u);
v___x_1406_ = lean_nat_mul(v___x_1405_, v_size_1399_);
v___x_1407_ = lean_nat_dec_lt(v___x_1406_, v_size_1400_);
lean_dec(v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_dec(v_r_1404_);
lean_dec(v_l_1403_);
lean_dec(v_v_1402_);
lean_dec(v_k_1401_);
v___x_1408_ = lean_nat_add(v___x_1398_, v_size_1400_);
lean_dec(v_size_1400_);
v___x_1409_ = lean_nat_add(v___x_1408_, v_size_1399_);
lean_dec(v___x_1408_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 3, v_impl_1397_);
lean_ctor_set(v___x_1394_, 0, v___x_1409_);
v___x_1411_ = v___x_1394_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_impl_1397_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_r_1392_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
else
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1478_; 
v_isSharedCheck_1478_ = !lean_is_exclusive(v_impl_1397_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; 
v_unused_1479_ = lean_ctor_get(v_impl_1397_, 4);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_impl_1397_, 3);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_impl_1397_, 2);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_impl_1397_, 1);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_impl_1397_, 0);
lean_dec(v_unused_1483_);
v___x_1414_ = v_impl_1397_;
v_isShared_1415_ = v_isSharedCheck_1478_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_impl_1397_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1478_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_size_1416_; lean_object* v_size_1417_; lean_object* v_k_1418_; lean_object* v_v_1419_; lean_object* v_l_1420_; lean_object* v_r_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_size_1416_ = lean_ctor_get(v_l_1403_, 0);
v_size_1417_ = lean_ctor_get(v_r_1404_, 0);
v_k_1418_ = lean_ctor_get(v_r_1404_, 1);
v_v_1419_ = lean_ctor_get(v_r_1404_, 2);
v_l_1420_ = lean_ctor_get(v_r_1404_, 3);
v_r_1421_ = lean_ctor_get(v_r_1404_, 4);
v___x_1422_ = lean_unsigned_to_nat(2u);
v___x_1423_ = lean_nat_mul(v___x_1422_, v_size_1416_);
v___x_1424_ = lean_nat_dec_lt(v_size_1417_, v___x_1423_);
lean_dec(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1453_; 
lean_inc(v_r_1421_);
lean_inc(v_l_1420_);
lean_inc(v_v_1419_);
lean_inc(v_k_1418_);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_r_1404_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1454_ = lean_ctor_get(v_r_1404_, 4);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_r_1404_, 3);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1404_, 2);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_r_1404_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_r_1404_, 0);
lean_dec(v_unused_1458_);
v___x_1426_ = v_r_1404_;
v_isShared_1427_ = v_isSharedCheck_1453_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v_r_1404_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1453_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___x_1441_; lean_object* v___y_1443_; 
v___x_1428_ = lean_nat_add(v___x_1398_, v_size_1400_);
lean_dec(v_size_1400_);
v___x_1429_ = lean_nat_add(v___x_1428_, v_size_1399_);
lean_dec(v___x_1428_);
v___x_1441_ = lean_nat_add(v___x_1398_, v_size_1416_);
if (lean_obj_tag(v_l_1420_) == 0)
{
lean_object* v_size_1451_; 
v_size_1451_ = lean_ctor_get(v_l_1420_, 0);
lean_inc(v_size_1451_);
v___y_1443_ = v_size_1451_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___y_1443_ = v___x_1452_;
goto v___jp_1442_;
}
v___jp_1430_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_nat_add(v___y_1431_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec(v___y_1431_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 4, v_r_1392_);
lean_ctor_set(v___x_1426_, 3, v_r_1421_);
lean_ctor_set(v___x_1426_, 2, v_v_1390_);
lean_ctor_set(v___x_1426_, 1, v_k_1389_);
lean_ctor_set(v___x_1426_, 0, v___x_1434_);
v___x_1436_ = v___x_1426_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_r_1421_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_r_1392_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v___x_1436_);
lean_ctor_set(v___x_1414_, 3, v___y_1432_);
lean_ctor_set(v___x_1414_, 2, v_v_1419_);
lean_ctor_set(v___x_1414_, 1, v_k_1418_);
lean_ctor_set(v___x_1414_, 0, v___x_1429_);
v___x_1438_ = v___x_1414_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v___y_1432_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_nat_add(v___x_1441_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec(v___x_1441_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_l_1420_);
lean_ctor_set(v___x_1394_, 3, v_l_1403_);
lean_ctor_set(v___x_1394_, 2, v_v_1402_);
lean_ctor_set(v___x_1394_, 1, v_k_1401_);
lean_ctor_set(v___x_1394_, 0, v___x_1444_);
v___x_1446_ = v___x_1394_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1401_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1402_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_l_1403_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_l_1420_);
v___x_1446_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_nat_add(v___x_1398_, v_size_1399_);
if (lean_obj_tag(v_r_1421_) == 0)
{
lean_object* v_size_1448_; 
v_size_1448_ = lean_ctor_get(v_r_1421_, 0);
lean_inc(v_size_1448_);
v___y_1431_ = v___x_1447_;
v___y_1432_ = v___x_1446_;
v___y_1433_ = v_size_1448_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___y_1431_ = v___x_1447_;
v___y_1432_ = v___x_1446_;
v___y_1433_ = v___x_1449_;
goto v___jp_1430_;
}
}
}
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_del_object(v___x_1394_);
v___x_1459_ = lean_nat_add(v___x_1398_, v_size_1400_);
lean_dec(v_size_1400_);
v___x_1460_ = lean_nat_add(v___x_1459_, v_size_1399_);
lean_dec(v___x_1459_);
v___x_1461_ = lean_nat_add(v___x_1398_, v_size_1399_);
v___x_1462_ = lean_nat_add(v___x_1461_, v_size_1417_);
lean_dec(v___x_1461_);
lean_inc_ref(v_r_1392_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v_r_1392_);
lean_ctor_set(v___x_1414_, 3, v_r_1404_);
lean_ctor_set(v___x_1414_, 2, v_v_1390_);
lean_ctor_set(v___x_1414_, 1, v_k_1389_);
lean_ctor_set(v___x_1414_, 0, v___x_1462_);
v___x_1464_ = v___x_1414_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_r_1404_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1392_);
v___x_1464_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_isSharedCheck_1471_ = !lean_is_exclusive(v_r_1392_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; 
v_unused_1472_ = lean_ctor_get(v_r_1392_, 4);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_r_1392_, 3);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_r_1392_, 2);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_r_1392_, 1);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_r_1392_, 0);
lean_dec(v_unused_1476_);
v___x_1466_ = v_r_1392_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_r_1392_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 4, v___x_1464_);
lean_ctor_set(v___x_1466_, 3, v_l_1403_);
lean_ctor_set(v___x_1466_, 2, v_v_1402_);
lean_ctor_set(v___x_1466_, 1, v_k_1401_);
lean_ctor_set(v___x_1466_, 0, v___x_1460_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1401_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1402_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_l_1403_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v___x_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1484_; 
v_l_1484_ = lean_ctor_get(v_impl_1397_, 3);
lean_inc(v_l_1484_);
if (lean_obj_tag(v_l_1484_) == 0)
{
lean_object* v_r_1485_; lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1498_; 
v_r_1485_ = lean_ctor_get(v_impl_1397_, 4);
v_k_1486_ = lean_ctor_get(v_impl_1397_, 1);
v_v_1487_ = lean_ctor_get(v_impl_1397_, 2);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_impl_1397_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; lean_object* v_unused_1500_; 
v_unused_1499_ = lean_ctor_get(v_impl_1397_, 3);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_impl_1397_, 0);
lean_dec(v_unused_1500_);
v___x_1489_ = v_impl_1397_;
v_isShared_1490_ = v_isSharedCheck_1498_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_r_1485_);
lean_inc(v_v_1487_);
lean_inc(v_k_1486_);
lean_dec(v_impl_1397_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1498_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1485_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 3, v_r_1485_);
lean_ctor_set(v___x_1489_, 2, v_v_1390_);
lean_ctor_set(v___x_1489_, 1, v_k_1389_);
lean_ctor_set(v___x_1489_, 0, v___x_1398_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_r_1485_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1485_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v___x_1493_);
lean_ctor_set(v___x_1394_, 3, v_l_1484_);
lean_ctor_set(v___x_1394_, 2, v_v_1487_);
lean_ctor_set(v___x_1394_, 1, v_k_1486_);
lean_ctor_set(v___x_1394_, 0, v___x_1491_);
v___x_1495_ = v___x_1394_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_k_1486_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_v_1487_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v_l_1484_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v___x_1493_);
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
else
{
lean_object* v_r_1501_; 
v_r_1501_ = lean_ctor_get(v_impl_1397_, 4);
lean_inc(v_r_1501_);
if (lean_obj_tag(v_r_1501_) == 0)
{
lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1526_; 
v_k_1502_ = lean_ctor_get(v_impl_1397_, 1);
v_v_1503_ = lean_ctor_get(v_impl_1397_, 2);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_impl_1397_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; 
v_unused_1527_ = lean_ctor_get(v_impl_1397_, 4);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_impl_1397_, 3);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_impl_1397_, 0);
lean_dec(v_unused_1529_);
v___x_1505_ = v_impl_1397_;
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_v_1503_);
lean_inc(v_k_1502_);
lean_dec(v_impl_1397_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1522_; 
v_k_1507_ = lean_ctor_get(v_r_1501_, 1);
v_v_1508_ = lean_ctor_get(v_r_1501_, 2);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_r_1501_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; 
v_unused_1523_ = lean_ctor_get(v_r_1501_, 4);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_r_1501_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_r_1501_, 0);
lean_dec(v_unused_1525_);
v___x_1510_ = v_r_1501_;
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_v_1508_);
lean_inc(v_k_1507_);
lean_dec(v_r_1501_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(3u);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_l_1484_);
lean_ctor_set(v___x_1510_, 3, v_l_1484_);
lean_ctor_set(v___x_1510_, 2, v_v_1503_);
lean_ctor_set(v___x_1510_, 1, v_k_1502_);
lean_ctor_set(v___x_1510_, 0, v___x_1398_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1502_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1503_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_l_1484_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_l_1484_);
v___x_1514_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_l_1484_);
lean_ctor_set(v___x_1505_, 2, v_v_1390_);
lean_ctor_set(v___x_1505_, 1, v_k_1389_);
lean_ctor_set(v___x_1505_, 0, v___x_1398_);
v___x_1516_ = v___x_1505_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_l_1484_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_l_1484_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v___x_1516_);
lean_ctor_set(v___x_1394_, 3, v___x_1514_);
lean_ctor_set(v___x_1394_, 2, v_v_1508_);
lean_ctor_set(v___x_1394_, 1, v_k_1507_);
lean_ctor_set(v___x_1394_, 0, v___x_1512_);
v___x_1518_ = v___x_1394_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1508_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = lean_unsigned_to_nat(2u);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_r_1501_);
lean_ctor_set(v___x_1394_, 3, v_impl_1397_);
lean_ctor_set(v___x_1394_, 0, v___x_1530_);
v___x_1532_ = v___x_1394_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_impl_1397_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_r_1501_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1535_; 
lean_dec(v_v_1390_);
lean_dec(v_k_1389_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 2, v_v_1386_);
lean_ctor_set(v___x_1394_, 1, v_k_1385_);
v___x_1535_ = v___x_1394_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_size_1388_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1385_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1386_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_l_1391_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_r_1392_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
default: 
{
lean_object* v_impl_1537_; lean_object* v___x_1538_; 
lean_dec(v_size_1388_);
v_impl_1537_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1385_, v_v_1386_, v_r_1392_);
v___x_1538_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1391_) == 0)
{
lean_object* v_size_1539_; lean_object* v_size_1540_; lean_object* v_k_1541_; lean_object* v_v_1542_; lean_object* v_l_1543_; lean_object* v_r_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_size_1539_ = lean_ctor_get(v_l_1391_, 0);
v_size_1540_ = lean_ctor_get(v_impl_1537_, 0);
lean_inc(v_size_1540_);
v_k_1541_ = lean_ctor_get(v_impl_1537_, 1);
lean_inc(v_k_1541_);
v_v_1542_ = lean_ctor_get(v_impl_1537_, 2);
lean_inc(v_v_1542_);
v_l_1543_ = lean_ctor_get(v_impl_1537_, 3);
lean_inc(v_l_1543_);
v_r_1544_ = lean_ctor_get(v_impl_1537_, 4);
lean_inc(v_r_1544_);
v___x_1545_ = lean_unsigned_to_nat(3u);
v___x_1546_ = lean_nat_mul(v___x_1545_, v_size_1539_);
v___x_1547_ = lean_nat_dec_lt(v___x_1546_, v_size_1540_);
lean_dec(v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v_r_1544_);
lean_dec(v_l_1543_);
lean_dec(v_v_1542_);
lean_dec(v_k_1541_);
v___x_1548_ = lean_nat_add(v___x_1538_, v_size_1539_);
v___x_1549_ = lean_nat_add(v___x_1548_, v_size_1540_);
lean_dec(v_size_1540_);
lean_dec(v___x_1548_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_impl_1537_);
lean_ctor_set(v___x_1394_, 0, v___x_1549_);
v___x_1551_ = v___x_1394_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_l_1391_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_impl_1537_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
else
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1616_; 
v_isSharedCheck_1616_ = !lean_is_exclusive(v_impl_1537_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; 
v_unused_1617_ = lean_ctor_get(v_impl_1537_, 4);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_impl_1537_, 3);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_impl_1537_, 2);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_impl_1537_, 1);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_impl_1537_, 0);
lean_dec(v_unused_1621_);
v___x_1554_ = v_impl_1537_;
v_isShared_1555_ = v_isSharedCheck_1616_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_impl_1537_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1616_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_size_1556_; lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v_l_1559_; lean_object* v_r_1560_; lean_object* v_size_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_size_1556_ = lean_ctor_get(v_l_1543_, 0);
v_k_1557_ = lean_ctor_get(v_l_1543_, 1);
v_v_1558_ = lean_ctor_get(v_l_1543_, 2);
v_l_1559_ = lean_ctor_get(v_l_1543_, 3);
v_r_1560_ = lean_ctor_get(v_l_1543_, 4);
v_size_1561_ = lean_ctor_get(v_r_1544_, 0);
v___x_1562_ = lean_unsigned_to_nat(2u);
v___x_1563_ = lean_nat_mul(v___x_1562_, v_size_1561_);
v___x_1564_ = lean_nat_dec_lt(v_size_1556_, v___x_1563_);
lean_dec(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1592_; 
lean_inc(v_r_1560_);
lean_inc(v_l_1559_);
lean_inc(v_v_1558_);
lean_inc(v_k_1557_);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_l_1543_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; lean_object* v_unused_1596_; lean_object* v_unused_1597_; 
v_unused_1593_ = lean_ctor_get(v_l_1543_, 4);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1543_, 3);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1543_, 2);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_l_1543_, 1);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_l_1543_, 0);
lean_dec(v_unused_1597_);
v___x_1566_ = v_l_1543_;
v_isShared_1567_ = v_isSharedCheck_1592_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_l_1543_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1592_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1582_; 
v___x_1568_ = lean_nat_add(v___x_1538_, v_size_1539_);
v___x_1569_ = lean_nat_add(v___x_1568_, v_size_1540_);
lean_dec(v_size_1540_);
if (lean_obj_tag(v_l_1559_) == 0)
{
lean_object* v_size_1590_; 
v_size_1590_ = lean_ctor_get(v_l_1559_, 0);
lean_inc(v_size_1590_);
v___y_1582_ = v_size_1590_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
v___y_1582_ = v___x_1591_;
goto v___jp_1581_;
}
v___jp_1570_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_nat_add(v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_r_1544_);
lean_ctor_set(v___x_1566_, 3, v_r_1560_);
lean_ctor_set(v___x_1566_, 2, v_v_1542_);
lean_ctor_set(v___x_1566_, 1, v_k_1541_);
lean_ctor_set(v___x_1566_, 0, v___x_1574_);
v___x_1576_ = v___x_1566_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_r_1560_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_r_1544_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v___x_1576_);
lean_ctor_set(v___x_1554_, 3, v___y_1571_);
lean_ctor_set(v___x_1554_, 2, v_v_1558_);
lean_ctor_set(v___x_1554_, 1, v_k_1557_);
lean_ctor_set(v___x_1554_, 0, v___x_1569_);
v___x_1578_ = v___x_1554_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v___y_1571_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_nat_add(v___x_1568_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec(v___x_1568_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_l_1559_);
lean_ctor_set(v___x_1394_, 0, v___x_1583_);
v___x_1585_ = v___x_1394_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_l_1391_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_l_1559_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_nat_add(v___x_1538_, v_size_1561_);
if (lean_obj_tag(v_r_1560_) == 0)
{
lean_object* v_size_1587_; 
v_size_1587_ = lean_ctor_get(v_r_1560_, 0);
lean_inc(v_size_1587_);
v___y_1571_ = v___x_1585_;
v___y_1572_ = v___x_1586_;
v___y_1573_ = v_size_1587_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_unsigned_to_nat(0u);
v___y_1571_ = v___x_1585_;
v___y_1572_ = v___x_1586_;
v___y_1573_ = v___x_1588_;
goto v___jp_1570_;
}
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_del_object(v___x_1394_);
v___x_1598_ = lean_nat_add(v___x_1538_, v_size_1539_);
v___x_1599_ = lean_nat_add(v___x_1598_, v_size_1540_);
lean_dec(v_size_1540_);
v___x_1600_ = lean_nat_add(v___x_1598_, v_size_1556_);
lean_dec(v___x_1598_);
lean_inc_ref(v_l_1391_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v_l_1543_);
lean_ctor_set(v___x_1554_, 3, v_l_1391_);
lean_ctor_set(v___x_1554_, 2, v_v_1390_);
lean_ctor_set(v___x_1554_, 1, v_k_1389_);
lean_ctor_set(v___x_1554_, 0, v___x_1600_);
v___x_1602_ = v___x_1554_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_l_1391_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_l_1543_);
v___x_1602_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_isSharedCheck_1609_ = !lean_is_exclusive(v_l_1391_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1610_ = lean_ctor_get(v_l_1391_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_l_1391_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_l_1391_, 2);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_l_1391_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_l_1391_, 0);
lean_dec(v_unused_1614_);
v___x_1604_ = v_l_1391_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v_l_1391_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 4, v_r_1544_);
lean_ctor_set(v___x_1604_, 3, v___x_1602_);
lean_ctor_set(v___x_1604_, 2, v_v_1542_);
lean_ctor_set(v___x_1604_, 1, v_k_1541_);
lean_ctor_set(v___x_1604_, 0, v___x_1599_);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_r_1544_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1622_; 
v_l_1622_ = lean_ctor_get(v_impl_1537_, 3);
lean_inc(v_l_1622_);
if (lean_obj_tag(v_l_1622_) == 0)
{
lean_object* v_r_1623_; lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1648_; 
v_r_1623_ = lean_ctor_get(v_impl_1537_, 4);
v_k_1624_ = lean_ctor_get(v_impl_1537_, 1);
v_v_1625_ = lean_ctor_get(v_impl_1537_, 2);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_impl_1537_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1649_ = lean_ctor_get(v_impl_1537_, 3);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_impl_1537_, 0);
lean_dec(v_unused_1650_);
v___x_1627_ = v_impl_1537_;
v_isShared_1628_ = v_isSharedCheck_1648_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_r_1623_);
lean_inc(v_v_1625_);
lean_inc(v_k_1624_);
lean_dec(v_impl_1537_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1648_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_k_1629_; lean_object* v_v_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1644_; 
v_k_1629_ = lean_ctor_get(v_l_1622_, 1);
v_v_1630_ = lean_ctor_get(v_l_1622_, 2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_l_1622_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; 
v_unused_1645_ = lean_ctor_get(v_l_1622_, 4);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_l_1622_, 3);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_l_1622_, 0);
lean_dec(v_unused_1647_);
v___x_1632_ = v_l_1622_;
v_isShared_1633_ = v_isSharedCheck_1644_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_v_1630_);
lean_inc(v_k_1629_);
lean_dec(v_l_1622_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1644_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1623_, 2);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 4, v_r_1623_);
lean_ctor_set(v___x_1632_, 3, v_r_1623_);
lean_ctor_set(v___x_1632_, 2, v_v_1390_);
lean_ctor_set(v___x_1632_, 1, v_k_1389_);
lean_ctor_set(v___x_1632_, 0, v___x_1538_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_r_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_r_1623_);
v___x_1636_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
lean_inc(v_r_1623_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 3, v_r_1623_);
lean_ctor_set(v___x_1627_, 0, v___x_1538_);
v___x_1638_ = v___x_1627_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_r_1623_);
lean_ctor_set(v_reuseFailAlloc_1642_, 4, v_r_1623_);
v___x_1638_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v___x_1638_);
lean_ctor_set(v___x_1394_, 3, v___x_1636_);
lean_ctor_set(v___x_1394_, 2, v_v_1630_);
lean_ctor_set(v___x_1394_, 1, v_k_1629_);
lean_ctor_set(v___x_1394_, 0, v___x_1634_);
v___x_1640_ = v___x_1394_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1629_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1630_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
}
else
{
lean_object* v_r_1651_; 
v_r_1651_ = lean_ctor_get(v_impl_1537_, 4);
lean_inc(v_r_1651_);
if (lean_obj_tag(v_r_1651_) == 0)
{
lean_object* v_k_1652_; lean_object* v_v_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1664_; 
v_k_1652_ = lean_ctor_get(v_impl_1537_, 1);
v_v_1653_ = lean_ctor_get(v_impl_1537_, 2);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_impl_1537_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; 
v_unused_1665_ = lean_ctor_get(v_impl_1537_, 4);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_impl_1537_, 3);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_impl_1537_, 0);
lean_dec(v_unused_1667_);
v___x_1655_ = v_impl_1537_;
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_v_1653_);
lean_inc(v_k_1652_);
lean_dec(v_impl_1537_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_unsigned_to_nat(3u);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 4, v_l_1622_);
lean_ctor_set(v___x_1655_, 2, v_v_1390_);
lean_ctor_set(v___x_1655_, 1, v_k_1389_);
lean_ctor_set(v___x_1655_, 0, v___x_1538_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v_l_1622_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v_l_1622_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_r_1651_);
lean_ctor_set(v___x_1394_, 3, v___x_1659_);
lean_ctor_set(v___x_1394_, 2, v_v_1653_);
lean_ctor_set(v___x_1394_, 1, v_k_1652_);
lean_ctor_set(v___x_1394_, 0, v___x_1657_);
v___x_1661_ = v___x_1394_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_k_1652_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_v_1653_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v_r_1651_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_unsigned_to_nat(2u);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_impl_1537_);
lean_ctor_set(v___x_1394_, 3, v_r_1651_);
lean_ctor_set(v___x_1394_, 0, v___x_1668_);
v___x_1670_ = v___x_1394_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_r_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_impl_1537_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
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
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_k_1385_);
lean_ctor_set(v___x_1674_, 2, v_v_1386_);
lean_ctor_set(v___x_1674_, 3, v_t_1387_);
lean_ctor_set(v___x_1674_, 4, v_t_1387_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_1675_, size_t v_sz_1676_, size_t v_i_1677_, lean_object* v_b_1678_){
_start:
{
lean_object* v___y_1681_; uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1677_, v_sz_1676_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_b_1678_);
return v___x_1686_;
}
else
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_array_uget_borrowed(v_as_1675_, v_i_1677_);
lean_inc(v_b_1678_);
lean_inc(v_a_1687_);
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_1687_, v_b_1678_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_box(0);
lean_inc(v_a_1687_);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_1687_, v___x_1689_, v_b_1678_);
v___y_1681_ = v___x_1690_;
goto v___jp_1680_;
}
else
{
v___y_1681_ = v_b_1678_;
goto v___jp_1680_;
}
}
v___jp_1680_:
{
size_t v___x_1682_; size_t v___x_1683_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1677_, v___x_1682_);
v_i_1677_ = v___x_1683_;
v_b_1678_ = v___y_1681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_1691_, lean_object* v_sz_1692_, lean_object* v_i_1693_, lean_object* v_b_1694_, lean_object* v___y_1695_){
_start:
{
size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1692_);
lean_dec(v_sz_1692_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1693_);
lean_dec(v_i_1693_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1691_, v_sz_boxed_1696_, v_i_boxed_1697_, v_b_1694_);
lean_dec_ref(v_as_1691_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v_set_1707_; size_t v_sz_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v_set_1707_ = lean_box(1);
v_sz_1708_ = lean_array_size(v_a_1706_);
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_1706_, v_sz_1708_, v___x_1709_, v_set_1707_);
lean_dec(v_a_1706_);
return v___x_1710_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1705_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1705_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_1726_, lean_object* v_k_1727_, lean_object* v_t_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1727_, v_t_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_1730_, lean_object* v_k_1731_, lean_object* v_t_1732_){
_start:
{
uint8_t v_res_1733_; lean_object* v_r_1734_; 
v_res_1733_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_1730_, v_k_1731_, v_t_1732_);
v_r_1734_ = lean_box(v_res_1733_);
return v_r_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_1735_, lean_object* v_k_1736_, lean_object* v_v_1737_, lean_object* v_t_1738_, lean_object* v_hl_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1736_, v_v_1737_, v_t_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_1741_, size_t v_sz_1742_, size_t v_i_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1741_, v_sz_1742_, v_i_1743_, v_b_1744_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_1751_, lean_object* v_sz_1752_, lean_object* v_i_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
size_t v_sz_boxed_1760_; size_t v_i_boxed_1761_; lean_object* v_res_1762_; 
v_sz_boxed_1760_ = lean_unbox_usize(v_sz_1752_);
lean_dec(v_sz_1752_);
v_i_boxed_1761_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1751_, v_sz_boxed_1760_, v_i_boxed_1761_, v_b_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v_as_1751_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_1763_, lean_object* v_declName_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
uint8_t v___y_1771_; uint8_t v___y_1793_; lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Expr_getAppFn(v_e_1763_);
if (lean_obj_tag(v___x_1796_) == 4)
{
lean_object* v_declName_1797_; lean_object* v___x_1798_; 
v_declName_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc_n(v_declName_1797_, 2);
lean_dec_ref_known(v___x_1796_, 2);
v___x_1798_ = lean_private_to_user_name(v_declName_1797_);
if (lean_obj_tag(v___x_1798_) == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_name_eq(v_declName_1797_, v_declName_1764_);
lean_dec(v_declName_1797_);
v___y_1793_ = v___x_1799_;
goto v___jp_1792_;
}
else
{
lean_object* v_val_1800_; uint8_t v___x_1801_; 
lean_dec(v_declName_1797_);
v_val_1800_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_val_1800_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1801_ = lean_name_eq(v_val_1800_, v_declName_1764_);
lean_dec(v_val_1800_);
v___y_1793_ = v___x_1801_;
goto v___jp_1792_;
}
}
else
{
uint8_t v___x_1802_; 
lean_dec_ref(v___x_1796_);
v___x_1802_ = 0;
v___y_1771_ = v___x_1802_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_1763_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1783_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
if (lean_obj_tag(v_a_1773_) == 1)
{
lean_object* v_val_1777_; 
lean_del_object(v___x_1775_);
v_val_1777_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v_a_1773_, 1);
v_e_1763_ = v_val_1777_;
goto _start;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_dec(v_a_1773_);
v___x_1779_ = lean_box(v___y_1771_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1779_);
v___x_1781_ = v___x_1775_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1772_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1772_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
v___jp_1792_:
{
if (v___y_1793_ == 0)
{
v___y_1771_ = v___y_1793_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v_e_1763_);
v___x_1794_ = lean_box(v___y_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_1803_, lean_object* v_declName_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1803_, v_declName_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_declName_1804_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_1811_, lean_object* v_b_1812_, lean_object* v_c_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
v___x_1819_ = lean_apply_7(v_k_1811_, v_b_1812_, v_c_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, lean_box(0));
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_1820_, lean_object* v_b_1821_, lean_object* v_c_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1820_, v_b_1821_, v_c_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_1829_, lean_object* v_k_1830_, uint8_t v_cleanupAnnotations_1831_, uint8_t v_whnfType_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___f_1838_; lean_object* v___x_1839_; 
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1838_, 0, v_k_1830_);
v___x_1839_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1829_, v___f_1838_, v_cleanupAnnotations_1831_, v_whnfType_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
v_a_1848_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1839_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1839_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_1856_, lean_object* v_k_1857_, lean_object* v_cleanupAnnotations_1858_, lean_object* v_whnfType_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1865_; uint8_t v_whnfType_boxed_1866_; lean_object* v_res_1867_; 
v_cleanupAnnotations_boxed_1865_ = lean_unbox(v_cleanupAnnotations_1858_);
v_whnfType_boxed_1866_ = lean_unbox(v_whnfType_1859_);
v_res_1867_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1856_, v_k_1857_, v_cleanupAnnotations_boxed_1865_, v_whnfType_boxed_1866_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_1868_, lean_object* v_type_1869_, lean_object* v_k_1870_, uint8_t v_cleanupAnnotations_1871_, uint8_t v_whnfType_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1869_, v_k_1870_, v_cleanupAnnotations_1871_, v_whnfType_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_1879_, lean_object* v_type_1880_, lean_object* v_k_1881_, lean_object* v_cleanupAnnotations_1882_, lean_object* v_whnfType_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1889_; uint8_t v_whnfType_boxed_1890_; lean_object* v_res_1891_; 
v_cleanupAnnotations_boxed_1889_ = lean_unbox(v_cleanupAnnotations_1882_);
v_whnfType_boxed_1890_ = lean_unbox(v_whnfType_1883_);
v_res_1891_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_1879_, v_type_1880_, v_k_1881_, v_cleanupAnnotations_boxed_1889_, v_whnfType_boxed_1890_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_1895_, lean_object* v_as_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_b_1899_);
return v___x_1906_;
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec_ref(v_b_1899_);
v_a_1907_ = lean_array_uget_borrowed(v_as_1896_, v_i_1898_);
v___x_1908_ = l_Lean_Expr_fvarId_x21(v_a_1907_);
v___x_1909_ = l_Lean_FVarId_getDecl___redArg(v___x_1908_, v___y_1900_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = l_Lean_LocalDecl_type(v_a_1910_);
lean_dec(v_a_1910_);
v___x_1912_ = l_Lean_Expr_consumeMData(v___x_1911_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_1912_, v_typeName_1895_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1929_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1929_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1929_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_unbox(v_a_1914_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; size_t v___x_1921_; size_t v___x_1922_; 
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
v___x_1920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1898_, v___x_1921_);
v_i_1898_ = v___x_1922_;
v_b_1899_ = v___x_1920_;
goto _start;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1914_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___x_1918_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1925_);
v___x_1927_ = v___x_1916_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1913_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1913_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1938_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1909_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1909_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_1946_, lean_object* v_as_1947_, lean_object* v_sz_1948_, lean_object* v_i_1949_, lean_object* v_b_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1948_);
lean_dec(v_sz_1948_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1946_, v_as_1947_, v_sz_boxed_1956_, v_i_boxed_1957_, v_b_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v_as_1947_);
lean_dec(v_typeName_1946_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_1959_, lean_object* v_xs_1960_, lean_object* v_x_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; size_t v_sz_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_1968_ = lean_array_size(v_xs_1960_);
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1959_, v_xs_1960_, v_sz_1968_, v___x_1969_, v___x_1967_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1985_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_fst_1975_; 
v_fst_1975_ = lean_ctor_get(v_a_1971_, 0);
lean_inc(v_fst_1975_);
lean_dec(v_a_1971_);
if (lean_obj_tag(v_fst_1975_) == 0)
{
uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = 0;
v___x_1977_ = lean_box(v___x_1976_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1977_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
else
{
lean_object* v_val_1981_; lean_object* v___x_1983_; 
v_val_1981_ = lean_ctor_get(v_fst_1975_, 0);
lean_inc(v_val_1981_);
lean_dec_ref_known(v_fst_1975_, 1);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_val_1981_);
v___x_1983_ = v___x_1973_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_val_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1970_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1970_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_1994_, lean_object* v_xs_1995_, lean_object* v_x_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_1994_, v_xs_1995_, v_x_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec_ref(v_x_1996_);
lean_dec_ref(v_xs_1995_);
lean_dec(v_typeName_1994_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_2003_, lean_object* v_info_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___f_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v___f_2010_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2010_, 0, v_typeName_2003_);
v___x_2011_ = l_Lean_ConstantInfo_type(v_info_2004_);
v___x_2012_ = 0;
v___x_2013_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_2011_, v___f_2010_, v___x_2012_, v___x_2012_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_2014_, lean_object* v_info_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2014_, v_info_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_info_2015_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_Expr_hasMVar(v_e_2022_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_e_2022_);
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; lean_object* v_mctx_2028_; lean_object* v___x_2029_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; lean_object* v_cache_2033_; lean_object* v_zetaDeltaFVarIds_2034_; lean_object* v_postponed_2035_; lean_object* v_diag_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2045_; 
v___x_2027_ = lean_st_ref_get(v___y_2023_);
v_mctx_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc_ref(v_mctx_2028_);
lean_dec(v___x_2027_);
v___x_2029_ = l_Lean_instantiateMVarsCore(v_mctx_2028_, v_e_2022_);
v_fst_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_fst_2030_);
v_snd_2031_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_snd_2031_);
lean_dec_ref(v___x_2029_);
v___x_2032_ = lean_st_ref_take(v___y_2023_);
v_cache_2033_ = lean_ctor_get(v___x_2032_, 1);
v_zetaDeltaFVarIds_2034_ = lean_ctor_get(v___x_2032_, 2);
v_postponed_2035_ = lean_ctor_get(v___x_2032_, 3);
v_diag_2036_ = lean_ctor_get(v___x_2032_, 4);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2046_);
v___x_2038_ = v___x_2032_;
v_isShared_2039_ = v_isSharedCheck_2045_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_diag_2036_);
lean_inc(v_postponed_2035_);
lean_inc(v_zetaDeltaFVarIds_2034_);
lean_inc(v_cache_2033_);
lean_dec(v___x_2032_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2045_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_snd_2031_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_snd_2031_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_cache_2033_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_zetaDeltaFVarIds_2034_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_postponed_2035_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_diag_2036_);
v___x_2041_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_st_ref_set(v___y_2023_, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_fst_2030_);
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object* v_e_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2047_, v___y_2048_);
lean_dec(v___y_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object* v_e_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2051_, v___y_2053_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object* v_e_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object* v_type_2065_, lean_object* v_k_2066_, uint8_t v_cleanupAnnotations_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___f_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2073_, 0, v_k_2066_);
v___x_2074_ = 0;
v___x_2075_ = lean_box(0);
v___x_2076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2074_, v___x_2075_, v_type_2065_, v___f_2073_, v_cleanupAnnotations_2067_, v___x_2074_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2076_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2076_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object* v_type_2093_, lean_object* v_k_2094_, lean_object* v_cleanupAnnotations_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2101_; lean_object* v_res_2102_; 
v_cleanupAnnotations_boxed_2101_ = lean_unbox(v_cleanupAnnotations_2095_);
v_res_2102_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2093_, v_k_2094_, v_cleanupAnnotations_boxed_2101_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object* v_00_u03b1_2103_, lean_object* v_type_2104_, lean_object* v_k_2105_, uint8_t v_cleanupAnnotations_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2104_, v_k_2105_, v_cleanupAnnotations_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_type_2114_, lean_object* v_k_2115_, lean_object* v_cleanupAnnotations_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2122_; lean_object* v_res_2123_; 
v_cleanupAnnotations_boxed_2122_ = lean_unbox(v_cleanupAnnotations_2116_);
v_res_2123_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(v_00_u03b1_2113_, v_type_2114_, v_k_2115_, v_cleanupAnnotations_boxed_2122_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object* v_typeNameSet_2124_, lean_object* v_x_2125_, lean_object* v_type_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2124_, v_x_2125_, v_type_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec_ref(v_x_2125_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object* v_typeNameSet_2133_, lean_object* v_type_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___f_2140_; lean_object* v_a_2142_; lean_object* v___y_2192_; lean_object* v___x_2202_; 
lean_inc(v_typeNameSet_2133_);
v___f_2140_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2140_, 0, v_typeNameSet_2133_);
lean_inc_ref(v_type_2134_);
v___x_2202_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(v_type_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_dec_ref(v_type_2134_);
v___y_2192_ = v___x_2202_;
goto v___jp_2191_;
}
else
{
lean_object* v_a_2203_; uint8_t v___y_2205_; uint8_t v___x_2206_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
v___x_2206_ = l_Lean_Exception_isInterrupt(v_a_2203_);
if (v___x_2206_ == 0)
{
uint8_t v___x_2207_; 
v___x_2207_ = l_Lean_Exception_isRuntime(v_a_2203_);
v___y_2205_ = v___x_2207_;
goto v___jp_2204_;
}
else
{
lean_dec(v_a_2203_);
v___y_2205_ = v___x_2206_;
goto v___jp_2204_;
}
v___jp_2204_:
{
if (v___y_2205_ == 0)
{
lean_dec_ref_known(v___x_2202_, 1);
v_a_2142_ = v_type_2134_;
goto v___jp_2141_;
}
else
{
lean_dec_ref(v_type_2134_);
v___y_2192_ = v___x_2202_;
goto v___jp_2191_;
}
}
}
v___jp_2141_:
{
uint8_t v___x_2143_; 
v___x_2143_ = l_Lean_Expr_isForall(v_a_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
lean_dec_ref(v___f_2140_);
v___x_2144_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_a_2142_, v_a_2136_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2180_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2180_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2180_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Expr_getAppFn(v_a_2145_);
if (lean_obj_tag(v___x_2149_) == 4)
{
lean_object* v_declName_2150_; uint8_t v___x_2151_; 
v_declName_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_declName_2150_);
lean_dec_ref_known(v___x_2149_, 2);
lean_inc(v_typeNameSet_2133_);
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_declName_2150_, v_typeNameSet_2133_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_del_object(v___x_2147_);
v___x_2152_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_a_2145_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2163_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2163_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2163_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
if (lean_obj_tag(v_a_2153_) == 1)
{
lean_object* v_val_2157_; 
lean_del_object(v___x_2155_);
v_val_2157_ = lean_ctor_get(v_a_2153_, 0);
lean_inc(v_val_2157_);
lean_dec_ref_known(v_a_2153_, 1);
v_type_2134_ = v_val_2157_;
goto _start;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_2153_);
lean_dec(v_typeNameSet_2133_);
v___x_2159_ = lean_box(v___x_2151_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2159_);
v___x_2161_ = v___x_2155_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_typeNameSet_2133_);
v_a_2164_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2152_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2152_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v_a_2145_);
lean_dec(v_typeNameSet_2133_);
v___x_2172_ = lean_box(v___x_2151_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2172_);
v___x_2174_ = v___x_2147_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec_ref(v___x_2149_);
lean_dec(v_a_2145_);
lean_dec(v_typeNameSet_2133_);
v___x_2176_ = lean_box(v___x_2143_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2176_);
v___x_2178_ = v___x_2147_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_typeNameSet_2133_);
v_a_2181_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2144_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2144_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
uint8_t v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_typeNameSet_2133_);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_a_2142_, v___f_2140_, v___x_2189_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
return v___x_2190_;
}
}
v___jp_2191_:
{
if (lean_obj_tag(v___y_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___y_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___y_2192_, 1);
v_a_2142_ = v_a_2193_;
goto v___jp_2141_;
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v___f_2140_);
lean_dec(v_typeNameSet_2133_);
v_a_2194_ = lean_ctor_get(v___y_2192_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___y_2192_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___y_2192_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___y_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object* v_typeNameSet_2208_, lean_object* v_x_2209_, lean_object* v_type_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2208_, v_type_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object* v_typeNameSet_2217_, lean_object* v_type_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2217_, v_type_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* v_typeNameSet_2225_, lean_object* v_info_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = l_Lean_ConstantInfo_type(v_info_2226_);
v___x_2233_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2225_, v___x_2232_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* v_typeNameSet_2234_, lean_object* v_info_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2234_, v_info_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec_ref(v_info_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* v_matchAlias_2242_, lean_object* v_addAlias_2243_, lean_object* v_alias_2244_, lean_object* v_declNames_2245_, lean_object* v_ns_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
lean_inc_ref(v_matchAlias_2242_);
lean_inc(v_alias_2244_);
lean_inc(v_ns_2246_);
v___x_2255_ = lean_apply_2(v_matchAlias_2242_, v_ns_2246_, v_alias_2244_);
v___x_2256_ = lean_unbox(v___x_2255_);
if (v___x_2256_ == 0)
{
if (lean_obj_tag(v_ns_2246_) == 1)
{
lean_object* v_pre_2257_; 
v_pre_2257_ = lean_ctor_get(v_ns_2246_, 0);
lean_inc(v_pre_2257_);
lean_dec_ref_known(v_ns_2246_, 2);
v_ns_2246_ = v_pre_2257_;
goto _start;
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v_ns_2246_);
lean_dec(v_declNames_2245_);
lean_dec(v_alias_2244_);
lean_dec_ref(v_addAlias_2243_);
lean_dec_ref(v_matchAlias_2242_);
v___x_2259_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
else
{
lean_object* v___x_2261_; 
lean_dec(v_ns_2246_);
lean_dec_ref(v_matchAlias_2242_);
lean_inc(v_a_2253_);
lean_inc_ref(v_a_2252_);
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
lean_inc_ref(v_a_2249_);
lean_inc(v_a_2248_);
lean_inc_ref(v_a_2247_);
v___x_2261_ = lean_apply_10(v_addAlias_2243_, v_alias_2244_, v_declNames_2245_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, lean_box(0));
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object* v_matchAlias_2262_, lean_object* v_addAlias_2263_, lean_object* v_alias_2264_, lean_object* v_declNames_2265_, lean_object* v_ns_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2262_, v_addAlias_2263_, v_alias_2264_, v_declNames_2265_, v_ns_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object* v_a_2278_){
_start:
{
uint8_t v___x_2280_; 
v___x_2280_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_2278_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0));
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object* v_a_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2285_);
lean_dec_ref(v_a_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object* v_a_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2288_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object* v_a_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object* v_ctx_2302_, lean_object* v_id_2303_, uint8_t v_danglingDot_2304_, lean_object* v_declName_2305_, lean_object* v_decl_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
lean_inc(v_declName_2305_);
v___x_2315_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_2302_, v_declName_2305_, v_id_2303_, v_danglingDot_2304_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2368_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2368_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2368_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_decl_2306_);
lean_dec(v_declName_2305_);
v_a_2320_ = lean_ctor_get(v_a_2316_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_a_2316_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2322_ = v_a_2316_;
v_isShared_2323_ = v_isSharedCheck_2330_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v_a_2316_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2330_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2325_);
v___x_2327_ = v___x_2318_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v_a_2331_; 
v_a_2331_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v_a_2316_, 1);
if (lean_obj_tag(v_a_2331_) == 1)
{
lean_object* v_val_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2318_);
v_val_2332_ = lean_ctor_get(v_a_2331_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2331_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2334_ = v_a_2331_;
v_isShared_2335_ = v_isSharedCheck_2363_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_val_2332_);
lean_dec(v_a_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2363_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_kind_2336_; lean_object* v_tags_2337_; lean_object* v___x_2338_; 
v_kind_2336_ = lean_ctor_get(v_decl_2306_, 1);
lean_inc_ref(v_kind_2336_);
v_tags_2337_ = lean_ctor_get(v_decl_2306_, 2);
lean_inc_ref(v_tags_2337_);
lean_dec_ref(v_decl_2306_);
lean_inc(v___y_2313_);
lean_inc_ref(v___y_2312_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
v___x_2338_ = lean_apply_5(v_kind_2336_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, lean_box(0));
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
lean_inc(v___y_2313_);
lean_inc_ref(v___y_2312_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
v___x_2340_ = lean_apply_5(v_tags_2337_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, lean_box(0));
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 0);
lean_ctor_set(v___x_2334_, 0, v_declName_2305_);
v___x_2343_ = v___x_2334_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_declName_2305_);
v___x_2343_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
uint8_t v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_unbox(v_a_2339_);
lean_dec(v_a_2339_);
v___x_2345_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_2332_, v___x_2343_, v___x_2344_, v_a_2341_, v___y_2307_, v___y_2308_);
return v___x_2345_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_a_2339_);
lean_del_object(v___x_2334_);
lean_dec(v_val_2332_);
lean_dec(v_declName_2305_);
v_a_2347_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2340_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2340_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_tags_2337_);
lean_del_object(v___x_2334_);
lean_dec(v_val_2332_);
lean_dec(v_declName_2305_);
v_a_2355_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2338_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2338_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
lean_dec(v_a_2331_);
lean_dec_ref(v_decl_2306_);
lean_dec(v_declName_2305_);
v___x_2364_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2364_);
v___x_2366_ = v___x_2318_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_decl_2306_);
lean_dec(v_declName_2305_);
v_a_2369_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2315_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2315_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object* v_ctx_2377_, lean_object* v_id_2378_, lean_object* v_danglingDot_2379_, lean_object* v_declName_2380_, lean_object* v_decl_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v_danglingDot_boxed_2390_; lean_object* v_res_2391_; 
v_danglingDot_boxed_2390_ = lean_unbox(v_danglingDot_2379_);
v_res_2391_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2377_, v_id_2378_, v_danglingDot_boxed_2390_, v_declName_2380_, v_decl_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
return v_res_2391_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object* v_id_2392_, uint8_t v_danglingDot_2393_, lean_object* v_ns_2394_, lean_object* v_alias_2395_){
_start:
{
uint8_t v___x_2396_; 
v___x_2396_ = l_Lean_Name_isPrefixOf(v_ns_2394_, v_alias_2395_);
if (v___x_2396_ == 0)
{
lean_dec(v_alias_2395_);
return v___x_2396_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2397_ = lean_box(0);
v___x_2398_ = l_Lean_Name_replacePrefix(v_alias_2395_, v_ns_2394_, v___x_2397_);
v___x_2399_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_2392_, v___x_2398_, v_danglingDot_2393_);
lean_dec(v___x_2398_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object* v_id_2400_, lean_object* v_danglingDot_2401_, lean_object* v_ns_2402_, lean_object* v_alias_2403_){
_start:
{
uint8_t v_danglingDot_boxed_2404_; uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_danglingDot_boxed_2404_ = lean_unbox(v_danglingDot_2401_);
v_res_2405_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2400_, v_danglingDot_boxed_2404_, v_ns_2402_, v_alias_2403_);
lean_dec(v_ns_2402_);
lean_dec(v_id_2400_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object* v_a_2407_, lean_object* v___x_2408_, lean_object* v_alias_2409_, lean_object* v_as_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
if (lean_obj_tag(v_as_2410_) == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref(v___x_2408_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
else
{
lean_object* v_head_2420_; lean_object* v_tail_2421_; uint8_t v___x_2422_; 
v_head_2420_ = lean_ctor_get(v_as_2410_, 0);
lean_inc_n(v_head_2420_, 2);
v_tail_2421_ = lean_ctor_get(v_as_2410_, 1);
lean_inc(v_tail_2421_);
lean_dec_ref_known(v_as_2410_, 2);
lean_inc_ref(v___x_2408_);
v___x_2422_ = l_Lean_Server_Completion_allowCompletion(v_a_2407_, v___x_2408_, v_head_2420_);
if (v___x_2422_ == 0)
{
lean_dec(v_head_2420_);
v_as_2410_ = v_tail_2421_;
goto _start;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2424_ = l_Lean_Name_getString_x21(v_alias_2409_);
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Lean_Name_str___override(v___x_2425_, v___x_2424_);
v___x_2427_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_2426_, v_head_2420_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_dec_ref_known(v___x_2427_, 1);
v_as_2410_ = v_tail_2421_;
goto _start;
}
else
{
lean_dec(v_tail_2421_);
lean_dec_ref(v___x_2408_);
return v___x_2427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object* v_a_2429_, lean_object* v___x_2430_, lean_object* v_alias_2431_, lean_object* v_as_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2429_, v___x_2430_, v_alias_2431_, v_as_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v_alias_2431_);
lean_dec_ref(v_a_2429_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object* v_a_2441_, lean_object* v_env_2442_, lean_object* v_alias_2443_, lean_object* v_declNames_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2441_, v_env_2442_, v_alias_2443_, v_declNames_2444_, v___y_2445_, v___y_2446_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object* v_a_2454_, lean_object* v_env_2455_, lean_object* v_alias_2456_, lean_object* v_declNames_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2454_, v_env_2455_, v_alias_2456_, v_declNames_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v_alias_2456_);
lean_dec_ref(v_a_2454_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object* v___f_2467_, lean_object* v___f_2468_, lean_object* v_currNamespace_2469_, lean_object* v_alias_2470_, lean_object* v_declNames_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v___f_2467_, v___f_2468_, v_alias_2470_, v_declNames_2471_, v_currNamespace_2469_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object* v___f_2481_, lean_object* v___f_2482_, lean_object* v_currNamespace_2483_, lean_object* v_alias_2484_, lean_object* v_declNames_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2481_, v___f_2482_, v_currNamespace_2483_, v_alias_2484_, v_declNames_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object* v_f_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
if (lean_obj_tag(v_x_2497_) == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v_f_2495_);
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_x_2496_);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
else
{
lean_object* v_key_2508_; lean_object* v_value_2509_; lean_object* v_tail_2510_; lean_object* v___x_2511_; 
v_key_2508_ = lean_ctor_get(v_x_2497_, 0);
lean_inc(v_key_2508_);
v_value_2509_ = lean_ctor_get(v_x_2497_, 1);
lean_inc(v_value_2509_);
v_tail_2510_ = lean_ctor_get(v_x_2497_, 2);
lean_inc(v_tail_2510_);
lean_dec_ref_known(v_x_2497_, 3);
lean_inc_ref(v_f_2495_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___y_2499_);
lean_inc_ref(v___y_2498_);
v___x_2511_ = lean_apply_10(v_f_2495_, v_key_2508_, v_value_2509_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, lean_box(0));
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
if (lean_obj_tag(v_a_2512_) == 0)
{
lean_dec_ref_known(v_a_2512_, 1);
lean_dec(v_tail_2510_);
lean_dec_ref(v_f_2495_);
return v___x_2511_;
}
else
{
lean_object* v_a_2513_; 
lean_dec_ref_known(v___x_2511_, 1);
v_a_2513_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v_a_2512_, 1);
v_x_2496_ = v_a_2513_;
v_x_2497_ = v_tail_2510_;
goto _start;
}
}
else
{
lean_dec(v_tail_2510_);
lean_dec_ref(v_f_2495_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object* v_f_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2515_, v_x_2516_, v_x_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(lean_object* v_f_2527_, lean_object* v_as_2528_, size_t v_i_2529_, size_t v_stop_2530_, lean_object* v_b_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_usize_dec_eq(v_i_2529_, v_stop_2530_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_array_uget_borrowed(v_as_2528_, v_i_2529_);
v___x_2542_ = lean_box(0);
lean_inc(v___x_2541_);
lean_inc_ref(v_f_2527_);
v___x_2543_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2527_, v___x_2542_, v___x_2541_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
if (lean_obj_tag(v_a_2544_) == 0)
{
lean_dec_ref_known(v_a_2544_, 1);
lean_dec_ref(v_f_2527_);
return v___x_2543_;
}
else
{
lean_object* v_a_2545_; size_t v___x_2546_; size_t v___x_2547_; 
lean_dec_ref_known(v___x_2543_, 1);
v_a_2545_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v_a_2544_, 1);
v___x_2546_ = ((size_t)1ULL);
v___x_2547_ = lean_usize_add(v_i_2529_, v___x_2546_);
v_i_2529_ = v___x_2547_;
v_b_2531_ = v_a_2545_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_2527_);
return v___x_2543_;
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec_ref(v_f_2527_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_b_2531_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg___boxed(lean_object* v_f_2551_, lean_object* v_as_2552_, lean_object* v_i_2553_, lean_object* v_stop_2554_, lean_object* v_b_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
size_t v_i_boxed_2564_; size_t v_stop_boxed_2565_; lean_object* v_res_2566_; 
v_i_boxed_2564_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_stop_boxed_2565_ = lean_unbox_usize(v_stop_2554_);
lean_dec(v_stop_2554_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2551_, v_as_2552_, v_i_boxed_2564_, v_stop_boxed_2565_, v_b_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v_as_2552_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object* v_f_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
v___x_2579_ = lean_apply_10(v_f_2567_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, lean_box(0));
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_f_2580_, lean_object* v_x_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(v_f_2580_, v_x_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(lean_object* v_f_2593_, lean_object* v_keys_2594_, lean_object* v_vals_2595_, lean_object* v_i_2596_, lean_object* v_acc_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = lean_array_get_size(v_keys_2594_);
v___x_2607_ = lean_nat_dec_lt(v_i_2596_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec(v_i_2596_);
lean_dec_ref(v_f_2593_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_acc_2597_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
else
{
lean_object* v_k_2610_; lean_object* v_v_2611_; lean_object* v___x_2612_; 
v_k_2610_ = lean_array_fget_borrowed(v_keys_2594_, v_i_2596_);
v_v_2611_ = lean_array_fget_borrowed(v_vals_2595_, v_i_2596_);
lean_inc_ref(v_f_2593_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v_v_2611_);
lean_inc(v_k_2610_);
v___x_2612_ = lean_apply_11(v_f_2593_, v_acc_2597_, v_k_2610_, v_v_2611_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, lean_box(0));
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_dec_ref_known(v_a_2613_, 1);
lean_dec(v_i_2596_);
lean_dec_ref(v_f_2593_);
return v___x_2612_;
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec_ref_known(v___x_2612_, 1);
v_a_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v_a_2613_, 1);
v___x_2615_ = lean_unsigned_to_nat(1u);
v___x_2616_ = lean_nat_add(v_i_2596_, v___x_2615_);
lean_dec(v_i_2596_);
v_i_2596_ = v___x_2616_;
v_acc_2597_ = v_a_2614_;
goto _start;
}
}
else
{
lean_dec(v_i_2596_);
lean_dec_ref(v_f_2593_);
return v___x_2612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg___boxed(lean_object* v_f_2618_, lean_object* v_keys_2619_, lean_object* v_vals_2620_, lean_object* v_i_2621_, lean_object* v_acc_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2618_, v_keys_2619_, v_vals_2620_, v_i_2621_, v_acc_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v_vals_2620_);
lean_dec_ref(v_keys_2619_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(lean_object* v_f_2632_, lean_object* v_x_2633_, lean_object* v_x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
if (lean_obj_tag(v_x_2633_) == 0)
{
lean_object* v_es_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2665_; 
v_es_2643_ = lean_ctor_get(v_x_2633_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_x_2633_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2645_ = v_x_2633_;
v_isShared_2646_ = v_isSharedCheck_2665_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_es_2643_);
lean_dec(v_x_2633_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2665_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = lean_array_get_size(v_es_2643_);
v___x_2649_ = lean_nat_dec_lt(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2651_; 
lean_dec_ref(v_es_2643_);
lean_dec_ref(v_f_2632_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 1);
lean_ctor_set(v___x_2645_, 0, v_x_2634_);
v___x_2651_ = v___x_2645_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_x_2634_);
v___x_2651_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
return v___x_2652_;
}
}
else
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
if (v___x_2654_ == 0)
{
if (v___x_2649_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v_es_2643_);
lean_dec_ref(v_f_2632_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 1);
lean_ctor_set(v___x_2645_, 0, v_x_2634_);
v___x_2656_ = v___x_2645_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_x_2634_);
v___x_2656_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
else
{
size_t v___x_2659_; size_t v___x_2660_; lean_object* v___x_2661_; 
lean_del_object(v___x_2645_);
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = lean_usize_of_nat(v___x_2648_);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2632_, v_es_2643_, v___x_2659_, v___x_2660_, v_x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v_es_2643_);
return v___x_2661_;
}
}
else
{
size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
lean_del_object(v___x_2645_);
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = lean_usize_of_nat(v___x_2648_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2632_, v_es_2643_, v___x_2662_, v___x_2663_, v_x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v_es_2643_);
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_ks_2666_; lean_object* v_vs_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_ks_2666_ = lean_ctor_get(v_x_2633_, 0);
lean_inc_ref(v_ks_2666_);
v_vs_2667_ = lean_ctor_get(v_x_2633_, 1);
lean_inc_ref(v_vs_2667_);
lean_dec_ref_known(v_x_2633_, 2);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2632_, v_ks_2666_, v_vs_2667_, v___x_2668_, v_x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v_vs_2667_);
lean_dec_ref(v_ks_2666_);
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(lean_object* v_f_2670_, lean_object* v_as_2671_, size_t v_i_2672_, size_t v_stop_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_a_2684_; lean_object* v___y_2689_; uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_eq(v_i_2672_, v_stop_2673_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_array_uget_borrowed(v_as_2671_, v_i_2672_);
switch(lean_obj_tag(v___x_2693_))
{
case 0:
{
lean_object* v_key_2694_; lean_object* v_val_2695_; lean_object* v___x_2696_; 
v_key_2694_ = lean_ctor_get(v___x_2693_, 0);
v_val_2695_ = lean_ctor_get(v___x_2693_, 1);
lean_inc_ref(v_f_2670_);
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
lean_inc_ref(v___y_2677_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v_val_2695_);
lean_inc(v_key_2694_);
v___x_2696_ = lean_apply_11(v_f_2670_, v_b_2674_, v_key_2694_, v_val_2695_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, lean_box(0));
v___y_2689_ = v___x_2696_;
goto v___jp_2688_;
}
case 1:
{
lean_object* v_node_2697_; lean_object* v___x_2698_; 
v_node_2697_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_node_2697_);
lean_inc_ref(v_f_2670_);
v___x_2698_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2670_, v_node_2697_, v_b_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
v___y_2689_ = v___x_2698_;
goto v___jp_2688_;
}
default: 
{
v_a_2684_ = v_b_2674_;
goto v___jp_2683_;
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec_ref(v_f_2670_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_b_2674_);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
v___jp_2683_:
{
size_t v___x_2685_; size_t v___x_2686_; 
v___x_2685_ = ((size_t)1ULL);
v___x_2686_ = lean_usize_add(v_i_2672_, v___x_2685_);
v_i_2672_ = v___x_2686_;
v_b_2674_ = v_a_2684_;
goto _start;
}
v___jp_2688_:
{
if (lean_obj_tag(v___y_2689_) == 0)
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v___y_2689_, 0);
if (lean_obj_tag(v_a_2690_) == 0)
{
lean_dec_ref(v_f_2670_);
return v___y_2689_;
}
else
{
lean_object* v_a_2691_; 
lean_inc_ref(v_a_2690_);
lean_dec_ref_known(v___y_2689_, 1);
v_a_2691_ = lean_ctor_get(v_a_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v_a_2690_, 1);
v_a_2684_ = v_a_2691_;
goto v___jp_2683_;
}
}
else
{
lean_dec_ref(v_f_2670_);
return v___y_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_f_2701_, lean_object* v_as_2702_, lean_object* v_i_2703_, lean_object* v_stop_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
size_t v_i_boxed_2714_; size_t v_stop_boxed_2715_; lean_object* v_res_2716_; 
v_i_boxed_2714_ = lean_unbox_usize(v_i_2703_);
lean_dec(v_i_2703_);
v_stop_boxed_2715_ = lean_unbox_usize(v_stop_2704_);
lean_dec(v_stop_2704_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2701_, v_as_2702_, v_i_boxed_2714_, v_stop_boxed_2715_, v_b_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v_as_2702_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_f_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2717_, v_x_2718_, v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object* v_map_2729_, lean_object* v_f_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___f_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___f_2739_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2739_, 0, v_f_2730_);
v___x_2740_ = lean_box(0);
v___x_2741_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v___f_2739_, v_map_2729_, v___x_2740_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object* v_map_2742_, lean_object* v_f_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_2742_, v_f_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object* v_s_2753_, lean_object* v_f_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_map_u2081_2763_; lean_object* v_map_u2082_2764_; lean_object* v_buckets_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_map_u2081_2763_ = lean_ctor_get(v_s_2753_, 0);
lean_inc_ref(v_map_u2081_2763_);
v_map_u2082_2764_ = lean_ctor_get(v_s_2753_, 1);
lean_inc_ref(v_map_u2082_2764_);
lean_dec_ref(v_s_2753_);
v_buckets_2765_ = lean_ctor_get(v_map_u2081_2763_, 1);
lean_inc_ref(v_buckets_2765_);
lean_dec_ref(v_map_u2081_2763_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = lean_array_get_size(v_buckets_2765_);
v___x_2768_ = lean_nat_dec_lt(v___x_2766_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
lean_dec_ref(v_buckets_2765_);
v___x_2769_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2764_, v_f_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = lean_box(0);
v___x_2771_ = lean_nat_dec_le(v___x_2767_, v___x_2767_);
if (v___x_2771_ == 0)
{
if (v___x_2768_ == 0)
{
lean_object* v___x_2772_; 
lean_dec_ref(v_buckets_2765_);
v___x_2772_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2764_, v_f_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2772_;
}
else
{
size_t v___x_2773_; size_t v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = ((size_t)0ULL);
v___x_2774_ = lean_usize_of_nat(v___x_2767_);
lean_inc_ref(v_f_2754_);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2754_, v_buckets_2765_, v___x_2773_, v___x_2774_, v___x_2770_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec_ref(v_buckets_2765_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
if (lean_obj_tag(v_a_2776_) == 0)
{
lean_dec_ref_known(v_a_2776_, 1);
lean_dec_ref(v_map_u2082_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2775_;
}
else
{
lean_object* v___x_2777_; 
lean_dec_ref_known(v_a_2776_, 1);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2764_, v_f_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2777_;
}
}
else
{
lean_dec_ref(v_map_u2082_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2775_;
}
}
}
else
{
size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = ((size_t)0ULL);
v___x_2779_ = lean_usize_of_nat(v___x_2767_);
lean_inc_ref(v_f_2754_);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2754_, v_buckets_2765_, v___x_2778_, v___x_2779_, v___x_2770_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec_ref(v_buckets_2765_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
if (lean_obj_tag(v_a_2781_) == 0)
{
lean_dec_ref_known(v_a_2781_, 1);
lean_dec_ref(v_map_u2082_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2780_;
}
else
{
lean_object* v___x_2782_; 
lean_dec_ref_known(v_a_2781_, 1);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2764_, v_f_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2782_;
}
}
else
{
lean_dec_ref(v_map_u2082_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object* v_s_2783_, lean_object* v_f_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_2783_, v_f_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object* v_f_2794_, lean_object* v_decl_2795_, lean_object* v_ci_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___y_2807_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_unsigned_to_nat(1u);
v___x_2846_ = lean_nat_add(v___y_2797_, v___x_2845_);
v___x_2847_ = lean_unsigned_to_nat(10000u);
v___x_2848_ = lean_nat_dec_le(v___x_2847_, v___x_2846_);
if (v___x_2848_ == 0)
{
v___y_2807_ = v___x_2846_;
goto v___jp_2806_;
}
else
{
lean_object* v___x_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v___x_2846_);
v___x_2849_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_2800_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2866_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2866_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
if (lean_obj_tag(v_a_2850_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_ci_2796_);
lean_dec(v_decl_2795_);
lean_dec_ref(v_f_2794_);
v_a_2854_ = lean_ctor_get(v_a_2850_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2850_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2856_ = v_a_2850_;
v_isShared_2857_ = v_isSharedCheck_2864_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v_a_2850_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2864_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2859_);
v___x_2861_ = v___x_2852_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v___x_2865_; 
lean_dec_ref_known(v_a_2850_, 1);
lean_del_object(v___x_2852_);
v___x_2865_ = lean_unsigned_to_nat(0u);
v___y_2807_ = v___x_2865_;
goto v___jp_2806_;
}
}
}
v___jp_2806_:
{
lean_object* v___x_2808_; 
lean_inc(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc_ref(v___y_2800_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2808_ = lean_apply_10(v_f_2794_, v_decl_2795_, v_ci_2796_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, lean_box(0));
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2836_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2836_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2836_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v___y_2807_);
v_a_2813_ = lean_ctor_get(v_a_2809_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_a_2809_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2815_ = v_a_2809_;
v_isShared_2816_ = v_isSharedCheck_2823_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v_a_2809_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2823_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2818_);
v___x_2820_ = v___x_2811_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2835_; 
v_a_2824_ = lean_ctor_get(v_a_2809_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_a_2809_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2826_ = v_a_2809_;
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v_a_2809_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2824_);
lean_ctor_set(v___x_2828_, 1, v___y_2807_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2828_);
v___x_2830_ = v___x_2826_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2830_);
v___x_2832_ = v___x_2811_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v___y_2807_);
v_a_2837_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2808_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2808_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object* v_f_2867_, lean_object* v_decl_2868_, lean_object* v_ci_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2867_, v_decl_2868_, v_ci_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(lean_object* v_f_2880_, lean_object* v_keys_2881_, lean_object* v_vals_2882_, lean_object* v_i_2883_, lean_object* v_acc_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = lean_array_get_size(v_keys_2881_);
v___x_2895_ = lean_nat_dec_lt(v_i_2883_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec(v_i_2883_);
lean_dec_ref(v_f_2880_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_acc_2884_);
lean_ctor_set(v___x_2896_, 1, v___y_2885_);
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
else
{
lean_object* v_k_2899_; lean_object* v_v_2900_; lean_object* v___x_2901_; 
v_k_2899_ = lean_array_fget_borrowed(v_keys_2881_, v_i_2883_);
v_v_2900_ = lean_array_fget_borrowed(v_vals_2882_, v_i_2883_);
lean_inc_ref(v_f_2880_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc(v_v_2900_);
lean_inc(v_k_2899_);
v___x_2901_ = lean_apply_12(v_f_2880_, v_acc_2884_, v_k_2899_, v_v_2900_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, lean_box(0));
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
if (lean_obj_tag(v_a_2902_) == 0)
{
lean_dec_ref_known(v_a_2902_, 1);
lean_dec(v_i_2883_);
lean_dec_ref(v_f_2880_);
return v___x_2901_;
}
else
{
lean_object* v_a_2903_; lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec_ref_known(v___x_2901_, 1);
v_a_2903_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v_a_2902_, 1);
v_fst_2904_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_fst_2904_);
v_snd_2905_ = lean_ctor_get(v_a_2903_, 1);
lean_inc(v_snd_2905_);
lean_dec(v_a_2903_);
v___x_2906_ = lean_unsigned_to_nat(1u);
v___x_2907_ = lean_nat_add(v_i_2883_, v___x_2906_);
lean_dec(v_i_2883_);
v_i_2883_ = v___x_2907_;
v_acc_2884_ = v_fst_2904_;
v___y_2885_ = v_snd_2905_;
goto _start;
}
}
else
{
lean_dec(v_i_2883_);
lean_dec_ref(v_f_2880_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg___boxed(lean_object* v_f_2909_, lean_object* v_keys_2910_, lean_object* v_vals_2911_, lean_object* v_i_2912_, lean_object* v_acc_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2909_, v_keys_2910_, v_vals_2911_, v_i_2912_, v_acc_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec_ref(v_vals_2911_);
lean_dec_ref(v_keys_2910_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(lean_object* v_f_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
if (lean_obj_tag(v_x_2925_) == 0)
{
lean_object* v_es_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2960_; 
v_es_2936_ = lean_ctor_get(v_x_2925_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_x_2925_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2938_ = v_x_2925_;
v_isShared_2939_ = v_isSharedCheck_2960_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_es_2936_);
lean_dec(v_x_2925_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2960_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_array_get_size(v_es_2936_);
v___x_2942_ = lean_nat_dec_lt(v___x_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
lean_dec_ref(v_es_2936_);
lean_dec_ref(v_f_2924_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v_x_2926_);
lean_ctor_set(v___x_2943_, 1, v___y_2927_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set_tag(v___x_2938_, 1);
lean_ctor_set(v___x_2938_, 0, v___x_2943_);
v___x_2945_ = v___x_2938_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
return v___x_2946_;
}
}
else
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_nat_dec_le(v___x_2941_, v___x_2941_);
if (v___x_2948_ == 0)
{
if (v___x_2942_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
lean_dec_ref(v_es_2936_);
lean_dec_ref(v_f_2924_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v_x_2926_);
lean_ctor_set(v___x_2949_, 1, v___y_2927_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set_tag(v___x_2938_, 1);
lean_ctor_set(v___x_2938_, 0, v___x_2949_);
v___x_2951_ = v___x_2938_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
else
{
size_t v___x_2954_; size_t v___x_2955_; lean_object* v___x_2956_; 
lean_del_object(v___x_2938_);
v___x_2954_ = ((size_t)0ULL);
v___x_2955_ = lean_usize_of_nat(v___x_2941_);
v___x_2956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2924_, v_es_2936_, v___x_2954_, v___x_2955_, v_x_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec_ref(v_es_2936_);
return v___x_2956_;
}
}
else
{
size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
lean_del_object(v___x_2938_);
v___x_2957_ = ((size_t)0ULL);
v___x_2958_ = lean_usize_of_nat(v___x_2941_);
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2924_, v_es_2936_, v___x_2957_, v___x_2958_, v_x_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec_ref(v_es_2936_);
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_ks_2961_; lean_object* v_vs_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_ks_2961_ = lean_ctor_get(v_x_2925_, 0);
lean_inc_ref(v_ks_2961_);
v_vs_2962_ = lean_ctor_get(v_x_2925_, 1);
lean_inc_ref(v_vs_2962_);
lean_dec_ref_known(v_x_2925_, 2);
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2924_, v_ks_2961_, v_vs_2962_, v___x_2963_, v_x_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec_ref(v_vs_2962_);
lean_dec_ref(v_ks_2961_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(lean_object* v_f_2965_, lean_object* v_as_2966_, size_t v_i_2967_, size_t v_stop_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___y_2986_; uint8_t v___x_2991_; 
v___x_2991_ = lean_usize_dec_eq(v_i_2967_, v_stop_2968_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_array_uget_borrowed(v_as_2966_, v_i_2967_);
switch(lean_obj_tag(v___x_2992_))
{
case 0:
{
lean_object* v_key_2993_; lean_object* v_val_2994_; lean_object* v___x_2995_; 
v_key_2993_ = lean_ctor_get(v___x_2992_, 0);
v_val_2994_ = lean_ctor_get(v___x_2992_, 1);
lean_inc_ref(v_f_2965_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc_ref(v___y_2973_);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
lean_inc(v_val_2994_);
lean_inc(v_key_2993_);
v___x_2995_ = lean_apply_12(v_f_2965_, v_b_2969_, v_key_2993_, v_val_2994_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, lean_box(0));
v___y_2986_ = v___x_2995_;
goto v___jp_2985_;
}
case 1:
{
lean_object* v_node_2996_; lean_object* v___x_2997_; 
v_node_2996_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_node_2996_);
lean_inc_ref(v_f_2965_);
v___x_2997_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_2965_, v_node_2996_, v_b_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
v___y_2986_ = v___x_2997_;
goto v___jp_2985_;
}
default: 
{
v_fst_2980_ = v_b_2969_;
v_snd_2981_ = v___y_2970_;
goto v___jp_2979_;
}
}
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec_ref(v_f_2965_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2969_);
lean_ctor_set(v___x_2998_, 1, v___y_2970_);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
v___jp_2979_:
{
size_t v___x_2982_; size_t v___x_2983_; 
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2967_, v___x_2982_);
v_i_2967_ = v___x_2983_;
v_b_2969_ = v_fst_2980_;
v___y_2970_ = v_snd_2981_;
goto _start;
}
v___jp_2985_:
{
if (lean_obj_tag(v___y_2986_) == 0)
{
lean_object* v_a_2987_; 
v_a_2987_ = lean_ctor_get(v___y_2986_, 0);
if (lean_obj_tag(v_a_2987_) == 0)
{
lean_dec_ref(v_f_2965_);
return v___y_2986_;
}
else
{
lean_object* v_a_2988_; lean_object* v_fst_2989_; lean_object* v_snd_2990_; 
lean_inc_ref(v_a_2987_);
lean_dec_ref_known(v___y_2986_, 1);
v_a_2988_ = lean_ctor_get(v_a_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v_a_2987_, 1);
v_fst_2989_ = lean_ctor_get(v_a_2988_, 0);
lean_inc(v_fst_2989_);
v_snd_2990_ = lean_ctor_get(v_a_2988_, 1);
lean_inc(v_snd_2990_);
lean_dec(v_a_2988_);
v_fst_2980_ = v_fst_2989_;
v_snd_2981_ = v_snd_2990_;
goto v___jp_2979_;
}
}
else
{
lean_dec_ref(v_f_2965_);
return v___y_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg___boxed(lean_object* v_f_3001_, lean_object* v_as_3002_, lean_object* v_i_3003_, lean_object* v_stop_3004_, lean_object* v_b_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
size_t v_i_boxed_3015_; size_t v_stop_boxed_3016_; lean_object* v_res_3017_; 
v_i_boxed_3015_ = lean_unbox_usize(v_i_3003_);
lean_dec(v_i_3003_);
v_stop_boxed_3016_ = lean_unbox_usize(v_stop_3004_);
lean_dec(v_stop_3004_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_3001_, v_as_3002_, v_i_boxed_3015_, v_stop_boxed_3016_, v_b_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v_as_3002_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg___boxed(lean_object* v_f_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_3018_, v_x_3019_, v_x_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_f_3031_, lean_object* v_x_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
lean_inc(v___y_3042_);
lean_inc_ref(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc_ref(v___y_3039_);
lean_inc_ref(v___y_3038_);
lean_inc(v___y_3037_);
lean_inc_ref(v___y_3036_);
v___x_3044_ = lean_apply_11(v_f_3031_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, lean_box(0));
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_f_3045_, lean_object* v_x_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_3045_, v_x_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_map_3059_, lean_object* v_f_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___f_3070_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3070_, 0, v_f_3060_);
v___x_3071_ = lean_box(0);
v___x_3072_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v___f_3070_, v_map_3059_, v___x_3071_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_map_3073_, lean_object* v_f_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3073_, v_f_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object* v_f_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref(v_f_3085_);
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_x_3086_);
lean_ctor_set(v___x_3097_, 1, v___y_3088_);
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v_key_3100_; lean_object* v_value_3101_; lean_object* v_tail_3102_; lean_object* v___x_3103_; 
v_key_3100_ = lean_ctor_get(v_x_3087_, 0);
lean_inc(v_key_3100_);
v_value_3101_ = lean_ctor_get(v_x_3087_, 1);
lean_inc(v_value_3101_);
v_tail_3102_ = lean_ctor_get(v_x_3087_, 2);
lean_inc(v_tail_3102_);
lean_dec_ref_known(v_x_3087_, 3);
lean_inc_ref(v_f_3085_);
lean_inc(v___y_3095_);
lean_inc_ref(v___y_3094_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
lean_inc_ref(v___y_3091_);
lean_inc(v___y_3090_);
lean_inc_ref(v___y_3089_);
v___x_3103_ = lean_apply_11(v_f_3085_, v_key_3100_, v_value_3101_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, lean_box(0));
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
if (lean_obj_tag(v_a_3104_) == 0)
{
lean_dec_ref_known(v_a_3104_, 1);
lean_dec(v_tail_3102_);
lean_dec_ref(v_f_3085_);
return v___x_3103_;
}
else
{
lean_object* v_a_3105_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; 
lean_dec_ref_known(v___x_3103_, 1);
v_a_3105_ = lean_ctor_get(v_a_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v_a_3104_, 1);
v_fst_3106_ = lean_ctor_get(v_a_3105_, 0);
lean_inc(v_fst_3106_);
v_snd_3107_ = lean_ctor_get(v_a_3105_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_a_3105_);
v_x_3086_ = v_fst_3106_;
v_x_3087_ = v_tail_3102_;
v___y_3088_ = v_snd_3107_;
goto _start;
}
}
else
{
lean_dec(v_tail_3102_);
lean_dec_ref(v_f_3085_);
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_f_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3109_, v_x_3110_, v_x_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(lean_object* v_f_3122_, lean_object* v_as_3123_, size_t v_i_3124_, size_t v_stop_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_usize_dec_eq(v_i_3124_, v_stop_3125_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_array_uget_borrowed(v_as_3123_, v_i_3124_);
v___x_3138_ = lean_box(0);
lean_inc(v___x_3137_);
lean_inc_ref(v_f_3122_);
v___x_3139_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3122_, v___x_3138_, v___x_3137_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
if (lean_obj_tag(v_a_3140_) == 0)
{
lean_dec_ref_known(v_a_3140_, 1);
lean_dec_ref(v_f_3122_);
return v___x_3139_;
}
else
{
lean_object* v_a_3141_; lean_object* v_fst_3142_; lean_object* v_snd_3143_; size_t v___x_3144_; size_t v___x_3145_; 
lean_dec_ref_known(v___x_3139_, 1);
v_a_3141_ = lean_ctor_get(v_a_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v_a_3140_, 1);
v_fst_3142_ = lean_ctor_get(v_a_3141_, 0);
lean_inc(v_fst_3142_);
v_snd_3143_ = lean_ctor_get(v_a_3141_, 1);
lean_inc(v_snd_3143_);
lean_dec(v_a_3141_);
v___x_3144_ = ((size_t)1ULL);
v___x_3145_ = lean_usize_add(v_i_3124_, v___x_3144_);
v_i_3124_ = v___x_3145_;
v_b_3126_ = v_fst_3142_;
v___y_3127_ = v_snd_3143_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_3122_);
return v___x_3139_;
}
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec_ref(v_f_3122_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_b_3126_);
lean_ctor_set(v___x_3147_, 1, v___y_3127_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4___boxed(lean_object* v_f_3150_, lean_object* v_as_3151_, lean_object* v_i_3152_, lean_object* v_stop_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
size_t v_i_boxed_3164_; size_t v_stop_boxed_3165_; lean_object* v_res_3166_; 
v_i_boxed_3164_ = lean_unbox_usize(v_i_3152_);
lean_dec(v_i_3152_);
v_stop_boxed_3165_ = lean_unbox_usize(v_stop_3153_);
lean_dec(v_stop_3153_);
v_res_3166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3150_, v_as_3151_, v_i_boxed_3164_, v_stop_boxed_3165_, v_b_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v_as_3151_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object* v_env_3167_, lean_object* v_f_3168_, lean_object* v_name_3169_, lean_object* v_c_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v___x_3180_; 
lean_inc(v_name_3169_);
v___x_3180_ = l_Lean_Meta_allowCompletion(v_env_3167_, v_name_3169_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec_ref(v_c_3170_);
lean_dec(v_name_3169_);
lean_dec_ref(v_f_3168_);
v___x_3181_ = lean_box(0);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___y_3171_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_inc_ref(v_c_3170_);
v___x_3185_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionKindForDecl___boxed), 6, 1);
lean_closure_set(v___x_3185_, 0, v_c_3170_);
lean_inc(v_name_3169_);
v___x_3186_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionTagsForDecl___boxed), 6, 1);
lean_closure_set(v___x_3186_, 0, v_name_3169_);
v___x_3187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3187_, 0, v_c_3170_);
lean_ctor_set(v___x_3187_, 1, v___x_3185_);
lean_ctor_set(v___x_3187_, 2, v___x_3186_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc_ref(v___y_3174_);
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
v___x_3188_ = lean_apply_11(v_f_3168_, v_name_3169_, v___x_3187_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, lean_box(0));
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object* v_env_3189_, lean_object* v_f_3190_, lean_object* v_name_3191_, lean_object* v_c_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3189_, v_f_3190_, v_name_3191_, v_c_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object* v_f_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; lean_object* v_env_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_st_ref_get(v___y_3211_);
v_env_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc_ref_n(v_env_3214_, 2);
lean_dec(v___x_3213_);
v___x_3215_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_3214_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v_buckets_3217_; lean_object* v___f_3218_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v_buckets_3217_ = lean_ctor_get(v_a_3216_, 1);
lean_inc_ref(v_buckets_3217_);
lean_dec(v_a_3216_);
lean_inc_ref(v_f_3203_);
lean_inc_ref(v_env_3214_);
v___f_3218_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3218_, 0, v_env_3214_);
lean_closure_set(v___f_3218_, 1, v_f_3203_);
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = lean_array_get_size(v_buckets_3217_);
v___x_3233_ = lean_nat_dec_lt(v___x_3231_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v_map_u2082_3235_; lean_object* v___x_3236_; 
lean_dec_ref(v_buckets_3217_);
lean_dec_ref(v_f_3203_);
v___x_3234_ = l_Lean_Environment_constants(v_env_3214_);
v_map_u2082_3235_ = lean_ctor_get(v___x_3234_, 1);
lean_inc_ref(v_map_u2082_3235_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3235_, v___f_3218_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_nat_dec_le(v___x_3232_, v___x_3232_);
if (v___x_3238_ == 0)
{
if (v___x_3233_ == 0)
{
lean_dec_ref(v_buckets_3217_);
lean_dec_ref(v_f_3203_);
v___y_3220_ = v___y_3204_;
v___y_3221_ = v___y_3205_;
v___y_3222_ = v___y_3206_;
v___y_3223_ = v___y_3207_;
v___y_3224_ = v___y_3208_;
v___y_3225_ = v___y_3209_;
v___y_3226_ = v___y_3210_;
v___y_3227_ = v___y_3211_;
goto v___jp_3219_;
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = ((size_t)0ULL);
v___x_3240_ = lean_usize_of_nat(v___x_3232_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3203_, v_buckets_3217_, v___x_3239_, v___x_3240_, v___x_3237_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v_buckets_3217_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
if (lean_obj_tag(v_a_3242_) == 0)
{
lean_dec_ref_known(v_a_3242_, 1);
lean_dec_ref(v___f_3218_);
lean_dec_ref(v_env_3214_);
return v___x_3241_;
}
else
{
lean_object* v_a_3243_; lean_object* v_snd_3244_; 
lean_dec_ref_known(v___x_3241_, 1);
v_a_3243_ = lean_ctor_get(v_a_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v_a_3242_, 1);
v_snd_3244_ = lean_ctor_get(v_a_3243_, 1);
lean_inc(v_snd_3244_);
lean_dec(v_a_3243_);
v___y_3220_ = v_snd_3244_;
v___y_3221_ = v___y_3205_;
v___y_3222_ = v___y_3206_;
v___y_3223_ = v___y_3207_;
v___y_3224_ = v___y_3208_;
v___y_3225_ = v___y_3209_;
v___y_3226_ = v___y_3210_;
v___y_3227_ = v___y_3211_;
goto v___jp_3219_;
}
}
else
{
lean_dec_ref(v___f_3218_);
lean_dec_ref(v_env_3214_);
return v___x_3241_;
}
}
}
else
{
size_t v___x_3245_; size_t v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = ((size_t)0ULL);
v___x_3246_ = lean_usize_of_nat(v___x_3232_);
v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3203_, v_buckets_3217_, v___x_3245_, v___x_3246_, v___x_3237_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v_buckets_3217_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
if (lean_obj_tag(v_a_3248_) == 0)
{
lean_dec_ref_known(v_a_3248_, 1);
lean_dec_ref(v___f_3218_);
lean_dec_ref(v_env_3214_);
return v___x_3247_;
}
else
{
lean_object* v_a_3249_; lean_object* v_snd_3250_; 
lean_dec_ref_known(v___x_3247_, 1);
v_a_3249_ = lean_ctor_get(v_a_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v_a_3248_, 1);
v_snd_3250_ = lean_ctor_get(v_a_3249_, 1);
lean_inc(v_snd_3250_);
lean_dec(v_a_3249_);
v___y_3220_ = v_snd_3250_;
v___y_3221_ = v___y_3205_;
v___y_3222_ = v___y_3206_;
v___y_3223_ = v___y_3207_;
v___y_3224_ = v___y_3208_;
v___y_3225_ = v___y_3209_;
v___y_3226_ = v___y_3210_;
v___y_3227_ = v___y_3211_;
goto v___jp_3219_;
}
}
else
{
lean_dec_ref(v___f_3218_);
lean_dec_ref(v_env_3214_);
return v___x_3247_;
}
}
}
v___jp_3219_:
{
lean_object* v___x_3228_; lean_object* v_map_u2082_3229_; lean_object* v___x_3230_; 
v___x_3228_ = l_Lean_Environment_constants(v_env_3214_);
v_map_u2082_3229_ = lean_ctor_get(v___x_3228_, 1);
lean_inc_ref(v_map_u2082_3229_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3229_, v___f_3218_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3230_;
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v_env_3214_);
lean_dec(v___y_3204_);
lean_dec_ref(v_f_3203_);
v_a_3251_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3215_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3215_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object* v_f_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object* v_f_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___f_3279_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3279_, 0, v_f_3270_);
v___x_3280_ = lean_unsigned_to_nat(0u);
v___x_3281_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v___f_3279_, v___x_3280_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3301_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3301_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3301_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
if (lean_obj_tag(v_a_3282_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3296_; 
v_a_3286_ = lean_ctor_get(v_a_3282_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_a_3282_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3288_ = v_a_3282_;
v_isShared_3289_ = v_isSharedCheck_3296_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v_a_3282_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3296_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3293_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3291_);
v___x_3293_ = v___x_3284_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
lean_dec_ref_known(v_a_3282_, 1);
v___x_3297_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3297_);
v___x_3299_ = v___x_3284_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
v_a_3302_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3281_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3281_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object* v_f_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(lean_object* v_id_3322_, uint8_t v_danglingDot_3323_, lean_object* v_as_3324_, size_t v_sz_3325_, size_t v_i_3326_, lean_object* v_b_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_usize_dec_lt(v_i_3326_, v_sz_3325_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_b_3327_);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
return v___x_3333_;
}
else
{
lean_object* v_snd_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3387_; 
v_snd_3334_ = lean_ctor_get(v_b_3327_, 1);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_b_3327_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v_b_3327_, 0);
lean_dec(v_unused_3388_);
v___x_3336_ = v_b_3327_;
v_isShared_3337_ = v_isSharedCheck_3387_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snd_3334_);
lean_dec(v_b_3327_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3387_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v_a_3340_; lean_object* v_a_3347_; 
v___x_3338_ = lean_box(0);
v_a_3347_ = lean_array_uget(v_as_3324_, v_i_3326_);
if (lean_obj_tag(v_a_3347_) == 0)
{
v_a_3340_ = v_snd_3334_;
goto v___jp_3339_;
}
else
{
lean_object* v_val_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_snd_3334_);
v_val_3348_ = lean_ctor_get(v_a_3347_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3347_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3350_ = v_a_3347_;
v_isShared_3351_ = v_isSharedCheck_3386_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_val_3348_);
lean_dec(v_a_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3386_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = l_Lean_LocalDecl_userName(v_val_3348_);
v___x_3354_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3322_, v___x_3353_, v_danglingDot_3323_);
if (v___x_3354_ == 0)
{
lean_dec(v___x_3353_);
lean_del_object(v___x_3350_);
lean_dec(v_val_3348_);
v_a_3340_ = v___x_3352_;
goto v___jp_3339_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = l_Lean_LocalDecl_fvarId(v_val_3348_);
lean_dec(v_val_3348_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3355_);
v___x_3357_ = v___x_3350_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3358_ = 5;
v___x_3359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3360_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3353_, v___x_3357_, v___x_3358_, v___x_3359_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3376_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3376_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3376_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
if (lean_obj_tag(v_a_3361_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3375_; 
lean_del_object(v___x_3336_);
v_a_3365_ = lean_ctor_get(v_a_3361_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_a_3361_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3367_ = v_a_3361_;
v_isShared_3368_ = v_isSharedCheck_3375_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v_a_3361_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3375_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3372_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3370_);
v___x_3372_ = v___x_3363_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3361_, 1);
lean_del_object(v___x_3363_);
v_a_3340_ = v___x_3352_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_del_object(v___x_3336_);
v_a_3377_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3360_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3360_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
}
}
v___jp_3339_:
{
lean_object* v___x_3342_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v_a_3340_);
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3342_ = v___x_3336_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_a_3340_);
v___x_3342_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
size_t v___x_3343_; size_t v___x_3344_; 
v___x_3343_ = ((size_t)1ULL);
v___x_3344_ = lean_usize_add(v_i_3326_, v___x_3343_);
v_i_3326_ = v___x_3344_;
v_b_3327_ = v___x_3342_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___boxed(lean_object* v_id_3389_, lean_object* v_danglingDot_3390_, lean_object* v_as_3391_, lean_object* v_sz_3392_, lean_object* v_i_3393_, lean_object* v_b_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
uint8_t v_danglingDot_boxed_3398_; size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_danglingDot_boxed_3398_ = lean_unbox(v_danglingDot_3390_);
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3392_);
lean_dec(v_sz_3392_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3393_);
lean_dec(v_i_3393_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3389_, v_danglingDot_boxed_3398_, v_as_3391_, v_sz_boxed_3399_, v_i_boxed_3400_, v_b_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v_as_3391_);
lean_dec(v_id_3389_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(lean_object* v_id_3402_, uint8_t v_danglingDot_3403_, lean_object* v_as_3404_, size_t v_sz_3405_, size_t v_i_3406_, lean_object* v_b_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_lt(v_i_3406_, v_sz_3405_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_b_3407_);
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v_snd_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3472_; 
v_snd_3419_ = lean_ctor_get(v_b_3407_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_b_3407_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v_b_3407_, 0);
lean_dec(v_unused_3473_);
v___x_3421_ = v_b_3407_;
v_isShared_3422_ = v_isSharedCheck_3472_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3419_);
lean_dec(v_b_3407_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3472_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v_a_3425_; lean_object* v_a_3432_; 
v___x_3423_ = lean_box(0);
v_a_3432_ = lean_array_uget(v_as_3404_, v_i_3406_);
if (lean_obj_tag(v_a_3432_) == 0)
{
v_a_3425_ = v_snd_3419_;
goto v___jp_3424_;
}
else
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_snd_3419_);
v_val_3433_ = lean_ctor_get(v_a_3432_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3435_ = v_a_3432_;
v_isShared_3436_ = v_isSharedCheck_3471_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v_a_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3471_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3437_ = lean_box(0);
v___x_3438_ = l_Lean_LocalDecl_userName(v_val_3433_);
v___x_3439_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3402_, v___x_3438_, v_danglingDot_3403_);
if (v___x_3439_ == 0)
{
lean_dec(v___x_3438_);
lean_del_object(v___x_3435_);
lean_dec(v_val_3433_);
v_a_3425_ = v___x_3437_;
goto v___jp_3424_;
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = l_Lean_LocalDecl_fvarId(v_val_3433_);
lean_dec(v_val_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3440_);
v___x_3442_ = v___x_3435_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = 5;
v___x_3444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3445_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3438_, v___x_3442_, v___x_3443_, v___x_3444_, v___y_3408_, v___y_3409_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3461_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3461_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3461_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
if (lean_obj_tag(v_a_3446_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3460_; 
lean_del_object(v___x_3421_);
v_a_3450_ = lean_ctor_get(v_a_3446_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_a_3446_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3452_ = v_a_3446_;
v_isShared_3453_ = v_isSharedCheck_3460_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v_a_3446_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3460_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3455_);
v___x_3457_ = v___x_3448_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3446_, 1);
lean_del_object(v___x_3448_);
v_a_3425_ = v___x_3437_;
goto v___jp_3424_;
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_del_object(v___x_3421_);
v_a_3462_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3445_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3445_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
}
v___jp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v_a_3425_);
lean_ctor_set(v___x_3421_, 0, v___x_3423_);
v___x_3427_ = v___x_3421_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_a_3425_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
size_t v___x_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = ((size_t)1ULL);
v___x_3429_ = lean_usize_add(v_i_3406_, v___x_3428_);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3402_, v_danglingDot_3403_, v_as_3404_, v_sz_3405_, v___x_3429_, v___x_3427_, v___y_3408_, v___y_3409_);
return v___x_3430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17___boxed(lean_object* v_id_3474_, lean_object* v_danglingDot_3475_, lean_object* v_as_3476_, lean_object* v_sz_3477_, lean_object* v_i_3478_, lean_object* v_b_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
uint8_t v_danglingDot_boxed_3488_; size_t v_sz_boxed_3489_; size_t v_i_boxed_3490_; lean_object* v_res_3491_; 
v_danglingDot_boxed_3488_ = lean_unbox(v_danglingDot_3475_);
v_sz_boxed_3489_ = lean_unbox_usize(v_sz_3477_);
lean_dec(v_sz_3477_);
v_i_boxed_3490_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_res_3491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3474_, v_danglingDot_boxed_3488_, v_as_3476_, v_sz_boxed_3489_, v_i_boxed_3490_, v_b_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v_as_3476_);
lean_dec(v_id_3474_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object* v_init_3492_, lean_object* v_id_3493_, uint8_t v_danglingDot_3494_, lean_object* v_n_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
if (lean_obj_tag(v_n_3495_) == 0)
{
lean_object* v_cs_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; size_t v_sz_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v_cs_3505_ = lean_ctor_get(v_n_3495_, 0);
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v_b_3496_);
v_sz_3508_ = lean_array_size(v_cs_3505_);
v___x_3509_ = ((size_t)0ULL);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3492_, v_id_3493_, v_danglingDot_3494_, v_cs_3505_, v_sz_3508_, v___x_3509_, v___x_3507_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3547_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3547_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3510_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3547_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
if (lean_obj_tag(v_a_3511_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3525_; 
v_a_3515_ = lean_ctor_get(v_a_3511_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_a_3511_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3517_ = v_a_3511_;
v_isShared_3518_ = v_isSharedCheck_3525_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v_a_3511_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3525_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3520_);
v___x_3522_ = v___x_3513_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3546_; 
v_a_3526_ = lean_ctor_get(v_a_3511_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_a_3511_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3528_ = v_a_3511_;
v_isShared_3529_ = v_isSharedCheck_3546_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v_a_3511_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3546_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_fst_3530_; 
v_fst_3530_ = lean_ctor_get(v_a_3526_, 0);
if (lean_obj_tag(v_fst_3530_) == 0)
{
lean_object* v_snd_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v_snd_3531_ = lean_ctor_get(v_a_3526_, 1);
lean_inc(v_snd_3531_);
lean_dec(v_a_3526_);
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_snd_3531_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3532_);
v___x_3534_ = v___x_3528_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3534_);
v___x_3536_ = v___x_3513_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v_val_3539_; lean_object* v___x_3541_; 
lean_inc_ref(v_fst_3530_);
lean_dec(v_a_3526_);
v_val_3539_ = lean_ctor_get(v_fst_3530_, 0);
lean_inc(v_val_3539_);
lean_dec_ref_known(v_fst_3530_, 1);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v_val_3539_);
v___x_3541_ = v___x_3528_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_val_3539_);
v___x_3541_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3541_);
v___x_3543_ = v___x_3513_;
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
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3510_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3510_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_vs_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; size_t v_sz_3559_; size_t v___x_3560_; lean_object* v___x_3561_; 
v_vs_3556_ = lean_ctor_get(v_n_3495_, 0);
v___x_3557_ = lean_box(0);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
lean_ctor_set(v___x_3558_, 1, v_b_3496_);
v_sz_3559_ = lean_array_size(v_vs_3556_);
v___x_3560_ = ((size_t)0ULL);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3493_, v_danglingDot_3494_, v_vs_3556_, v_sz_3559_, v___x_3560_, v___x_3558_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3598_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3598_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3598_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
if (lean_obj_tag(v_a_3562_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3576_; 
v_a_3566_ = lean_ctor_get(v_a_3562_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_a_3562_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3568_ = v_a_3562_;
v_isShared_3569_ = v_isSharedCheck_3576_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v_a_3562_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3576_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3571_);
v___x_3573_ = v___x_3564_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3597_; 
v_a_3577_ = lean_ctor_get(v_a_3562_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3562_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3579_ = v_a_3562_;
v_isShared_3580_ = v_isSharedCheck_3597_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v_a_3562_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3597_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_fst_3581_; 
v_fst_3581_ = lean_ctor_get(v_a_3577_, 0);
if (lean_obj_tag(v_fst_3581_) == 0)
{
lean_object* v_snd_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v_snd_3582_ = lean_ctor_get(v_a_3577_, 1);
lean_inc(v_snd_3582_);
lean_dec(v_a_3577_);
v___x_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3583_, 0, v_snd_3582_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3583_);
v___x_3585_ = v___x_3579_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3585_);
v___x_3587_ = v___x_3564_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
else
{
lean_object* v_val_3590_; lean_object* v___x_3592_; 
lean_inc_ref(v_fst_3581_);
lean_dec(v_a_3577_);
v_val_3590_ = lean_ctor_get(v_fst_3581_, 0);
lean_inc(v_val_3590_);
lean_dec_ref_known(v_fst_3581_, 1);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v_val_3590_);
v___x_3592_ = v___x_3579_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_val_3590_);
v___x_3592_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3592_);
v___x_3594_ = v___x_3564_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v_a_3599_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3561_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3561_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(lean_object* v_init_3607_, lean_object* v_id_3608_, uint8_t v_danglingDot_3609_, lean_object* v_as_3610_, size_t v_sz_3611_, size_t v_i_3612_, lean_object* v_b_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
uint8_t v___x_3622_; 
v___x_3622_ = lean_usize_dec_lt(v_i_3612_, v_sz_3611_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3623_, 0, v_b_3613_);
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
return v___x_3624_;
}
else
{
lean_object* v_snd_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3678_; 
v_snd_3625_ = lean_ctor_get(v_b_3613_, 1);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_b_3613_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; 
v_unused_3679_ = lean_ctor_get(v_b_3613_, 0);
lean_dec(v_unused_3679_);
v___x_3627_ = v_b_3613_;
v_isShared_3628_ = v_isSharedCheck_3678_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_snd_3625_);
lean_dec(v_b_3613_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3678_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_a_3629_; lean_object* v___x_3630_; 
v_a_3629_ = lean_array_uget_borrowed(v_as_3610_, v_i_3612_);
lean_inc(v_snd_3625_);
v___x_3630_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3607_, v_id_3608_, v_danglingDot_3609_, v_a_3629_, v_snd_3625_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3669_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3669_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3669_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
if (lean_obj_tag(v_a_3631_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3645_; 
lean_del_object(v___x_3627_);
lean_dec(v_snd_3625_);
v_a_3635_ = lean_ctor_get(v_a_3631_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3637_ = v_a_3631_;
v_isShared_3638_ = v_isSharedCheck_3645_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v_a_3631_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3645_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3642_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3640_);
v___x_3642_ = v___x_3633_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3668_; 
v_a_3646_ = lean_ctor_get(v_a_3631_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3648_ = v_a_3631_;
v_isShared_3649_ = v_isSharedCheck_3668_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v_a_3631_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3668_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
if (lean_obj_tag(v_a_3646_) == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_a_3646_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3650_);
v___x_3652_ = v___x_3627_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_snd_3625_);
v___x_3652_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3652_);
v___x_3654_ = v___x_3648_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3654_);
v___x_3656_ = v___x_3633_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
lean_del_object(v___x_3648_);
lean_del_object(v___x_3633_);
lean_dec(v_snd_3625_);
v_a_3660_ = lean_ctor_get(v_a_3646_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v_a_3646_, 1);
v___x_3661_ = lean_box(0);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 1, v_a_3660_);
lean_ctor_set(v___x_3627_, 0, v___x_3661_);
v___x_3663_ = v___x_3627_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_a_3660_);
v___x_3663_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
size_t v___x_3664_; size_t v___x_3665_; 
v___x_3664_ = ((size_t)1ULL);
v___x_3665_ = lean_usize_add(v_i_3612_, v___x_3664_);
v_i_3612_ = v___x_3665_;
v_b_3613_ = v___x_3663_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_del_object(v___x_3627_);
lean_dec(v_snd_3625_);
v_a_3670_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3630_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3630_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16___boxed(lean_object* v_init_3680_, lean_object* v_id_3681_, lean_object* v_danglingDot_3682_, lean_object* v_as_3683_, lean_object* v_sz_3684_, lean_object* v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
uint8_t v_danglingDot_boxed_3695_; size_t v_sz_boxed_3696_; size_t v_i_boxed_3697_; lean_object* v_res_3698_; 
v_danglingDot_boxed_3695_ = lean_unbox(v_danglingDot_3682_);
v_sz_boxed_3696_ = lean_unbox_usize(v_sz_3684_);
lean_dec(v_sz_3684_);
v_i_boxed_3697_ = lean_unbox_usize(v_i_3685_);
lean_dec(v_i_3685_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3680_, v_id_3681_, v_danglingDot_boxed_3695_, v_as_3683_, v_sz_boxed_3696_, v_i_boxed_3697_, v_b_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_as_3683_);
lean_dec(v_id_3681_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object* v_init_3699_, lean_object* v_id_3700_, lean_object* v_danglingDot_3701_, lean_object* v_n_3702_, lean_object* v_b_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
uint8_t v_danglingDot_boxed_3712_; lean_object* v_res_3713_; 
v_danglingDot_boxed_3712_ = lean_unbox(v_danglingDot_3701_);
v_res_3713_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3699_, v_id_3700_, v_danglingDot_boxed_3712_, v_n_3702_, v_b_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_n_3702_);
lean_dec(v_id_3700_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(lean_object* v_id_3714_, uint8_t v_danglingDot_3715_, lean_object* v_as_3716_, size_t v_sz_3717_, size_t v_i_3718_, lean_object* v_b_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_usize_dec_lt(v_i_3718_, v_sz_3717_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3724_, 0, v_b_3719_);
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
return v___x_3725_;
}
else
{
lean_object* v_snd_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3779_; 
v_snd_3726_ = lean_ctor_get(v_b_3719_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_b_3719_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v_b_3719_, 0);
lean_dec(v_unused_3780_);
v___x_3728_ = v_b_3719_;
v_isShared_3729_ = v_isSharedCheck_3779_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_snd_3726_);
lean_dec(v_b_3719_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3779_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3730_; lean_object* v_a_3732_; lean_object* v_a_3739_; 
v___x_3730_ = lean_box(0);
v_a_3739_ = lean_array_uget(v_as_3716_, v_i_3718_);
if (lean_obj_tag(v_a_3739_) == 0)
{
v_a_3732_ = v_snd_3726_;
goto v___jp_3731_;
}
else
{
lean_object* v_val_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v_snd_3726_);
v_val_3740_ = lean_ctor_get(v_a_3739_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_a_3739_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3742_ = v_a_3739_;
v_isShared_3743_ = v_isSharedCheck_3778_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_val_3740_);
lean_dec(v_a_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3778_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3744_ = lean_box(0);
v___x_3745_ = l_Lean_LocalDecl_userName(v_val_3740_);
v___x_3746_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3714_, v___x_3745_, v_danglingDot_3715_);
if (v___x_3746_ == 0)
{
lean_dec(v___x_3745_);
lean_del_object(v___x_3742_);
lean_dec(v_val_3740_);
v_a_3732_ = v___x_3744_;
goto v___jp_3731_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = l_Lean_LocalDecl_fvarId(v_val_3740_);
lean_dec(v_val_3740_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3747_);
v___x_3749_ = v___x_3742_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
uint8_t v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3750_ = 5;
v___x_3751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3752_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3745_, v___x_3749_, v___x_3750_, v___x_3751_, v___y_3720_, v___y_3721_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3768_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3755_ = v___x_3752_;
v_isShared_3756_ = v_isSharedCheck_3768_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3768_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
if (lean_obj_tag(v_a_3753_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3767_; 
lean_del_object(v___x_3728_);
v_a_3757_ = lean_ctor_get(v_a_3753_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_a_3753_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3759_ = v_a_3753_;
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v_a_3753_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3764_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3762_);
v___x_3764_ = v___x_3755_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3753_, 1);
lean_del_object(v___x_3755_);
v_a_3732_ = v___x_3744_;
goto v___jp_3731_;
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3728_);
v_a_3769_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3752_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3752_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
}
}
v___jp_3731_:
{
lean_object* v___x_3734_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 1, v_a_3732_);
lean_ctor_set(v___x_3728_, 0, v___x_3730_);
v___x_3734_ = v___x_3728_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_a_3732_);
v___x_3734_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
size_t v___x_3735_; size_t v___x_3736_; 
v___x_3735_ = ((size_t)1ULL);
v___x_3736_ = lean_usize_add(v_i_3718_, v___x_3735_);
v_i_3718_ = v___x_3736_;
v_b_3719_ = v___x_3734_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_id_3781_, lean_object* v_danglingDot_3782_, lean_object* v_as_3783_, lean_object* v_sz_3784_, lean_object* v_i_3785_, lean_object* v_b_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
uint8_t v_danglingDot_boxed_3790_; size_t v_sz_boxed_3791_; size_t v_i_boxed_3792_; lean_object* v_res_3793_; 
v_danglingDot_boxed_3790_ = lean_unbox(v_danglingDot_3782_);
v_sz_boxed_3791_ = lean_unbox_usize(v_sz_3784_);
lean_dec(v_sz_3784_);
v_i_boxed_3792_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_res_3793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3781_, v_danglingDot_boxed_3790_, v_as_3783_, v_sz_boxed_3791_, v_i_boxed_3792_, v_b_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v_as_3783_);
lean_dec(v_id_3781_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(lean_object* v_id_3794_, uint8_t v_danglingDot_3795_, lean_object* v_as_3796_, size_t v_sz_3797_, size_t v_i_3798_, lean_object* v_b_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
uint8_t v___x_3808_; 
v___x_3808_ = lean_usize_dec_lt(v_i_3798_, v_sz_3797_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v_b_3799_);
v___x_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
return v___x_3810_;
}
else
{
lean_object* v_snd_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3864_; 
v_snd_3811_ = lean_ctor_get(v_b_3799_, 1);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_b_3799_);
if (v_isSharedCheck_3864_ == 0)
{
lean_object* v_unused_3865_; 
v_unused_3865_ = lean_ctor_get(v_b_3799_, 0);
lean_dec(v_unused_3865_);
v___x_3813_ = v_b_3799_;
v_isShared_3814_ = v_isSharedCheck_3864_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_snd_3811_);
lean_dec(v_b_3799_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3864_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; lean_object* v_a_3817_; lean_object* v_a_3824_; 
v___x_3815_ = lean_box(0);
v_a_3824_ = lean_array_uget(v_as_3796_, v_i_3798_);
if (lean_obj_tag(v_a_3824_) == 0)
{
v_a_3817_ = v_snd_3811_;
goto v___jp_3816_;
}
else
{
lean_object* v_val_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3863_; 
lean_dec(v_snd_3811_);
v_val_3825_ = lean_ctor_get(v_a_3824_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_a_3824_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3827_ = v_a_3824_;
v_isShared_3828_ = v_isSharedCheck_3863_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_val_3825_);
lean_dec(v_a_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3863_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3829_ = lean_box(0);
v___x_3830_ = l_Lean_LocalDecl_userName(v_val_3825_);
v___x_3831_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3794_, v___x_3830_, v_danglingDot_3795_);
if (v___x_3831_ == 0)
{
lean_dec(v___x_3830_);
lean_del_object(v___x_3827_);
lean_dec(v_val_3825_);
v_a_3817_ = v___x_3829_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = l_Lean_LocalDecl_fvarId(v_val_3825_);
lean_dec(v_val_3825_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3832_);
v___x_3834_ = v___x_3827_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
uint8_t v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3835_ = 5;
v___x_3836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3837_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3830_, v___x_3834_, v___x_3835_, v___x_3836_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3853_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3853_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3853_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
if (lean_obj_tag(v_a_3838_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3852_; 
lean_del_object(v___x_3813_);
v_a_3842_ = lean_ctor_get(v_a_3838_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3838_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3844_ = v_a_3838_;
v_isShared_3845_ = v_isSharedCheck_3852_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v_a_3838_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3852_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3849_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3847_);
v___x_3849_ = v___x_3840_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3838_, 1);
lean_del_object(v___x_3840_);
v_a_3817_ = v___x_3829_;
goto v___jp_3816_;
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_del_object(v___x_3813_);
v_a_3854_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3837_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3837_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
}
}
v___jp_3816_:
{
lean_object* v___x_3819_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 1, v_a_3817_);
lean_ctor_set(v___x_3813_, 0, v___x_3815_);
v___x_3819_ = v___x_3813_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v_a_3817_);
v___x_3819_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
size_t v___x_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_add(v_i_3798_, v___x_3820_);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3794_, v_danglingDot_3795_, v_as_3796_, v_sz_3797_, v___x_3821_, v___x_3819_, v___y_3800_, v___y_3801_);
return v___x_3822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12___boxed(lean_object* v_id_3866_, lean_object* v_danglingDot_3867_, lean_object* v_as_3868_, lean_object* v_sz_3869_, lean_object* v_i_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
uint8_t v_danglingDot_boxed_3880_; size_t v_sz_boxed_3881_; size_t v_i_boxed_3882_; lean_object* v_res_3883_; 
v_danglingDot_boxed_3880_ = lean_unbox(v_danglingDot_3867_);
v_sz_boxed_3881_ = lean_unbox_usize(v_sz_3869_);
lean_dec(v_sz_3869_);
v_i_boxed_3882_ = lean_unbox_usize(v_i_3870_);
lean_dec(v_i_3870_);
v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3866_, v_danglingDot_boxed_3880_, v_as_3868_, v_sz_boxed_3881_, v_i_boxed_3882_, v_b_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec_ref(v_as_3868_);
lean_dec(v_id_3866_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object* v_id_3884_, uint8_t v_danglingDot_3885_, lean_object* v_t_3886_, lean_object* v_init_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_b_3897_; lean_object* v_root_3900_; lean_object* v_tail_3901_; lean_object* v___x_3902_; 
v_root_3900_ = lean_ctor_get(v_t_3886_, 0);
v_tail_3901_ = lean_ctor_get(v_t_3886_, 1);
v___x_3902_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3887_, v_id_3884_, v_danglingDot_3885_, v_root_3900_, v_init_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3964_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3964_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3964_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_a_3903_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3917_; 
v_a_3907_ = lean_ctor_get(v_a_3903_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_a_3903_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3909_ = v_a_3903_;
v_isShared_3910_ = v_isSharedCheck_3917_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v_a_3903_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3917_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3914_; 
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3912_);
v___x_3914_ = v___x_3905_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
else
{
lean_object* v_a_3918_; 
lean_del_object(v___x_3905_);
v_a_3918_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v_a_3903_, 1);
if (lean_obj_tag(v_a_3918_) == 0)
{
lean_object* v_a_3919_; 
v_a_3919_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v_a_3918_, 1);
v_b_3897_ = v_a_3919_;
goto v___jp_3896_;
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; size_t v_sz_3923_; size_t v___x_3924_; lean_object* v___x_3925_; 
v_a_3920_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v_a_3918_, 1);
v___x_3921_ = lean_box(0);
v___x_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v_a_3920_);
v_sz_3923_ = lean_array_size(v_tail_3901_);
v___x_3924_ = ((size_t)0ULL);
v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3884_, v_danglingDot_3885_, v_tail_3901_, v_sz_3923_, v___x_3924_, v___x_3922_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3955_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3928_ = v___x_3925_;
v_isShared_3929_ = v_isSharedCheck_3955_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3925_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3955_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
if (lean_obj_tag(v_a_3926_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3940_; 
v_a_3930_ = lean_ctor_get(v_a_3926_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_a_3926_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3932_ = v_a_3926_;
v_isShared_3933_ = v_isSharedCheck_3940_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v_a_3926_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3940_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; 
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3935_);
v___x_3937_ = v___x_3928_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3954_; 
v_a_3941_ = lean_ctor_get(v_a_3926_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_a_3926_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3943_ = v_a_3926_;
v_isShared_3944_ = v_isSharedCheck_3954_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v_a_3926_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3954_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v_fst_3945_; 
v_fst_3945_ = lean_ctor_get(v_a_3941_, 0);
if (lean_obj_tag(v_fst_3945_) == 0)
{
lean_object* v_snd_3946_; lean_object* v___x_3948_; 
v_snd_3946_ = lean_ctor_get(v_a_3941_, 1);
lean_inc(v_snd_3946_);
lean_dec(v_a_3941_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v_snd_3946_);
v___x_3948_ = v___x_3943_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_snd_3946_);
v___x_3948_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3950_; 
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3948_);
v___x_3950_ = v___x_3928_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
else
{
lean_object* v_val_3953_; 
lean_inc_ref(v_fst_3945_);
lean_del_object(v___x_3943_);
lean_dec(v_a_3941_);
lean_del_object(v___x_3928_);
v_val_3953_ = lean_ctor_get(v_fst_3945_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v_fst_3945_, 1);
v_b_3897_ = v_val_3953_;
goto v___jp_3896_;
}
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
v_a_3956_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3925_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3925_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3902_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3902_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
v___jp_3896_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3898_, 0, v_b_3897_);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object* v_id_3973_, lean_object* v_danglingDot_3974_, lean_object* v_t_3975_, lean_object* v_init_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
uint8_t v_danglingDot_boxed_3985_; lean_object* v_res_3986_; 
v_danglingDot_boxed_3985_ = lean_unbox(v_danglingDot_3974_);
v_res_3986_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_3973_, v_danglingDot_boxed_3985_, v_t_3975_, v_init_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v_t_3975_);
lean_dec(v_id_3973_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object* v_as_3987_, size_t v_sz_3988_, size_t v_i_3989_, lean_object* v_b_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_usize_dec_lt(v_i_3989_, v_sz_3988_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_b_3990_);
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
return v___x_3996_;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3998_; 
v_a_3997_ = lean_array_uget_borrowed(v_as_3987_, v_i_3989_);
lean_inc(v_a_3997_);
v___x_3998_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_3997_, v___y_3991_, v___y_3992_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
if (lean_obj_tag(v_a_3999_) == 0)
{
lean_dec_ref_known(v_a_3999_, 1);
return v___x_3998_;
}
else
{
lean_object* v___x_4000_; size_t v___x_4001_; size_t v___x_4002_; 
lean_dec_ref_known(v_a_3999_, 1);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = lean_box(0);
v___x_4001_ = ((size_t)1ULL);
v___x_4002_ = lean_usize_add(v_i_3989_, v___x_4001_);
v_i_3989_ = v___x_4002_;
v_b_3990_ = v___x_4000_;
goto _start;
}
}
else
{
return v___x_3998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object* v_as_4004_, lean_object* v_sz_4005_, lean_object* v_i_4006_, lean_object* v_b_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
size_t v_sz_boxed_4011_; size_t v_i_boxed_4012_; lean_object* v_res_4013_; 
v_sz_boxed_4011_ = lean_unbox_usize(v_sz_4005_);
lean_dec(v_sz_4005_);
v_i_boxed_4012_ = lean_unbox_usize(v_i_4006_);
lean_dec(v_i_4006_);
v_res_4013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4004_, v_sz_boxed_4011_, v_i_boxed_4012_, v_b_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v_as_4004_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object* v___x_4014_, lean_object* v_a_4015_, lean_object* v___x_4016_, lean_object* v_ns_4017_, lean_object* v_id_4018_, uint8_t v_danglingDot_4019_, lean_object* v_alias_4020_, lean_object* v_declNames_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
uint8_t v___y_4031_; uint8_t v___x_4035_; 
v___x_4035_ = l_Lean_Name_isPrefixOf(v_ns_4017_, v_alias_4020_);
if (v___x_4035_ == 0)
{
v___y_4031_ = v___x_4035_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4036_ = lean_box(0);
lean_inc(v_alias_4020_);
v___x_4037_ = l_Lean_Name_replacePrefix(v_alias_4020_, v_ns_4017_, v___x_4036_);
v___x_4038_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4018_, v___x_4037_, v_danglingDot_4019_);
lean_dec(v___x_4037_);
v___y_4031_ = v___x_4038_;
goto v___jp_4030_;
}
v___jp_4030_:
{
if (v___y_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_dec(v_declNames_4021_);
lean_dec(v_alias_4020_);
lean_dec_ref(v___x_4016_);
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4014_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
else
{
lean_object* v___x_4034_; 
v___x_4034_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4015_, v___x_4016_, v_alias_4020_, v_declNames_4021_, v___y_4022_, v___y_4023_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v_alias_4020_);
return v___x_4034_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_4039_, lean_object* v_a_4040_, lean_object* v___x_4041_, lean_object* v_ns_4042_, lean_object* v_id_4043_, lean_object* v_danglingDot_4044_, lean_object* v_alias_4045_, lean_object* v_declNames_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
uint8_t v_danglingDot_boxed_4055_; lean_object* v_res_4056_; 
v_danglingDot_boxed_4055_ = lean_unbox(v_danglingDot_4044_);
v_res_4056_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_4039_, v_a_4040_, v___x_4041_, v_ns_4042_, v_id_4043_, v_danglingDot_boxed_4055_, v_alias_4045_, v_declNames_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v_id_4043_);
lean_dec(v_ns_4042_);
lean_dec_ref(v_a_4040_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(lean_object* v_a_4057_, lean_object* v___x_4058_, lean_object* v_id_4059_, uint8_t v_danglingDot_4060_, lean_object* v_as_x27_4061_, lean_object* v_b_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_a_4072_; 
if (lean_obj_tag(v_as_x27_4061_) == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec(v_id_4059_);
lean_dec_ref(v___x_4058_);
lean_dec_ref(v_a_4057_);
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_b_4062_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
else
{
lean_object* v_head_4077_; lean_object* v_tail_4078_; lean_object* v___x_4079_; 
v_head_4077_ = lean_ctor_get(v_as_x27_4061_, 0);
v_tail_4078_ = lean_ctor_get(v_as_x27_4061_, 1);
v___x_4079_ = lean_box(0);
if (lean_obj_tag(v_head_4077_) == 0)
{
lean_object* v_ns_4080_; lean_object* v___x_4081_; lean_object* v___f_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v_ns_4080_ = lean_ctor_get(v_head_4077_, 0);
v___x_4081_ = lean_box(v_danglingDot_4060_);
lean_inc(v_id_4059_);
lean_inc(v_ns_4080_);
lean_inc_ref_n(v___x_4058_, 2);
lean_inc_ref(v_a_4057_);
v___f_4082_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4082_, 0, v___x_4079_);
lean_closure_set(v___f_4082_, 1, v_a_4057_);
lean_closure_set(v___f_4082_, 2, v___x_4058_);
lean_closure_set(v___f_4082_, 3, v_ns_4080_);
lean_closure_set(v___f_4082_, 4, v_id_4059_);
lean_closure_set(v___f_4082_, 5, v___x_4081_);
v___x_4083_ = l_Lean_getAliasState(v___x_4058_);
v___x_4084_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4083_, v___f_4082_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
if (lean_obj_tag(v_a_4085_) == 0)
{
lean_object* v_a_4086_; 
lean_dec(v_id_4059_);
lean_dec_ref(v___x_4058_);
lean_dec_ref(v_a_4057_);
v_a_4086_ = lean_ctor_get(v_a_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v_a_4085_, 1);
v_a_4072_ = v_a_4086_;
goto v___jp_4071_;
}
else
{
lean_dec_ref_known(v_a_4085_, 1);
v_as_x27_4061_ = v_tail_4078_;
v_b_4062_ = v___x_4079_;
goto _start;
}
}
else
{
lean_dec(v_id_4059_);
lean_dec_ref(v___x_4058_);
lean_dec_ref(v_a_4057_);
return v___x_4084_;
}
}
else
{
lean_object* v_id_4088_; lean_object* v_declName_4089_; uint8_t v___x_4090_; 
v_id_4088_ = lean_ctor_get(v_head_4077_, 0);
v_declName_4089_ = lean_ctor_get(v_head_4077_, 1);
lean_inc(v_declName_4089_);
lean_inc_ref(v___x_4058_);
v___x_4090_ = l_Lean_Server_Completion_allowCompletion(v_a_4057_, v___x_4058_, v_declName_4089_);
if (v___x_4090_ == 0)
{
v_as_x27_4061_ = v_tail_4078_;
v_b_4062_ = v___x_4079_;
goto _start;
}
else
{
uint8_t v___x_4092_; 
v___x_4092_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4059_, v_id_4088_, v_danglingDot_4060_);
if (v___x_4092_ == 0)
{
v_as_x27_4061_ = v_tail_4078_;
v_b_4062_ = v___x_4079_;
goto _start;
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4094_ = l_Lean_Name_getString_x21(v_id_4088_);
v___x_4095_ = lean_box(0);
v___x_4096_ = l_Lean_Name_str___override(v___x_4095_, v___x_4094_);
lean_inc(v_declName_4089_);
v___x_4097_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4096_, v_declName_4089_, v___y_4063_, v___y_4064_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_dec_ref_known(v___x_4097_, 1);
v_as_x27_4061_ = v_tail_4078_;
v_b_4062_ = v___x_4079_;
goto _start;
}
else
{
lean_dec(v_id_4059_);
lean_dec_ref(v___x_4058_);
lean_dec_ref(v_a_4057_);
return v___x_4097_;
}
}
}
}
}
v___jp_4071_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v_a_4072_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg___boxed(lean_object* v_a_4099_, lean_object* v___x_4100_, lean_object* v_id_4101_, lean_object* v_danglingDot_4102_, lean_object* v_as_x27_4103_, lean_object* v_b_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
uint8_t v_danglingDot_boxed_4113_; lean_object* v_res_4114_; 
v_danglingDot_boxed_4113_ = lean_unbox(v_danglingDot_4102_);
v_res_4114_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4099_, v___x_4100_, v_id_4101_, v_danglingDot_boxed_4113_, v_as_x27_4103_, v_b_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v_as_x27_4103_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_id_4115_, uint8_t v_danglingDot_4116_, lean_object* v_a_4117_, lean_object* v___x_4118_, lean_object* v_as_4119_, lean_object* v_as_x27_4120_, lean_object* v_b_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_a_4131_; 
if (lean_obj_tag(v_as_x27_4120_) == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v___x_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_id_4115_);
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_b_4121_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
else
{
lean_object* v_head_4136_; lean_object* v_tail_4137_; lean_object* v___x_4138_; 
v_head_4136_ = lean_ctor_get(v_as_x27_4120_, 0);
v_tail_4137_ = lean_ctor_get(v_as_x27_4120_, 1);
v___x_4138_ = lean_box(0);
if (lean_obj_tag(v_head_4136_) == 0)
{
lean_object* v_ns_4139_; lean_object* v___x_4140_; lean_object* v___f_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v_ns_4139_ = lean_ctor_get(v_head_4136_, 0);
v___x_4140_ = lean_box(v_danglingDot_4116_);
lean_inc(v_id_4115_);
lean_inc(v_ns_4139_);
lean_inc_ref_n(v___x_4118_, 2);
lean_inc_ref(v_a_4117_);
v___f_4141_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4141_, 0, v___x_4138_);
lean_closure_set(v___f_4141_, 1, v_a_4117_);
lean_closure_set(v___f_4141_, 2, v___x_4118_);
lean_closure_set(v___f_4141_, 3, v_ns_4139_);
lean_closure_set(v___f_4141_, 4, v_id_4115_);
lean_closure_set(v___f_4141_, 5, v___x_4140_);
v___x_4142_ = l_Lean_getAliasState(v___x_4118_);
v___x_4143_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4142_, v___f_4141_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
if (lean_obj_tag(v_a_4144_) == 0)
{
lean_object* v_a_4145_; 
lean_dec_ref(v___x_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_id_4115_);
v_a_4145_ = lean_ctor_get(v_a_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v_a_4144_, 1);
v_a_4131_ = v_a_4145_;
goto v___jp_4130_;
}
else
{
lean_object* v___x_4146_; 
lean_dec_ref_known(v_a_4144_, 1);
v___x_4146_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4117_, v___x_4118_, v_id_4115_, v_danglingDot_4116_, v_tail_4137_, v___x_4138_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4146_;
}
}
else
{
lean_dec_ref(v___x_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_id_4115_);
return v___x_4143_;
}
}
else
{
lean_object* v_id_4147_; lean_object* v_declName_4148_; uint8_t v___x_4149_; 
v_id_4147_ = lean_ctor_get(v_head_4136_, 0);
v_declName_4148_ = lean_ctor_get(v_head_4136_, 1);
lean_inc(v_declName_4148_);
lean_inc_ref(v___x_4118_);
v___x_4149_ = l_Lean_Server_Completion_allowCompletion(v_a_4117_, v___x_4118_, v_declName_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; 
v___x_4150_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4117_, v___x_4118_, v_id_4115_, v_danglingDot_4116_, v_tail_4137_, v___x_4138_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4150_;
}
else
{
uint8_t v___x_4151_; 
v___x_4151_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4115_, v_id_4147_, v_danglingDot_4116_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; 
v___x_4152_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4117_, v___x_4118_, v_id_4115_, v_danglingDot_4116_, v_tail_4137_, v___x_4138_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4152_;
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = l_Lean_Name_getString_x21(v_id_4147_);
v___x_4154_ = lean_box(0);
v___x_4155_ = l_Lean_Name_str___override(v___x_4154_, v___x_4153_);
lean_inc(v_declName_4148_);
v___x_4156_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4155_, v_declName_4148_, v___y_4122_, v___y_4123_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4157_; 
lean_dec_ref_known(v___x_4156_, 1);
v___x_4157_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4117_, v___x_4118_, v_id_4115_, v_danglingDot_4116_, v_tail_4137_, v___x_4138_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4157_;
}
else
{
lean_dec_ref(v___x_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_id_4115_);
return v___x_4156_;
}
}
}
}
}
v___jp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_a_4131_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_id_4158_, lean_object* v_danglingDot_4159_, lean_object* v_a_4160_, lean_object* v___x_4161_, lean_object* v_as_4162_, lean_object* v_as_x27_4163_, lean_object* v_b_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
uint8_t v_danglingDot_boxed_4173_; lean_object* v_res_4174_; 
v_danglingDot_boxed_4173_ = lean_unbox(v_danglingDot_4159_);
v_res_4174_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4158_, v_danglingDot_boxed_4173_, v_a_4160_, v___x_4161_, v_as_4162_, v_as_x27_4163_, v_b_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v_as_x27_4163_);
lean_dec(v_as_4162_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4175_, lean_object* v_stx_4176_, lean_object* v_id_4177_, lean_object* v_hoverInfo_4178_, uint8_t v_danglingDot_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; uint8_t v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v_id_4240_; uint8_t v_danglingDot_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v_id_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; uint8_t v___x_4271_; 
v___x_4271_ = l_Lean_Name_hasMacroScopes(v_id_4177_);
if (v___x_4271_ == 0)
{
v_id_4260_ = v_id_4177_;
v___y_4261_ = v_a_4180_;
v___y_4262_ = v_a_4181_;
v___y_4263_ = v_a_4182_;
v___y_4264_ = v_a_4183_;
v___y_4265_ = v_a_4184_;
v___y_4266_ = v_a_4185_;
v___y_4267_ = v_a_4186_;
goto v___jp_4259_;
}
else
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Syntax_getHeadInfo(v_stx_4176_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_id_4273_; 
lean_dec_ref_known(v___x_4272_, 4);
v_id_4273_ = lean_erase_macro_scopes(v_id_4177_);
v_id_4260_ = v_id_4273_;
v___y_4261_ = v_a_4180_;
v___y_4262_ = v_a_4181_;
v___y_4263_ = v_a_4182_;
v___y_4264_ = v_a_4183_;
v___y_4265_ = v_a_4184_;
v___y_4266_ = v_a_4185_;
v___y_4267_ = v_a_4186_;
goto v___jp_4259_;
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec(v___x_4272_);
lean_dec(v_hoverInfo_4178_);
lean_dec(v_id_4177_);
lean_dec_ref(v_ctx_4175_);
v___x_4274_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
}
v___jp_4188_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_st_ref_get(v___y_4199_);
v___x_4201_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4196_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
if (lean_obj_tag(v_a_4202_) == 0)
{
lean_dec_ref_known(v_a_4202_, 1);
lean_dec(v___x_4200_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4201_;
}
else
{
lean_object* v___x_4203_; lean_object* v_a_4204_; 
lean_dec_ref_known(v_a_4202_, 1);
lean_dec_ref_known(v___x_4201_, 1);
v___x_4203_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4198_);
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
if (lean_obj_tag(v_a_4204_) == 0)
{
lean_dec_ref_known(v_a_4204_, 1);
lean_dec(v___x_4200_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4203_;
}
else
{
lean_object* v_env_4205_; lean_object* v___x_4206_; 
lean_dec_ref_known(v_a_4204_, 1);
lean_dec_ref(v___x_4203_);
v_env_4205_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_ref_n(v_env_4205_, 2);
lean_dec(v___x_4200_);
v___x_4206_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4205_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_toCommandContextInfo_4207_; lean_object* v_a_4208_; lean_object* v_currNamespace_4209_; lean_object* v_openDecls_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_toCommandContextInfo_4207_ = lean_ctor_get(v_ctx_4175_, 0);
v_a_4208_ = lean_ctor_get(v___x_4206_, 0);
lean_inc_n(v_a_4208_, 2);
lean_dec_ref_known(v___x_4206_, 1);
v_currNamespace_4209_ = lean_ctor_get(v_toCommandContextInfo_4207_, 5);
v_openDecls_4210_ = lean_ctor_get(v_toCommandContextInfo_4207_, 6);
v___x_4211_ = lean_box(0);
lean_inc_ref(v_env_4205_);
lean_inc(v___y_4191_);
v___x_4212_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___y_4191_, v___y_4197_, v_a_4208_, v_env_4205_, v_openDecls_4210_, v_openDecls_4210_, v___x_4211_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
if (lean_obj_tag(v_a_4213_) == 0)
{
lean_dec_ref_known(v_a_4213_, 1);
lean_dec(v_a_4208_);
lean_dec_ref(v_env_4205_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4212_;
}
else
{
lean_object* v___f_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_dec_ref_known(v_a_4213_, 1);
lean_dec_ref_known(v___x_4212_, 1);
lean_inc_ref_n(v_env_4205_, 2);
v___f_4214_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4214_, 0, v_a_4208_);
lean_closure_set(v___f_4214_, 1, v_env_4205_);
lean_inc(v_currNamespace_4209_);
v___f_4215_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4215_, 0, v___y_4195_);
lean_closure_set(v___f_4215_, 1, v___f_4214_);
lean_closure_set(v___f_4215_, 2, v_currNamespace_4209_);
v___x_4216_ = l_Lean_getAliasState(v_env_4205_);
v___x_4217_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4216_, v___f_4215_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
if (lean_obj_tag(v_a_4218_) == 0)
{
lean_dec_ref_known(v_a_4218_, 1);
lean_dec_ref(v_env_4205_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4217_;
}
else
{
lean_dec_ref_known(v_a_4218_, 1);
lean_dec_ref_known(v___x_4217_, 1);
if (v___y_4197_ == 0)
{
if (lean_obj_tag(v___y_4191_) == 1)
{
lean_object* v_pre_4219_; 
v_pre_4219_ = lean_ctor_get(v___y_4191_, 0);
if (lean_obj_tag(v_pre_4219_) == 0)
{
lean_object* v_str_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; size_t v_sz_4223_; size_t v___x_4224_; lean_object* v___x_4225_; 
v_str_4220_ = lean_ctor_get(v___y_4191_, 1);
v___x_4221_ = l_Lean_Parser_getTokenTable(v_env_4205_);
v___x_4222_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4221_, v_str_4220_);
lean_dec_ref(v___x_4221_);
v_sz_4223_ = lean_array_size(v___x_4222_);
v___x_4224_ = ((size_t)0ULL);
v___x_4225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v___x_4222_, v_sz_4223_, v___x_4224_, v___x_4211_, v___y_4192_, v___y_4190_);
lean_dec_ref(v___x_4222_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
if (lean_obj_tag(v_a_4226_) == 0)
{
lean_dec_ref_known(v_a_4226_, 1);
lean_dec_ref_known(v___y_4191_, 2);
lean_dec_ref(v_ctx_4175_);
return v___x_4225_;
}
else
{
lean_object* v___x_4227_; 
lean_dec_ref_known(v_a_4226_, 1);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4175_, v___y_4191_, v___y_4197_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
return v___x_4227_;
}
}
else
{
lean_dec_ref_known(v___y_4191_, 2);
lean_dec_ref(v_ctx_4175_);
return v___x_4225_;
}
}
else
{
lean_object* v___x_4228_; 
lean_dec_ref(v_env_4205_);
v___x_4228_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4175_, v___y_4191_, v___y_4197_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
return v___x_4228_;
}
}
else
{
lean_object* v___x_4229_; 
lean_dec_ref(v_env_4205_);
v___x_4229_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4175_, v___y_4191_, v___y_4197_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
return v___x_4229_;
}
}
else
{
lean_object* v___x_4230_; 
lean_dec_ref(v_env_4205_);
v___x_4230_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4175_, v___y_4191_, v___y_4197_, v___y_4192_, v___y_4190_, v___y_4198_, v___y_4189_, v___y_4194_, v___y_4193_, v___y_4199_);
return v___x_4230_;
}
}
}
else
{
lean_dec_ref(v_env_4205_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4217_;
}
}
}
else
{
lean_dec(v_a_4208_);
lean_dec_ref(v_env_4205_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4212_;
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v_env_4205_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
v_a_4231_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4206_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4206_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4200_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4191_);
lean_dec_ref(v_ctx_4175_);
return v___x_4201_;
}
}
v___jp_4239_:
{
lean_object* v___x_4249_; lean_object* v___f_4250_; lean_object* v___x_4251_; lean_object* v___f_4252_; uint8_t v___x_4253_; 
v___x_4249_ = lean_box(v_danglingDot_4241_);
lean_inc_n(v_id_4240_, 2);
lean_inc_ref(v_ctx_4175_);
v___f_4250_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4250_, 0, v_ctx_4175_);
lean_closure_set(v___f_4250_, 1, v_id_4240_);
lean_closure_set(v___f_4250_, 2, v___x_4249_);
v___x_4251_ = lean_box(v_danglingDot_4241_);
v___f_4252_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4252_, 0, v_id_4240_);
lean_closure_set(v___f_4252_, 1, v___x_4251_);
v___x_4253_ = l_Lean_Name_isAtomic(v_id_4240_);
if (v___x_4253_ == 0)
{
v___y_4189_ = v___y_4245_;
v___y_4190_ = v___y_4243_;
v___y_4191_ = v_id_4240_;
v___y_4192_ = v___y_4242_;
v___y_4193_ = v___y_4247_;
v___y_4194_ = v___y_4246_;
v___y_4195_ = v___f_4252_;
v___y_4196_ = v___f_4250_;
v___y_4197_ = v_danglingDot_4241_;
v___y_4198_ = v___y_4244_;
v___y_4199_ = v___y_4248_;
goto v___jp_4188_;
}
else
{
lean_object* v_lctx_4254_; lean_object* v_decls_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_lctx_4254_ = lean_ctor_get(v___y_4245_, 2);
v_decls_4255_ = lean_ctor_get(v_lctx_4254_, 1);
v___x_4256_ = lean_box(0);
v___x_4257_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4240_, v_danglingDot_4241_, v_decls_4255_, v___x_4256_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
if (lean_obj_tag(v_a_4258_) == 0)
{
lean_dec_ref_known(v_a_4258_, 1);
lean_dec_ref(v___f_4252_);
lean_dec_ref(v___f_4250_);
lean_dec(v_id_4240_);
lean_dec_ref(v_ctx_4175_);
return v___x_4257_;
}
else
{
lean_dec_ref_known(v_a_4258_, 1);
lean_dec_ref_known(v___x_4257_, 1);
v___y_4189_ = v___y_4245_;
v___y_4190_ = v___y_4243_;
v___y_4191_ = v_id_4240_;
v___y_4192_ = v___y_4242_;
v___y_4193_ = v___y_4247_;
v___y_4194_ = v___y_4246_;
v___y_4195_ = v___f_4252_;
v___y_4196_ = v___f_4250_;
v___y_4197_ = v_danglingDot_4241_;
v___y_4198_ = v___y_4244_;
v___y_4199_ = v___y_4248_;
goto v___jp_4188_;
}
}
else
{
lean_dec_ref(v___f_4252_);
lean_dec_ref(v___f_4250_);
lean_dec(v_id_4240_);
lean_dec_ref(v_ctx_4175_);
return v___x_4257_;
}
}
}
v___jp_4259_:
{
if (lean_obj_tag(v_hoverInfo_4178_) == 1)
{
lean_object* v_delta_4268_; lean_object* v_id_4269_; uint8_t v_danglingDot_4270_; 
v_delta_4268_ = lean_ctor_get(v_hoverInfo_4178_, 0);
lean_inc(v_delta_4268_);
lean_dec_ref_known(v_hoverInfo_4178_, 1);
v_id_4269_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4260_, v_delta_4268_);
v_danglingDot_4270_ = 0;
v_id_4240_ = v_id_4269_;
v_danglingDot_4241_ = v_danglingDot_4270_;
v___y_4242_ = v___y_4261_;
v___y_4243_ = v___y_4262_;
v___y_4244_ = v___y_4263_;
v___y_4245_ = v___y_4264_;
v___y_4246_ = v___y_4265_;
v___y_4247_ = v___y_4266_;
v___y_4248_ = v___y_4267_;
goto v___jp_4239_;
}
else
{
lean_dec(v_hoverInfo_4178_);
v_id_4240_ = v_id_4260_;
v_danglingDot_4241_ = v_danglingDot_4179_;
v___y_4242_ = v___y_4261_;
v___y_4243_ = v___y_4262_;
v___y_4244_ = v___y_4263_;
v___y_4245_ = v___y_4264_;
v___y_4246_ = v___y_4265_;
v___y_4247_ = v___y_4266_;
v___y_4248_ = v___y_4267_;
goto v___jp_4239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4276_, lean_object* v_stx_4277_, lean_object* v_id_4278_, lean_object* v_hoverInfo_4279_, lean_object* v_danglingDot_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
uint8_t v_danglingDot_boxed_4289_; lean_object* v_res_4290_; 
v_danglingDot_boxed_4289_ = lean_unbox(v_danglingDot_4280_);
v_res_4290_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4276_, v_stx_4277_, v_id_4278_, v_hoverInfo_4279_, v_danglingDot_boxed_4289_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_stx_4277_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4291_, lean_object* v___x_4292_, lean_object* v_alias_4293_, lean_object* v_as_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4291_, v___x_4292_, v_alias_4293_, v_as_4294_, v___y_4295_, v___y_4296_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4304_, lean_object* v___x_4305_, lean_object* v_alias_4306_, lean_object* v_as_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4304_, v___x_4305_, v_alias_4306_, v_as_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v_alias_4306_);
lean_dec_ref(v_a_4304_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_00_u03b2_4317_, lean_object* v_s_4318_, lean_object* v_f_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_4318_, v_f_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_00_u03b2_4329_, lean_object* v_s_4330_, lean_object* v_f_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_00_u03b2_4329_, v_s_4330_, v_f_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_id_4341_, uint8_t v_danglingDot_4342_, lean_object* v_a_4343_, lean_object* v___x_4344_, lean_object* v_as_4345_, lean_object* v_as_x27_4346_, lean_object* v_b_4347_, lean_object* v_a_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4341_, v_danglingDot_4342_, v_a_4343_, v___x_4344_, v_as_4345_, v_as_x27_4346_, v_b_4347_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_id_4358_, lean_object* v_danglingDot_4359_, lean_object* v_a_4360_, lean_object* v___x_4361_, lean_object* v_as_4362_, lean_object* v_as_x27_4363_, lean_object* v_b_4364_, lean_object* v_a_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
uint8_t v_danglingDot_boxed_4374_; lean_object* v_res_4375_; 
v_danglingDot_boxed_4374_ = lean_unbox(v_danglingDot_4359_);
v_res_4375_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4358_, v_danglingDot_boxed_4374_, v_a_4360_, v___x_4361_, v_as_4362_, v_as_x27_4363_, v_b_4364_, v_a_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v_as_x27_4363_);
lean_dec(v_as_4362_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_as_4376_, size_t v_sz_4377_, size_t v_i_4378_, lean_object* v_b_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4376_, v_sz_4377_, v_i_4378_, v_b_4379_, v___y_4380_, v___y_4381_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_as_4389_, lean_object* v_sz_4390_, lean_object* v_i_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
size_t v_sz_boxed_4401_; size_t v_i_boxed_4402_; lean_object* v_res_4403_; 
v_sz_boxed_4401_ = lean_unbox_usize(v_sz_4390_);
lean_dec(v_sz_4390_);
v_i_boxed_4402_ = lean_unbox_usize(v_i_4391_);
lean_dec(v_i_4391_);
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4389_, v_sz_boxed_4401_, v_i_boxed_4402_, v_b_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec_ref(v_as_4389_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_00_u03b2_4404_, lean_object* v_f_4405_, lean_object* v_x_4406_, lean_object* v_x_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_4405_, v_x_4406_, v_x_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4417_, lean_object* v_f_4418_, lean_object* v_x_4419_, lean_object* v_x_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_00_u03b2_4417_, v_f_4418_, v_x_4419_, v_x_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object* v_00_u03b2_4430_, lean_object* v_map_4431_, lean_object* v_f_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_4431_, v_f_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4442_, lean_object* v_map_4443_, lean_object* v_f_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(v_00_u03b2_4442_, v_map_4443_, v_f_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_object* v_00_u03b2_4454_, lean_object* v_f_4455_, lean_object* v_as_4456_, size_t v_i_4457_, size_t v_stop_4458_, lean_object* v_b_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_4455_, v_as_4456_, v_i_4457_, v_stop_4458_, v_b_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4469_, lean_object* v_f_4470_, lean_object* v_as_4471_, lean_object* v_i_4472_, lean_object* v_stop_4473_, lean_object* v_b_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
size_t v_i_boxed_4483_; size_t v_stop_boxed_4484_; lean_object* v_res_4485_; 
v_i_boxed_4483_ = lean_unbox_usize(v_i_4472_);
lean_dec(v_i_4472_);
v_stop_boxed_4484_ = lean_unbox_usize(v_stop_4473_);
lean_dec(v_stop_4473_);
v_res_4485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(v_00_u03b2_4469_, v_f_4470_, v_as_4471_, v_i_boxed_4483_, v_stop_boxed_4484_, v_b_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec_ref(v_as_4471_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(lean_object* v_a_4486_, lean_object* v___x_4487_, lean_object* v_id_4488_, uint8_t v_danglingDot_4489_, lean_object* v_as_4490_, lean_object* v_as_x27_4491_, lean_object* v_b_4492_, lean_object* v_a_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4486_, v___x_4487_, v_id_4488_, v_danglingDot_4489_, v_as_x27_4491_, v_b_4492_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___boxed(lean_object* v_a_4503_, lean_object* v___x_4504_, lean_object* v_id_4505_, lean_object* v_danglingDot_4506_, lean_object* v_as_4507_, lean_object* v_as_x27_4508_, lean_object* v_b_4509_, lean_object* v_a_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
uint8_t v_danglingDot_boxed_4519_; lean_object* v_res_4520_; 
v_danglingDot_boxed_4519_ = lean_unbox(v_danglingDot_4506_);
v_res_4520_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(v_a_4503_, v___x_4504_, v_id_4505_, v_danglingDot_boxed_4519_, v_as_4507_, v_as_x27_4508_, v_b_4509_, v_a_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v_as_x27_4508_);
lean_dec(v_as_4507_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4521_, lean_object* v_map_4522_, lean_object* v_f_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4522_, v_f_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4534_, lean_object* v_map_4535_, lean_object* v_f_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4534_, v_map_4535_, v_f_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object* v_map_4547_, lean_object* v_f_4548_, lean_object* v_init_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4548_, v_map_4547_, v_init_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_map_4559_, lean_object* v_f_4560_, lean_object* v_init_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4559_, v_f_4560_, v_init_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_4571_, lean_object* v_00_u03b2_4572_, lean_object* v_map_4573_, lean_object* v_f_4574_, lean_object* v_init_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4574_, v_map_4573_, v_init_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_4585_, lean_object* v_00_u03b2_4586_, lean_object* v_map_4587_, lean_object* v_f_4588_, lean_object* v_init_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(v_00_u03c3_4585_, v_00_u03b2_4586_, v_map_4587_, v_f_4588_, v_init_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(lean_object* v_id_4599_, uint8_t v_danglingDot_4600_, lean_object* v_as_4601_, size_t v_sz_4602_, size_t v_i_4603_, lean_object* v_b_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_4599_, v_danglingDot_4600_, v_as_4601_, v_sz_4602_, v_i_4603_, v_b_4604_, v___y_4605_, v___y_4606_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___boxed(lean_object* v_id_4614_, lean_object* v_danglingDot_4615_, lean_object* v_as_4616_, lean_object* v_sz_4617_, lean_object* v_i_4618_, lean_object* v_b_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
uint8_t v_danglingDot_boxed_4628_; size_t v_sz_boxed_4629_; size_t v_i_boxed_4630_; lean_object* v_res_4631_; 
v_danglingDot_boxed_4628_ = lean_unbox(v_danglingDot_4615_);
v_sz_boxed_4629_ = lean_unbox_usize(v_sz_4617_);
lean_dec(v_sz_4617_);
v_i_boxed_4630_ = lean_unbox_usize(v_i_4618_);
lean_dec(v_i_4618_);
v_res_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(v_id_4614_, v_danglingDot_boxed_4628_, v_as_4616_, v_sz_boxed_4629_, v_i_boxed_4630_, v_b_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec_ref(v_as_4616_);
lean_dec(v_id_4614_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_map_4632_, lean_object* v_f_4633_, lean_object* v_init_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v___x_4644_; 
v___x_4644_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4633_, v_map_4632_, v_init_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_map_4645_, lean_object* v_f_4646_, lean_object* v_init_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(v_map_4645_, v_f_4646_, v_init_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03c3_4658_, lean_object* v_00_u03b2_4659_, lean_object* v_map_4660_, lean_object* v_f_4661_, lean_object* v_init_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4661_, v_map_4660_, v_init_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_00_u03c3_4673_, lean_object* v_00_u03b2_4674_, lean_object* v_map_4675_, lean_object* v_f_4676_, lean_object* v_init_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(v_00_u03c3_4673_, v_00_u03b2_4674_, v_map_4675_, v_f_4676_, v_init_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_object* v_00_u03c3_4688_, lean_object* v_00_u03b1_4689_, lean_object* v_00_u03b2_4690_, lean_object* v_f_4691_, lean_object* v_x_4692_, lean_object* v_x_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4691_, v_x_4692_, v_x_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03c3_4703_, lean_object* v_00_u03b1_4704_, lean_object* v_00_u03b2_4705_, lean_object* v_f_4706_, lean_object* v_x_4707_, lean_object* v_x_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(v_00_u03c3_4703_, v_00_u03b1_4704_, v_00_u03b2_4705_, v_f_4706_, v_x_4707_, v_x_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(lean_object* v_id_4718_, uint8_t v_danglingDot_4719_, lean_object* v_as_4720_, size_t v_sz_4721_, size_t v_i_4722_, lean_object* v_b_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_4718_, v_danglingDot_4719_, v_as_4720_, v_sz_4721_, v_i_4722_, v_b_4723_, v___y_4724_, v___y_4725_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___boxed(lean_object* v_id_4733_, lean_object* v_danglingDot_4734_, lean_object* v_as_4735_, lean_object* v_sz_4736_, lean_object* v_i_4737_, lean_object* v_b_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
uint8_t v_danglingDot_boxed_4747_; size_t v_sz_boxed_4748_; size_t v_i_boxed_4749_; lean_object* v_res_4750_; 
v_danglingDot_boxed_4747_ = lean_unbox(v_danglingDot_4734_);
v_sz_boxed_4748_ = lean_unbox_usize(v_sz_4736_);
lean_dec(v_sz_4736_);
v_i_boxed_4749_ = lean_unbox_usize(v_i_4737_);
lean_dec(v_i_4737_);
v_res_4750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(v_id_4733_, v_danglingDot_boxed_4747_, v_as_4735_, v_sz_boxed_4748_, v_i_boxed_4749_, v_b_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec_ref(v_as_4735_);
lean_dec(v_id_4733_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_object* v_00_u03c3_4751_, lean_object* v_00_u03b1_4752_, lean_object* v_00_u03b2_4753_, lean_object* v_f_4754_, lean_object* v_x_4755_, lean_object* v_x_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4754_, v_x_4755_, v_x_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___boxed(lean_object* v_00_u03c3_4767_, lean_object* v_00_u03b1_4768_, lean_object* v_00_u03b2_4769_, lean_object* v_f_4770_, lean_object* v_x_4771_, lean_object* v_x_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(v_00_u03c3_4767_, v_00_u03b1_4768_, v_00_u03b2_4769_, v_f_4770_, v_x_4771_, v_x_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_object* v_00_u03b1_4783_, lean_object* v_00_u03b2_4784_, lean_object* v_00_u03c3_4785_, lean_object* v_f_4786_, lean_object* v_as_4787_, size_t v_i_4788_, size_t v_stop_4789_, lean_object* v_b_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_4786_, v_as_4787_, v_i_4788_, v_stop_4789_, v_b_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___boxed(lean_object* v_00_u03b1_4800_, lean_object* v_00_u03b2_4801_, lean_object* v_00_u03c3_4802_, lean_object* v_f_4803_, lean_object* v_as_4804_, lean_object* v_i_4805_, lean_object* v_stop_4806_, lean_object* v_b_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
size_t v_i_boxed_4816_; size_t v_stop_boxed_4817_; lean_object* v_res_4818_; 
v_i_boxed_4816_ = lean_unbox_usize(v_i_4805_);
lean_dec(v_i_4805_);
v_stop_boxed_4817_ = lean_unbox_usize(v_stop_4806_);
lean_dec(v_stop_4806_);
v_res_4818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(v_00_u03b1_4800_, v_00_u03b2_4801_, v_00_u03c3_4802_, v_f_4803_, v_as_4804_, v_i_boxed_4816_, v_stop_boxed_4817_, v_b_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
lean_dec_ref(v_as_4804_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_object* v_00_u03c3_4819_, lean_object* v_00_u03b1_4820_, lean_object* v_00_u03b2_4821_, lean_object* v_f_4822_, lean_object* v_keys_4823_, lean_object* v_vals_4824_, lean_object* v_heq_4825_, lean_object* v_i_4826_, lean_object* v_acc_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_4822_, v_keys_4823_, v_vals_4824_, v_i_4826_, v_acc_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___boxed(lean_object** _args){
lean_object* v_00_u03c3_4837_ = _args[0];
lean_object* v_00_u03b1_4838_ = _args[1];
lean_object* v_00_u03b2_4839_ = _args[2];
lean_object* v_f_4840_ = _args[3];
lean_object* v_keys_4841_ = _args[4];
lean_object* v_vals_4842_ = _args[5];
lean_object* v_heq_4843_ = _args[6];
lean_object* v_i_4844_ = _args[7];
lean_object* v_acc_4845_ = _args[8];
lean_object* v___y_4846_ = _args[9];
lean_object* v___y_4847_ = _args[10];
lean_object* v___y_4848_ = _args[11];
lean_object* v___y_4849_ = _args[12];
lean_object* v___y_4850_ = _args[13];
lean_object* v___y_4851_ = _args[14];
lean_object* v___y_4852_ = _args[15];
lean_object* v___y_4853_ = _args[16];
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(v_00_u03c3_4837_, v_00_u03b1_4838_, v_00_u03b2_4839_, v_f_4840_, v_keys_4841_, v_vals_4842_, v_heq_4843_, v_i_4844_, v_acc_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec_ref(v_vals_4842_);
lean_dec_ref(v_keys_4841_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_object* v_00_u03b1_4855_, lean_object* v_00_u03b2_4856_, lean_object* v_00_u03c3_4857_, lean_object* v_f_4858_, lean_object* v_as_4859_, size_t v_i_4860_, size_t v_stop_4861_, lean_object* v_b_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_4858_, v_as_4859_, v_i_4860_, v_stop_4861_, v_b_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___boxed(lean_object** _args){
lean_object* v_00_u03b1_4873_ = _args[0];
lean_object* v_00_u03b2_4874_ = _args[1];
lean_object* v_00_u03c3_4875_ = _args[2];
lean_object* v_f_4876_ = _args[3];
lean_object* v_as_4877_ = _args[4];
lean_object* v_i_4878_ = _args[5];
lean_object* v_stop_4879_ = _args[6];
lean_object* v_b_4880_ = _args[7];
lean_object* v___y_4881_ = _args[8];
lean_object* v___y_4882_ = _args[9];
lean_object* v___y_4883_ = _args[10];
lean_object* v___y_4884_ = _args[11];
lean_object* v___y_4885_ = _args[12];
lean_object* v___y_4886_ = _args[13];
lean_object* v___y_4887_ = _args[14];
lean_object* v___y_4888_ = _args[15];
lean_object* v___y_4889_ = _args[16];
_start:
{
size_t v_i_boxed_4890_; size_t v_stop_boxed_4891_; lean_object* v_res_4892_; 
v_i_boxed_4890_ = lean_unbox_usize(v_i_4878_);
lean_dec(v_i_4878_);
v_stop_boxed_4891_ = lean_unbox_usize(v_stop_4879_);
lean_dec(v_stop_4879_);
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(v_00_u03b1_4873_, v_00_u03b2_4874_, v_00_u03c3_4875_, v_f_4876_, v_as_4877_, v_i_boxed_4890_, v_stop_boxed_4891_, v_b_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec_ref(v___y_4884_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
lean_dec_ref(v_as_4877_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_object* v_00_u03c3_4893_, lean_object* v_00_u03b1_4894_, lean_object* v_00_u03b2_4895_, lean_object* v_f_4896_, lean_object* v_keys_4897_, lean_object* v_vals_4898_, lean_object* v_heq_4899_, lean_object* v_i_4900_, lean_object* v_acc_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_4896_, v_keys_4897_, v_vals_4898_, v_i_4900_, v_acc_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_00_u03c3_4912_ = _args[0];
lean_object* v_00_u03b1_4913_ = _args[1];
lean_object* v_00_u03b2_4914_ = _args[2];
lean_object* v_f_4915_ = _args[3];
lean_object* v_keys_4916_ = _args[4];
lean_object* v_vals_4917_ = _args[5];
lean_object* v_heq_4918_ = _args[6];
lean_object* v_i_4919_ = _args[7];
lean_object* v_acc_4920_ = _args[8];
lean_object* v___y_4921_ = _args[9];
lean_object* v___y_4922_ = _args[10];
lean_object* v___y_4923_ = _args[11];
lean_object* v___y_4924_ = _args[12];
lean_object* v___y_4925_ = _args[13];
lean_object* v___y_4926_ = _args[14];
lean_object* v___y_4927_ = _args[15];
lean_object* v___y_4928_ = _args[16];
lean_object* v___y_4929_ = _args[17];
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(v_00_u03c3_4912_, v_00_u03b1_4913_, v_00_u03b2_4914_, v_f_4915_, v_keys_4916_, v_vals_4917_, v_heq_4918_, v_i_4919_, v_acc_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec_ref(v_vals_4917_);
lean_dec_ref(v_keys_4916_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4931_, lean_object* v_pos_4932_, lean_object* v_completionInfoPos_4933_, lean_object* v_ctx_4934_, lean_object* v_lctx_4935_, lean_object* v_stx_4936_, lean_object* v_id_4937_, lean_object* v_hoverInfo_4938_, uint8_t v_danglingDot_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4942_ = lean_box(v_danglingDot_4939_);
lean_inc_ref(v_ctx_4934_);
v___x_4943_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_4943_, 0, v_ctx_4934_);
lean_closure_set(v___x_4943_, 1, v_stx_4936_);
lean_closure_set(v___x_4943_, 2, v_id_4937_);
lean_closure_set(v___x_4943_, 3, v_hoverInfo_4938_);
lean_closure_set(v___x_4943_, 4, v___x_4942_);
v___x_4944_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4931_, v_pos_4932_, v_completionInfoPos_4933_, v_ctx_4934_, v_lctx_4935_, v___x_4943_, v_a_4940_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_4945_, lean_object* v_pos_4946_, lean_object* v_completionInfoPos_4947_, lean_object* v_ctx_4948_, lean_object* v_lctx_4949_, lean_object* v_stx_4950_, lean_object* v_id_4951_, lean_object* v_hoverInfo_4952_, lean_object* v_danglingDot_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
uint8_t v_danglingDot_boxed_4956_; lean_object* v_res_4957_; 
v_danglingDot_boxed_4956_ = lean_unbox(v_danglingDot_4953_);
v_res_4957_ = l_Lean_Server_Completion_idCompletion(v_uri_4945_, v_pos_4946_, v_completionInfoPos_4947_, v_ctx_4948_, v_lctx_4949_, v_stx_4950_, v_id_4951_, v_hoverInfo_4952_, v_danglingDot_boxed_4956_, v_a_4954_);
lean_dec_ref(v_a_4954_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_4958_, lean_object* v___y_4959_){
_start:
{
uint8_t v___x_4961_; 
v___x_4961_ = l_Lean_Expr_hasMVar(v_e_4958_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4962_, 0, v_e_4958_);
v___x_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
return v___x_4963_;
}
else
{
lean_object* v___x_4964_; lean_object* v_mctx_4965_; lean_object* v___x_4966_; lean_object* v_fst_4967_; lean_object* v_snd_4968_; lean_object* v___x_4969_; lean_object* v_cache_4970_; lean_object* v_zetaDeltaFVarIds_4971_; lean_object* v_postponed_4972_; lean_object* v_diag_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4983_; 
v___x_4964_ = lean_st_ref_get(v___y_4959_);
v_mctx_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc_ref(v_mctx_4965_);
lean_dec(v___x_4964_);
v___x_4966_ = l_Lean_instantiateMVarsCore(v_mctx_4965_, v_e_4958_);
v_fst_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_fst_4967_);
v_snd_4968_ = lean_ctor_get(v___x_4966_, 1);
lean_inc(v_snd_4968_);
lean_dec_ref(v___x_4966_);
v___x_4969_ = lean_st_ref_take(v___y_4959_);
v_cache_4970_ = lean_ctor_get(v___x_4969_, 1);
v_zetaDeltaFVarIds_4971_ = lean_ctor_get(v___x_4969_, 2);
v_postponed_4972_ = lean_ctor_get(v___x_4969_, 3);
v_diag_4973_ = lean_ctor_get(v___x_4969_, 4);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4983_ == 0)
{
lean_object* v_unused_4984_; 
v_unused_4984_ = lean_ctor_get(v___x_4969_, 0);
lean_dec(v_unused_4984_);
v___x_4975_ = v___x_4969_;
v_isShared_4976_ = v_isSharedCheck_4983_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_diag_4973_);
lean_inc(v_postponed_4972_);
lean_inc(v_zetaDeltaFVarIds_4971_);
lean_inc(v_cache_4970_);
lean_dec(v___x_4969_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4983_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v_snd_4968_);
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_snd_4968_);
lean_ctor_set(v_reuseFailAlloc_4982_, 1, v_cache_4970_);
lean_ctor_set(v_reuseFailAlloc_4982_, 2, v_zetaDeltaFVarIds_4971_);
lean_ctor_set(v_reuseFailAlloc_4982_, 3, v_postponed_4972_);
lean_ctor_set(v_reuseFailAlloc_4982_, 4, v_diag_4973_);
v___x_4978_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4979_ = lean_st_ref_set(v___y_4959_, v___x_4978_);
v___x_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4980_, 0, v_fst_4967_);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
return v___x_4981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4985_, v___y_4986_);
lean_dec(v___y_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v___x_4998_; 
v___x_4998_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4989_, v___y_4994_);
return v___x_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_5009_, lean_object* v_declName_5010_, lean_object* v_decl_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_unnormedTypeName_5020_; uint8_t v___x_5021_; 
v_unnormedTypeName_5020_ = l_Lean_Name_getPrefix(v_declName_5010_);
v___x_5021_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_5020_, v_a_5009_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
lean_dec_ref(v_decl_5011_);
lean_dec(v_declName_5010_);
v___x_5022_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5022_);
return v___x_5023_;
}
else
{
lean_object* v___x_5024_; lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5090_; 
v___x_5024_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5010_, v___y_5018_);
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5027_ = v___x_5024_;
v_isShared_5028_ = v_isSharedCheck_5090_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5024_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5090_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
if (lean_obj_tag(v_a_5025_) == 1)
{
lean_object* v_val_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5085_; 
lean_del_object(v___x_5027_);
v_val_5029_ = lean_ctor_get(v_a_5025_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_a_5025_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5031_ = v_a_5025_;
v_isShared_5032_ = v_isSharedCheck_5085_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_val_5029_);
lean_dec(v_a_5025_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5085_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v_info_5033_; lean_object* v_kind_5034_; lean_object* v_tags_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v_info_5033_ = lean_ctor_get(v_decl_5011_, 0);
lean_inc_ref(v_info_5033_);
v_kind_5034_ = lean_ctor_get(v_decl_5011_, 1);
lean_inc_ref(v_kind_5034_);
v_tags_5035_ = lean_ctor_get(v_decl_5011_, 2);
lean_inc_ref(v_tags_5035_);
lean_dec_ref(v_decl_5011_);
v___x_5036_ = l_Lean_Name_getPrefix(v_val_5029_);
lean_dec(v_val_5029_);
v___x_5037_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_5036_, v_info_5033_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5076_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5040_ = v___x_5037_;
v_isShared_5041_ = v_isSharedCheck_5076_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5037_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5076_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
uint8_t v___x_5042_; 
v___x_5042_ = lean_unbox(v_a_5038_);
lean_dec(v_a_5038_);
if (v___x_5042_ == 0)
{
lean_object* v___x_5043_; lean_object* v___x_5045_; 
lean_dec_ref(v_tags_5035_);
lean_dec_ref(v_kind_5034_);
lean_dec_ref(v_info_5033_);
lean_del_object(v___x_5031_);
v___x_5043_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5043_);
v___x_5045_ = v___x_5040_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
else
{
lean_object* v___x_5047_; 
lean_del_object(v___x_5040_);
lean_inc(v___y_5018_);
lean_inc_ref(v___y_5017_);
lean_inc(v___y_5016_);
lean_inc_ref(v___y_5015_);
v___x_5047_ = lean_apply_5(v_kind_5034_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, lean_box(0));
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
lean_inc(v___y_5018_);
lean_inc_ref(v___y_5017_);
lean_inc(v___y_5016_);
lean_inc_ref(v___y_5015_);
v___x_5049_ = lean_apply_5(v_tags_5035_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, lean_box(0));
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5056_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5051_ = l_Lean_ConstantInfo_name(v_info_5033_);
lean_dec_ref(v_info_5033_);
v___x_5052_ = l_Lean_Name_getString_x21(v___x_5051_);
v___x_5053_ = lean_box(0);
v___x_5054_ = l_Lean_Name_str___override(v___x_5053_, v___x_5052_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set_tag(v___x_5031_, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5051_);
v___x_5056_ = v___x_5031_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5051_);
v___x_5056_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
uint8_t v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = lean_unbox(v_a_5048_);
lean_dec(v_a_5048_);
v___x_5058_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5054_, v___x_5056_, v___x_5057_, v_a_5050_, v___y_5012_, v___y_5013_);
return v___x_5058_;
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_dec(v_a_5048_);
lean_dec_ref(v_info_5033_);
lean_del_object(v___x_5031_);
v_a_5060_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5049_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5049_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec_ref(v_tags_5035_);
lean_dec_ref(v_info_5033_);
lean_del_object(v___x_5031_);
v_a_5068_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5047_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5047_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_dec_ref(v_tags_5035_);
lean_dec_ref(v_kind_5034_);
lean_dec_ref(v_info_5033_);
lean_del_object(v___x_5031_);
v_a_5077_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5037_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5037_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
else
{
lean_object* v___x_5086_; lean_object* v___x_5088_; 
lean_dec(v_a_5025_);
lean_dec_ref(v_decl_5011_);
v___x_5086_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5028_ == 0)
{
lean_ctor_set(v___x_5027_, 0, v___x_5086_);
v___x_5088_ = v___x_5027_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
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
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_5091_, lean_object* v_declName_5092_, lean_object* v_decl_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5091_, v_declName_5092_, v_decl_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_a_5116_; lean_object* v___y_5120_; uint8_t v___y_5121_; lean_object* v___y_5131_; lean_object* v_a_5132_; lean_object* v___x_5135_; 
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
lean_inc(v___y_5108_);
lean_inc_ref(v___y_5107_);
v___x_5135_ = lean_infer_type(v_expr_5103_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_a_5136_; lean_object* v___x_5137_; lean_object* v_a_5138_; lean_object* v_a_5139_; lean_object* v___x_5140_; 
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5135_, 1);
v___x_5137_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_5136_, v___y_5108_);
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_a_5138_);
lean_dec_ref(v___x_5137_);
v_a_5139_ = lean_ctor_get(v_a_5138_, 0);
lean_inc(v_a_5139_);
lean_dec(v_a_5138_);
v___x_5140_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_5139_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5140_, 1);
v_a_5116_ = v_a_5141_;
goto v___jp_5115_;
}
else
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
v_a_5142_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5140_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5140_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
lean_inc(v_a_5142_);
if (v_isShared_5145_ == 0)
{
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_a_5142_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
v___y_5131_ = v___x_5147_;
v_a_5132_ = v_a_5142_;
goto v___jp_5130_;
}
}
}
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
v_a_5150_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5135_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5135_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
lean_inc(v_a_5150_);
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
v___y_5131_ = v___x_5155_;
v_a_5132_ = v_a_5150_;
goto v___jp_5130_;
}
}
}
v___jp_5112_:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
return v___x_5114_;
}
v___jp_5115_:
{
if (lean_obj_tag(v_a_5116_) == 0)
{
lean_object* v___f_5117_; lean_object* v___x_5118_; 
v___f_5117_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5117_, 0, v_a_5116_);
v___x_5118_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5117_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
return v___x_5118_;
}
else
{
goto v___jp_5112_;
}
}
v___jp_5119_:
{
if (v___y_5121_ == 0)
{
lean_dec_ref(v___y_5120_);
goto v___jp_5112_;
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
v_a_5122_ = lean_ctor_get(v___y_5120_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___y_5120_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___y_5120_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___y_5120_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
v___jp_5130_:
{
uint8_t v___x_5133_; 
v___x_5133_ = l_Lean_Exception_isInterrupt(v_a_5132_);
if (v___x_5133_ == 0)
{
uint8_t v___x_5134_; 
v___x_5134_ = l_Lean_Exception_isRuntime(v_a_5132_);
v___y_5120_ = v___y_5131_;
v___y_5121_ = v___x_5134_;
goto v___jp_5119_;
}
else
{
lean_dec_ref(v_a_5132_);
v___y_5120_ = v___y_5131_;
v___y_5121_ = v___x_5133_;
goto v___jp_5119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5168_, lean_object* v_pos_5169_, lean_object* v_completionInfoPos_5170_, lean_object* v_ctx_5171_, lean_object* v_info_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v_lctx_5175_; lean_object* v_expr_5176_; lean_object* v___f_5177_; lean_object* v___x_5178_; 
v_lctx_5175_ = lean_ctor_get(v_info_5172_, 1);
lean_inc_ref(v_lctx_5175_);
v_expr_5176_ = lean_ctor_get(v_info_5172_, 3);
lean_inc_ref(v_expr_5176_);
lean_dec_ref(v_info_5172_);
v___f_5177_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5177_, 0, v_expr_5176_);
v___x_5178_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5168_, v_pos_5169_, v_completionInfoPos_5170_, v_ctx_5171_, v_lctx_5175_, v___f_5177_, v_a_5173_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5179_, lean_object* v_pos_5180_, lean_object* v_completionInfoPos_5181_, lean_object* v_ctx_5182_, lean_object* v_info_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Lean_Server_Completion_dotCompletion(v_uri_5179_, v_pos_5180_, v_completionInfoPos_5181_, v_ctx_5182_, v_info_5183_, v_a_5184_);
lean_dec_ref(v_a_5184_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5187_, uint8_t v___x_5188_, lean_object* v_id_5189_, lean_object* v_declName_5190_, lean_object* v_decl_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
lean_object* v___x_5203_; uint8_t v___x_5204_; 
v___x_5203_ = l_Lean_Name_getPrefix(v_declName_5190_);
lean_inc(v___x_5187_);
v___x_5204_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5203_, v___x_5187_);
if (v___x_5204_ == 0)
{
lean_dec_ref(v_decl_5191_);
lean_dec(v_declName_5190_);
lean_dec(v___x_5187_);
goto v___jp_5200_;
}
else
{
if (v___x_5188_ == 0)
{
lean_object* v___x_5205_; lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5302_; 
v___x_5205_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5190_, v___y_5198_);
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5208_ = v___x_5205_;
v_isShared_5209_ = v_isSharedCheck_5302_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5205_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5302_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
if (lean_obj_tag(v_a_5206_) == 1)
{
lean_object* v_val_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5297_; 
lean_del_object(v___x_5208_);
v_val_5210_ = lean_ctor_get(v_a_5206_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v_a_5206_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5212_ = v_a_5206_;
v_isShared_5213_ = v_isSharedCheck_5297_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_val_5210_);
lean_dec(v_a_5206_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5297_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v_info_5214_; lean_object* v_kind_5215_; lean_object* v_tags_5216_; lean_object* v___x_5217_; 
v_info_5214_ = lean_ctor_get(v_decl_5191_, 0);
lean_inc_ref(v_info_5214_);
v_kind_5215_ = lean_ctor_get(v_decl_5191_, 1);
lean_inc_ref(v_kind_5215_);
v_tags_5216_ = lean_ctor_get(v_decl_5191_, 2);
lean_inc_ref(v_tags_5216_);
lean_dec_ref(v_decl_5191_);
v___x_5217_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5187_, v_info_5214_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5288_; 
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5220_ = v___x_5217_;
v_isShared_5221_ = v_isSharedCheck_5288_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5217_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5288_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
uint8_t v___x_5222_; 
v___x_5222_ = lean_unbox(v_a_5218_);
lean_dec(v_a_5218_);
if (v___x_5222_ == 0)
{
lean_object* v___x_5223_; lean_object* v___x_5225_; 
lean_dec_ref(v_tags_5216_);
lean_dec_ref(v_kind_5215_);
lean_dec_ref(v_info_5214_);
lean_del_object(v___x_5212_);
lean_dec(v_val_5210_);
v___x_5223_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 0, v___x_5223_);
v___x_5225_ = v___x_5220_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
else
{
lean_object* v___x_5227_; 
lean_del_object(v___x_5220_);
lean_inc(v___y_5198_);
lean_inc_ref(v___y_5197_);
lean_inc(v___y_5196_);
lean_inc_ref(v___y_5195_);
v___x_5227_ = lean_apply_5(v_kind_5215_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, lean_box(0));
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5229_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5227_, 1);
lean_inc(v___y_5198_);
lean_inc_ref(v___y_5197_);
lean_inc(v___y_5196_);
lean_inc_ref(v___y_5195_);
v___x_5229_ = lean_apply_5(v_tags_5216_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, lean_box(0));
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; uint8_t v___x_5231_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5230_);
lean_dec_ref_known(v___x_5229_, 1);
v___x_5231_ = l_Lean_Name_isAnonymous(v_id_5189_);
if (v___x_5231_ == 0)
{
lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5253_; 
lean_del_object(v___x_5212_);
v___x_5232_ = l_Lean_Name_getPrefix(v_val_5210_);
v___x_5233_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5232_, v_id_5189_, v___x_5231_, v_val_5210_, v___y_5198_);
lean_dec(v___x_5232_);
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5253_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5253_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
if (lean_obj_tag(v_a_5234_) == 1)
{
lean_object* v_val_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5248_; 
lean_del_object(v___x_5236_);
v_val_5238_ = lean_ctor_get(v_a_5234_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v_a_5234_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5240_ = v_a_5234_;
v_isShared_5241_ = v_isSharedCheck_5248_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_val_5238_);
lean_dec(v_a_5234_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5248_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5242_; lean_object* v___x_5244_; 
v___x_5242_ = l_Lean_ConstantInfo_name(v_info_5214_);
lean_dec_ref(v_info_5214_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set_tag(v___x_5240_, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5242_);
v___x_5244_ = v___x_5240_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5242_);
v___x_5244_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
uint8_t v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = lean_unbox(v_a_5228_);
lean_dec(v_a_5228_);
v___x_5246_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5238_, v___x_5244_, v___x_5245_, v_a_5230_, v___y_5192_, v___y_5193_);
return v___x_5246_;
}
}
}
else
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
lean_dec(v_a_5234_);
lean_dec(v_a_5230_);
lean_dec(v_a_5228_);
lean_dec_ref(v_info_5214_);
v___x_5249_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 0, v___x_5249_);
v___x_5251_ = v___x_5236_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
else
{
lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5259_; 
lean_dec(v_val_5210_);
v___x_5254_ = l_Lean_ConstantInfo_name(v_info_5214_);
lean_dec_ref(v_info_5214_);
v___x_5255_ = l_Lean_Name_getString_x21(v___x_5254_);
v___x_5256_ = lean_box(0);
v___x_5257_ = l_Lean_Name_str___override(v___x_5256_, v___x_5255_);
if (v_isShared_5213_ == 0)
{
lean_ctor_set_tag(v___x_5212_, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5254_);
v___x_5259_ = v___x_5212_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5254_);
v___x_5259_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
uint8_t v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5269_; 
v___x_5260_ = lean_unbox(v_a_5228_);
lean_dec(v_a_5228_);
v___x_5261_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5257_, v___x_5259_, v___x_5260_, v_a_5230_, v___y_5192_, v___y_5193_);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5269_ == 0)
{
lean_object* v_unused_5270_; 
v_unused_5270_ = lean_ctor_get(v___x_5261_, 0);
lean_dec(v_unused_5270_);
v___x_5263_ = v___x_5261_;
v_isShared_5264_ = v_isSharedCheck_5269_;
goto v_resetjp_5262_;
}
else
{
lean_dec(v___x_5261_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5269_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5265_; lean_object* v___x_5267_; 
v___x_5265_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 0, v___x_5265_);
v___x_5267_ = v___x_5263_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5265_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
lean_dec(v_a_5228_);
lean_dec_ref(v_info_5214_);
lean_del_object(v___x_5212_);
lean_dec(v_val_5210_);
v_a_5272_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5229_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5229_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5277_; 
if (v_isShared_5275_ == 0)
{
v___x_5277_ = v___x_5274_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_a_5272_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
else
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5287_; 
lean_dec_ref(v_tags_5216_);
lean_dec_ref(v_info_5214_);
lean_del_object(v___x_5212_);
lean_dec(v_val_5210_);
v_a_5280_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5282_ = v___x_5227_;
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___x_5227_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5283_ == 0)
{
v___x_5285_ = v___x_5282_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
}
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_dec_ref(v_tags_5216_);
lean_dec_ref(v_kind_5215_);
lean_dec_ref(v_info_5214_);
lean_del_object(v___x_5212_);
lean_dec(v_val_5210_);
v_a_5289_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5217_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5217_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
}
else
{
lean_object* v___x_5298_; lean_object* v___x_5300_; 
lean_dec(v_a_5206_);
lean_dec_ref(v_decl_5191_);
lean_dec(v___x_5187_);
v___x_5298_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 0, v___x_5298_);
v___x_5300_ = v___x_5208_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
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
else
{
lean_dec_ref(v_decl_5191_);
lean_dec(v_declName_5190_);
lean_dec(v___x_5187_);
goto v___jp_5200_;
}
}
v___jp_5200_:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5303_, lean_object* v___x_5304_, lean_object* v_id_5305_, lean_object* v_declName_5306_, lean_object* v_decl_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
uint8_t v___x_21334__boxed_5316_; lean_object* v_res_5317_; 
v___x_21334__boxed_5316_ = lean_unbox(v___x_5304_);
v_res_5317_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5303_, v___x_21334__boxed_5316_, v_id_5305_, v_declName_5306_, v_decl_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
lean_dec(v___y_5314_);
lean_dec_ref(v___y_5313_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec_ref(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v_id_5305_);
return v_res_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5318_, lean_object* v_id_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5318_) == 1)
{
lean_object* v_val_5328_; lean_object* v___x_5329_; 
v_val_5328_ = lean_ctor_get(v_expectedType_x3f_5318_, 0);
lean_inc(v_val_5328_);
lean_dec_ref_known(v_expectedType_x3f_5318_, 1);
v___x_5329_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5328_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5345_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5332_ = v___x_5329_;
v_isShared_5333_ = v_isSharedCheck_5345_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5329_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5345_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5334_ = lean_array_get_size(v_a_5330_);
v___x_5335_ = lean_unsigned_to_nat(0u);
v___x_5336_ = lean_nat_dec_eq(v___x_5334_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___f_5339_; lean_object* v___x_5340_; 
lean_del_object(v___x_5332_);
v___x_5337_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5330_);
lean_dec(v_a_5330_);
v___x_5338_ = lean_box(v___x_5336_);
v___f_5339_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 13, 3);
lean_closure_set(v___f_5339_, 0, v___x_5337_);
lean_closure_set(v___f_5339_, 1, v___x_5338_);
lean_closure_set(v___f_5339_, 2, v_id_5319_);
v___x_5340_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5339_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
return v___x_5340_;
}
else
{
lean_object* v___x_5341_; lean_object* v___x_5343_; 
lean_dec(v_a_5330_);
lean_dec(v_id_5319_);
v___x_5341_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 0, v___x_5341_);
v___x_5343_ = v___x_5332_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5341_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec(v_id_5319_);
v_a_5346_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5329_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5329_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
else
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
lean_dec(v_id_5319_);
lean_dec(v_expectedType_x3f_5318_);
v___x_5354_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5354_);
return v___x_5355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5356_, lean_object* v_id_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5356_, v_id_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5367_, lean_object* v_pos_5368_, lean_object* v_completionInfoPos_5369_, lean_object* v_ctx_5370_, lean_object* v_lctx_5371_, lean_object* v_id_5372_, lean_object* v_expectedType_x3f_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v___y_5376_; lean_object* v___x_5377_; 
v___y_5376_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5376_, 0, v_expectedType_x3f_5373_);
lean_closure_set(v___y_5376_, 1, v_id_5372_);
v___x_5377_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5367_, v_pos_5368_, v_completionInfoPos_5369_, v_ctx_5370_, v_lctx_5371_, v___y_5376_, v_a_5374_);
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5378_, lean_object* v_pos_5379_, lean_object* v_completionInfoPos_5380_, lean_object* v_ctx_5381_, lean_object* v_lctx_5382_, lean_object* v_id_5383_, lean_object* v_expectedType_x3f_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5378_, v_pos_5379_, v_completionInfoPos_5380_, v_ctx_5381_, v_lctx_5382_, v_id_5383_, v_expectedType_x3f_5384_, v_a_5385_);
lean_dec_ref(v_a_5385_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5394_, lean_object* v_as_5395_, size_t v_sz_5396_, size_t v_i_5397_, lean_object* v_b_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_){
_start:
{
lean_object* v_a_5403_; uint8_t v___x_5407_; 
v___x_5407_ = lean_usize_dec_lt(v_i_5397_, v_sz_5396_);
if (v___x_5407_ == 0)
{
lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5408_, 0, v_b_5398_);
v___x_5409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5408_);
return v___x_5409_;
}
else
{
lean_object* v___x_5410_; lean_object* v_a_5411_; 
v___x_5410_ = lean_box(0);
v_a_5411_ = lean_array_uget_borrowed(v_as_5395_, v_i_5397_);
if (lean_obj_tag(v_a_5411_) == 1)
{
lean_object* v_str_5412_; uint8_t v___x_5413_; 
v_str_5412_ = lean_ctor_get(v_a_5411_, 1);
v___x_5413_ = l_String_charactersIn(v___y_5394_, v_str_5412_);
if (v___x_5413_ == 0)
{
v_a_5403_ = v___x_5410_;
goto v___jp_5402_;
}
else
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5415_ = lean_box(0);
v___x_5416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5412_);
v___x_5417_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5417_, 0, v_str_5412_);
lean_ctor_set(v___x_5417_, 1, v___x_5414_);
lean_ctor_set(v___x_5417_, 2, v___x_5415_);
lean_ctor_set(v___x_5417_, 3, v___x_5416_);
lean_ctor_set(v___x_5417_, 4, v___x_5415_);
lean_ctor_set(v___x_5417_, 5, v___x_5415_);
lean_ctor_set(v___x_5417_, 6, v___x_5415_);
lean_ctor_set(v___x_5417_, 7, v___x_5415_);
v___x_5418_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5417_, v___x_5415_, v___y_5399_, v___y_5400_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_object* v_a_5419_; 
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
lean_inc(v_a_5419_);
if (lean_obj_tag(v_a_5419_) == 0)
{
lean_dec_ref_known(v_a_5419_, 1);
return v___x_5418_;
}
else
{
lean_dec_ref_known(v_a_5419_, 1);
lean_dec_ref_known(v___x_5418_, 1);
v_a_5403_ = v___x_5410_;
goto v___jp_5402_;
}
}
else
{
return v___x_5418_;
}
}
}
else
{
v_a_5403_ = v___x_5410_;
goto v___jp_5402_;
}
}
v___jp_5402_:
{
size_t v___x_5404_; size_t v___x_5405_; 
v___x_5404_ = ((size_t)1ULL);
v___x_5405_ = lean_usize_add(v_i_5397_, v___x_5404_);
v_i_5397_ = v___x_5405_;
v_b_5398_ = v_a_5403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5420_, lean_object* v_as_5421_, lean_object* v_sz_5422_, lean_object* v_i_5423_, lean_object* v_b_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
size_t v_sz_boxed_5428_; size_t v_i_boxed_5429_; lean_object* v_res_5430_; 
v_sz_boxed_5428_ = lean_unbox_usize(v_sz_5422_);
lean_dec(v_sz_5422_);
v_i_boxed_5429_ = lean_unbox_usize(v_i_5423_);
lean_dec(v_i_5423_);
v_res_5430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5420_, v_as_5421_, v_sz_boxed_5428_, v_i_boxed_5429_, v_b_5424_, v___y_5425_, v___y_5426_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec_ref(v_as_5421_);
lean_dec_ref(v___y_5420_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v___x_5441_; lean_object* v_env_5442_; uint8_t v___x_5443_; lean_object* v_fieldNames_5444_; lean_object* v___x_5445_; size_t v_sz_5446_; size_t v___x_5447_; lean_object* v___x_5448_; 
v___x_5441_ = lean_st_ref_get(v___y_5439_);
v_env_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc_ref(v_env_5442_);
lean_dec(v___x_5441_);
v___x_5443_ = 0;
v_fieldNames_5444_ = l_Lean_getStructureFieldsFlattened(v_env_5442_, v_structName_5431_, v___x_5443_);
v___x_5445_ = lean_box(0);
v_sz_5446_ = lean_array_size(v_fieldNames_5444_);
v___x_5447_ = ((size_t)0ULL);
v___x_5448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5432_, v_fieldNames_5444_, v_sz_5446_, v___x_5447_, v___x_5445_, v___y_5433_, v___y_5434_);
lean_dec_ref(v_fieldNames_5444_);
if (lean_obj_tag(v___x_5448_) == 0)
{
lean_object* v_a_5449_; 
v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_a_5449_);
if (lean_obj_tag(v_a_5449_) == 0)
{
lean_dec_ref_known(v_a_5449_, 1);
return v___x_5448_;
}
else
{
lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5457_; 
lean_dec_ref_known(v_a_5449_, 1);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5457_ == 0)
{
lean_object* v_unused_5458_; 
v_unused_5458_ = lean_ctor_get(v___x_5448_, 0);
lean_dec(v_unused_5458_);
v___x_5451_ = v___x_5448_;
v_isShared_5452_ = v_isSharedCheck_5457_;
goto v_resetjp_5450_;
}
else
{
lean_dec(v___x_5448_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5457_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; lean_object* v___x_5455_; 
v___x_5453_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 0, v___x_5453_);
v___x_5455_ = v___x_5451_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v___x_5453_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
else
{
return v___x_5448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec_ref(v___y_5460_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5471_, lean_object* v_pos_5472_, lean_object* v_completionInfoPos_5473_, lean_object* v_ctx_5474_, lean_object* v_lctx_5475_, lean_object* v_id_5476_, lean_object* v_structName_5477_, lean_object* v_a_5478_){
_start:
{
lean_object* v___y_5481_; 
if (lean_obj_tag(v_id_5476_) == 0)
{
lean_object* v___x_5484_; 
v___x_5484_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5481_ = v___x_5484_;
goto v___jp_5480_;
}
else
{
lean_object* v_val_5485_; uint8_t v___x_5486_; lean_object* v___x_5487_; 
v_val_5485_ = lean_ctor_get(v_id_5476_, 0);
lean_inc(v_val_5485_);
lean_dec_ref_known(v_id_5476_, 1);
v___x_5486_ = 1;
v___x_5487_ = l_Lean_Name_toString(v_val_5485_, v___x_5486_);
v___y_5481_ = v___x_5487_;
goto v___jp_5480_;
}
v___jp_5480_:
{
lean_object* v___f_5482_; lean_object* v___x_5483_; 
v___f_5482_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5482_, 0, v_structName_5477_);
lean_closure_set(v___f_5482_, 1, v___y_5481_);
v___x_5483_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5471_, v_pos_5472_, v_completionInfoPos_5473_, v_ctx_5474_, v_lctx_5475_, v___f_5482_, v_a_5478_);
return v___x_5483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5488_, lean_object* v_pos_5489_, lean_object* v_completionInfoPos_5490_, lean_object* v_ctx_5491_, lean_object* v_lctx_5492_, lean_object* v_id_5493_, lean_object* v_structName_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_){
_start:
{
lean_object* v_res_5497_; 
v_res_5497_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5488_, v_pos_5489_, v_completionInfoPos_5490_, v_ctx_5491_, v_lctx_5492_, v_id_5493_, v_structName_5494_, v_a_5495_);
lean_dec_ref(v_a_5495_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5498_, lean_object* v_as_5499_, size_t v_sz_5500_, size_t v_i_5501_, lean_object* v_b_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v___x_5511_; 
v___x_5511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5498_, v_as_5499_, v_sz_5500_, v_i_5501_, v_b_5502_, v___y_5503_, v___y_5504_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5512_, lean_object* v_as_5513_, lean_object* v_sz_5514_, lean_object* v_i_5515_, lean_object* v_b_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
size_t v_sz_boxed_5525_; size_t v_i_boxed_5526_; lean_object* v_res_5527_; 
v_sz_boxed_5525_ = lean_unbox_usize(v_sz_5514_);
lean_dec(v_sz_5514_);
v_i_boxed_5526_ = lean_unbox_usize(v_i_5515_);
lean_dec(v_i_5515_);
v_res_5527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5512_, v_as_5513_, v_sz_boxed_5525_, v_i_boxed_5526_, v_b_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec_ref(v___y_5519_);
lean_dec(v___y_5518_);
lean_dec_ref(v___y_5517_);
lean_dec_ref(v_as_5513_);
lean_dec_ref(v___y_5512_);
return v_res_5527_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0(void){
_start:
{
uint32_t v___x_5528_; lean_object* v___x_5529_; 
v___x_5528_ = 32;
v___x_5529_ = l_Char_utf8Size(v___x_5528_);
return v___x_5529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5530_, lean_object* v_caps_5531_, lean_object* v_mkItem_5532_, lean_object* v_ctx_5533_, lean_object* v_stx_5534_, uint8_t v_snd_5535_, lean_object* v_x_5536_, lean_object* v_____s_5537_){
_start:
{
lean_object* v_fst_5538_; lean_object* v_snd_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5592_; 
v_fst_5538_ = lean_ctor_get(v_x_5536_, 0);
v_snd_5539_ = lean_ctor_get(v_x_5536_, 1);
v_isSharedCheck_5592_ = !lean_is_exclusive(v_x_5536_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5541_ = v_x_5536_;
v_isShared_5542_ = v_isSharedCheck_5592_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_snd_5539_);
lean_inc(v_fst_5538_);
lean_dec(v_x_5536_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5592_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___y_5544_; uint8_t v___x_5548_; lean_object* v___x_5549_; lean_object* v___y_5551_; lean_object* v___y_5552_; uint8_t v___x_5581_; 
v___x_5548_ = 1;
lean_inc(v_fst_5538_);
v___x_5549_ = l_Lean_Name_toString(v_fst_5538_, v___x_5548_);
v___x_5581_ = l_String_charactersIn(v_fst_5530_, v___x_5549_);
if (v___x_5581_ == 0)
{
lean_object* v___x_5584_; 
lean_dec_ref(v___x_5549_);
lean_del_object(v___x_5541_);
lean_dec(v_snd_5539_);
lean_dec(v_fst_5538_);
lean_dec_ref(v_ctx_5533_);
lean_dec_ref(v_mkItem_5532_);
v___x_5584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5584_, 0, v_____s_5537_);
return v___x_5584_;
}
else
{
lean_object* v_textDocument_x3f_5585_; 
v_textDocument_x3f_5585_ = lean_ctor_get(v_caps_5531_, 0);
if (lean_obj_tag(v_textDocument_x3f_5585_) == 0)
{
goto v___jp_5582_;
}
else
{
lean_object* v_val_5586_; lean_object* v_completion_x3f_5587_; 
v_val_5586_ = lean_ctor_get(v_textDocument_x3f_5585_, 0);
v_completion_x3f_5587_ = lean_ctor_get(v_val_5586_, 0);
if (lean_obj_tag(v_completion_x3f_5587_) == 0)
{
goto v___jp_5582_;
}
else
{
lean_object* v_val_5588_; 
v_val_5588_ = lean_ctor_get(v_completion_x3f_5587_, 0);
if (lean_obj_tag(v_val_5588_) == 0)
{
goto v___jp_5582_;
}
else
{
lean_object* v_val_5589_; 
v_val_5589_ = lean_ctor_get(v_val_5588_, 0);
if (lean_obj_tag(v_val_5589_) == 0)
{
goto v___jp_5582_;
}
else
{
lean_object* v_val_5590_; uint8_t v___x_5591_; 
v_val_5590_ = lean_ctor_get(v_val_5589_, 0);
v___x_5591_ = lean_unbox(v_val_5590_);
if (v___x_5591_ == 0)
{
goto v___jp_5582_;
}
else
{
goto v___jp_5570_;
}
}
}
}
}
}
v___jp_5543_:
{
lean_object* v___x_5545_; lean_object* v_items_5546_; lean_object* v___x_5547_; 
v___x_5545_ = lean_apply_3(v_mkItem_5532_, v_fst_5538_, v_snd_5539_, v___y_5544_);
v_items_5546_ = lean_array_push(v_____s_5537_, v___x_5545_);
v___x_5547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5547_, 0, v_items_5546_);
return v___x_5547_;
}
v___jp_5550_:
{
lean_object* v_toCommandContextInfo_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5567_; 
v_toCommandContextInfo_5553_ = lean_ctor_get(v_ctx_5533_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v_ctx_5533_);
if (v_isSharedCheck_5567_ == 0)
{
lean_object* v_unused_5568_; lean_object* v_unused_5569_; 
v_unused_5568_ = lean_ctor_get(v_ctx_5533_, 2);
lean_dec(v_unused_5568_);
v_unused_5569_ = lean_ctor_get(v_ctx_5533_, 1);
lean_dec(v_unused_5569_);
v___x_5555_ = v_ctx_5533_;
v_isShared_5556_ = v_isSharedCheck_5567_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_toCommandContextInfo_5553_);
lean_dec(v_ctx_5533_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5567_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v_fileMap_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v_range_5561_; 
v_fileMap_5557_ = lean_ctor_get(v_toCommandContextInfo_5553_, 2);
lean_inc_ref_n(v_fileMap_5557_, 2);
lean_dec_ref(v_toCommandContextInfo_5553_);
v___x_5558_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5557_, v___y_5551_);
lean_dec(v___y_5551_);
v___x_5559_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5557_, v___y_5552_);
lean_dec(v___y_5552_);
if (v_isShared_5542_ == 0)
{
lean_ctor_set(v___x_5541_, 1, v___x_5559_);
lean_ctor_set(v___x_5541_, 0, v___x_5558_);
v_range_5561_ = v___x_5541_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5559_);
v_range_5561_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5563_; 
lean_inc_ref(v_range_5561_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 2, v_range_5561_);
lean_ctor_set(v___x_5555_, 1, v_range_5561_);
lean_ctor_set(v___x_5555_, 0, v___x_5549_);
v___x_5563_ = v___x_5555_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5549_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v_range_5561_);
lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_range_5561_);
v___x_5563_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5564_; 
v___x_5564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5563_);
v___y_5544_ = v___x_5564_;
goto v___jp_5543_;
}
}
}
}
v___jp_5570_:
{
uint8_t v___x_5571_; lean_object* v___x_5572_; 
v___x_5571_ = 0;
v___x_5572_ = l_Lean_Syntax_getRange_x3f(v_stx_5534_, v___x_5571_);
if (lean_obj_tag(v___x_5572_) == 1)
{
lean_object* v_val_5573_; 
v_val_5573_ = lean_ctor_get(v___x_5572_, 0);
lean_inc(v_val_5573_);
lean_dec_ref_known(v___x_5572_, 1);
if (v_snd_5535_ == 0)
{
lean_object* v_start_5574_; lean_object* v_stop_5575_; 
v_start_5574_ = lean_ctor_get(v_val_5573_, 0);
lean_inc(v_start_5574_);
v_stop_5575_ = lean_ctor_get(v_val_5573_, 1);
lean_inc(v_stop_5575_);
lean_dec(v_val_5573_);
v___y_5551_ = v_start_5574_;
v___y_5552_ = v_stop_5575_;
goto v___jp_5550_;
}
else
{
lean_object* v_start_5576_; lean_object* v_stop_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
v_start_5576_ = lean_ctor_get(v_val_5573_, 0);
lean_inc(v_start_5576_);
v_stop_5577_ = lean_ctor_get(v_val_5573_, 1);
lean_inc(v_stop_5577_);
lean_dec(v_val_5573_);
v___x_5578_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5579_ = lean_nat_add(v_stop_5577_, v___x_5578_);
lean_dec(v_stop_5577_);
v___y_5551_ = v_start_5576_;
v___y_5552_ = v___x_5579_;
goto v___jp_5550_;
}
}
else
{
lean_object* v___x_5580_; 
lean_dec(v___x_5572_);
lean_dec_ref(v___x_5549_);
lean_del_object(v___x_5541_);
lean_dec_ref(v_ctx_5533_);
v___x_5580_ = lean_box(0);
v___y_5544_ = v___x_5580_;
goto v___jp_5543_;
}
}
v___jp_5582_:
{
if (v___x_5581_ == 0)
{
goto v___jp_5570_;
}
else
{
lean_object* v___x_5583_; 
lean_dec_ref(v___x_5549_);
lean_del_object(v___x_5541_);
lean_dec_ref(v_ctx_5533_);
v___x_5583_ = lean_box(0);
v___y_5544_ = v___x_5583_;
goto v___jp_5543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5593_, lean_object* v_caps_5594_, lean_object* v_mkItem_5595_, lean_object* v_ctx_5596_, lean_object* v_stx_5597_, lean_object* v_snd_5598_, lean_object* v_x_5599_, lean_object* v_____s_5600_){
_start:
{
uint8_t v_snd_1079__boxed_5601_; lean_object* v_res_5602_; 
v_snd_1079__boxed_5601_ = lean_unbox(v_snd_5598_);
v_res_5602_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5593_, v_caps_5594_, v_mkItem_5595_, v_ctx_5596_, v_stx_5597_, v_snd_1079__boxed_5601_, v_x_5599_, v_____s_5600_);
lean_dec(v_stx_5597_);
lean_dec_ref(v_caps_5594_);
lean_dec_ref(v_fst_5593_);
return v_res_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5604_, lean_object* v_entries_5605_, lean_object* v_stx_5606_, lean_object* v_caps_5607_, lean_object* v_ctx_5608_, lean_object* v_mkItem_5609_){
_start:
{
lean_object* v_fst_5611_; uint8_t v_snd_5612_; uint8_t v___x_5617_; lean_object* v___x_5618_; 
v___x_5617_ = 0;
v___x_5618_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5606_, v___x_5617_, v___x_5617_);
if (lean_obj_tag(v___x_5618_) == 0)
{
lean_object* v___x_5619_; 
v___x_5619_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5611_ = v___x_5619_;
v_snd_5612_ = v___x_5617_;
goto v___jp_5610_;
}
else
{
lean_object* v_val_5620_; lean_object* v_str_5621_; lean_object* v_startPos_5622_; lean_object* v_stopPos_5623_; uint8_t v___y_5625_; uint8_t v___x_5627_; 
v_val_5620_ = lean_ctor_get(v___x_5618_, 0);
lean_inc(v_val_5620_);
lean_dec_ref_known(v___x_5618_, 1);
v_str_5621_ = lean_ctor_get(v_val_5620_, 0);
lean_inc_ref(v_str_5621_);
v_startPos_5622_ = lean_ctor_get(v_val_5620_, 1);
lean_inc(v_startPos_5622_);
v_stopPos_5623_ = lean_ctor_get(v_val_5620_, 2);
lean_inc(v_stopPos_5623_);
lean_dec(v_val_5620_);
v___x_5627_ = lean_string_utf8_at_end(v_str_5621_, v_stopPos_5623_);
if (v___x_5627_ == 0)
{
uint32_t v___x_5628_; uint32_t v___x_5629_; uint8_t v___x_5630_; 
v___x_5628_ = lean_string_utf8_get(v_str_5621_, v_stopPos_5623_);
v___x_5629_ = 46;
v___x_5630_ = lean_uint32_dec_eq(v___x_5628_, v___x_5629_);
if (v___x_5630_ == 0)
{
v___y_5625_ = v___x_5630_;
goto v___jp_5624_;
}
else
{
lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; 
v___x_5631_ = lean_string_utf8_extract(v_str_5621_, v_startPos_5622_, v_stopPos_5623_);
lean_dec(v_stopPos_5623_);
lean_dec(v_startPos_5622_);
lean_dec_ref(v_str_5621_);
v___x_5632_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5633_ = lean_string_append(v___x_5631_, v___x_5632_);
v_fst_5611_ = v___x_5633_;
v_snd_5612_ = v___x_5630_;
goto v___jp_5610_;
}
}
else
{
v___y_5625_ = v___x_5617_;
goto v___jp_5624_;
}
v___jp_5624_:
{
lean_object* v___x_5626_; 
v___x_5626_ = lean_string_utf8_extract(v_str_5621_, v_startPos_5622_, v_stopPos_5623_);
lean_dec(v_stopPos_5623_);
lean_dec(v_startPos_5622_);
lean_dec_ref(v_str_5621_);
v_fst_5611_ = v___x_5626_;
v_snd_5612_ = v___y_5625_;
goto v___jp_5610_;
}
}
v___jp_5610_:
{
lean_object* v___x_5613_; lean_object* v___f_5614_; lean_object* v_items_5615_; lean_object* v___x_5616_; 
v___x_5613_ = lean_box(v_snd_5612_);
v___f_5614_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5614_, 0, v_fst_5611_);
lean_closure_set(v___f_5614_, 1, v_caps_5607_);
lean_closure_set(v___f_5614_, 2, v_mkItem_5609_);
lean_closure_set(v___f_5614_, 3, v_ctx_5608_);
lean_closure_set(v___f_5614_, 4, v_stx_5606_);
lean_closure_set(v___f_5614_, 5, v___x_5613_);
v_items_5615_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5616_ = lean_apply_4(v_inst_5604_, lean_box(0), v_entries_5605_, v_items_5615_, v___f_5614_);
return v___x_5616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5634_, lean_object* v_00_u03b1_5635_, lean_object* v_inst_5636_, lean_object* v_entries_5637_, lean_object* v_stx_5638_, lean_object* v_caps_5639_, lean_object* v_ctx_5640_, lean_object* v_mkItem_5641_){
_start:
{
lean_object* v___x_5642_; 
v___x_5642_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5636_, v_entries_5637_, v_stx_5638_, v_caps_5639_, v_ctx_5640_, v_mkItem_5641_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v_options_5648_, lean_object* v_completionInfoPos_5649_, lean_object* v_uri_5650_, lean_object* v_pos_5651_, lean_object* v_name_5652_, lean_object* v_decl_5653_, lean_object* v_textEdit_x3f_5654_){
_start:
{
lean_object* v_defValue_5655_; lean_object* v_descr_5656_; lean_object* v_map_5657_; uint8_t v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___y_5662_; lean_object* v___x_5675_; 
v_defValue_5655_ = lean_ctor_get(v_decl_5653_, 2);
lean_inc_ref(v_defValue_5655_);
v_descr_5656_ = lean_ctor_get(v_decl_5653_, 3);
lean_inc_ref(v_descr_5656_);
lean_dec_ref(v_decl_5653_);
v_map_5657_ = lean_ctor_get(v_options_5648_, 0);
v___x_5658_ = 1;
lean_inc(v_name_5652_);
v___x_5659_ = l_Lean_Name_toString(v_name_5652_, v___x_5658_);
v___x_5660_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5675_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5657_, v_name_5652_);
lean_dec(v_name_5652_);
if (lean_obj_tag(v___x_5675_) == 0)
{
v___y_5662_ = v_defValue_5655_;
goto v___jp_5661_;
}
else
{
if (lean_obj_tag(v___x_5675_) == 0)
{
v___y_5662_ = v_defValue_5655_;
goto v___jp_5661_;
}
else
{
lean_object* v_val_5676_; 
lean_dec_ref(v_defValue_5655_);
v_val_5676_ = lean_ctor_get(v___x_5675_, 0);
lean_inc(v_val_5676_);
lean_dec_ref_known(v___x_5675_, 1);
v___y_5662_ = v_val_5676_;
goto v___jp_5661_;
}
}
v___jp_5661_:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; 
v___x_5663_ = lean_data_value_to_string(v___y_5662_);
v___x_5664_ = lean_string_append(v___x_5660_, v___x_5663_);
lean_dec_ref(v___x_5663_);
v___x_5665_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5666_ = lean_string_append(v___x_5664_, v___x_5665_);
v___x_5667_ = lean_string_append(v___x_5666_, v_descr_5656_);
lean_dec_ref(v_descr_5656_);
v___x_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
v___x_5669_ = lean_box(0);
v___x_5670_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5671_, 0, v_completionInfoPos_5649_);
v___x_5672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5672_, 0, v_uri_5650_);
lean_ctor_set(v___x_5672_, 1, v_pos_5651_);
lean_ctor_set(v___x_5672_, 2, v___x_5671_);
lean_ctor_set(v___x_5672_, 3, v___x_5669_);
v___x_5673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
v___x_5674_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5659_);
lean_ctor_set(v___x_5674_, 1, v___x_5668_);
lean_ctor_set(v___x_5674_, 2, v___x_5669_);
lean_ctor_set(v___x_5674_, 3, v___x_5670_);
lean_ctor_set(v___x_5674_, 4, v_textEdit_x3f_5654_);
lean_ctor_set(v___x_5674_, 5, v___x_5669_);
lean_ctor_set(v___x_5674_, 6, v___x_5673_);
lean_ctor_set(v___x_5674_, 7, v___x_5669_);
return v___x_5674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v_options_5677_, lean_object* v_completionInfoPos_5678_, lean_object* v_uri_5679_, lean_object* v_pos_5680_, lean_object* v_name_5681_, lean_object* v_decl_5682_, lean_object* v_textEdit_x3f_5683_){
_start:
{
lean_object* v_res_5684_; 
v_res_5684_ = l_Lean_Server_Completion_optionCompletion___lam__0(v_options_5677_, v_completionInfoPos_5678_, v_uri_5679_, v_pos_5680_, v_name_5681_, v_decl_5682_, v_textEdit_x3f_5683_);
lean_dec_ref(v_options_5677_);
return v_res_5684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5685_, lean_object* v_stx_5686_, lean_object* v_ctx_5687_, uint8_t v_snd_5688_, lean_object* v_fst_5689_, lean_object* v_caps_5690_, lean_object* v_init_5691_, lean_object* v_x_5692_){
_start:
{
if (lean_obj_tag(v_x_5692_) == 0)
{
lean_object* v_k_5693_; lean_object* v_v_5694_; lean_object* v_l_5695_; lean_object* v_r_5696_; lean_object* v___x_5697_; lean_object* v_a_5698_; lean_object* v___y_5700_; uint8_t v___x_5704_; lean_object* v___x_5705_; lean_object* v___y_5707_; lean_object* v___y_5708_; uint8_t v___x_5727_; 
v_k_5693_ = lean_ctor_get(v_x_5692_, 1);
lean_inc_n(v_k_5693_, 2);
v_v_5694_ = lean_ctor_get(v_x_5692_, 2);
lean_inc(v_v_5694_);
v_l_5695_ = lean_ctor_get(v_x_5692_, 3);
lean_inc(v_l_5695_);
v_r_5696_ = lean_ctor_get(v_x_5692_, 4);
lean_inc(v_r_5696_);
lean_dec_ref_known(v_x_5692_, 5);
lean_inc_ref(v_ctx_5687_);
lean_inc_ref(v_mkItem_5685_);
v___x_5697_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5685_, v_stx_5686_, v_ctx_5687_, v_snd_5688_, v_fst_5689_, v_caps_5690_, v_init_5691_, v_l_5695_);
v_a_5698_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5698_);
v___x_5704_ = 1;
v___x_5705_ = l_Lean_Name_toString(v_k_5693_, v___x_5704_);
v___x_5727_ = l_String_charactersIn(v_fst_5689_, v___x_5705_);
if (v___x_5727_ == 0)
{
lean_object* v_a_5730_; 
lean_dec_ref(v___x_5705_);
lean_dec(v_a_5698_);
lean_dec(v_v_5694_);
lean_dec(v_k_5693_);
v_a_5730_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5730_);
lean_dec_ref(v___x_5697_);
v_init_5691_ = v_a_5730_;
v_x_5692_ = v_r_5696_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5732_; 
lean_dec_ref(v___x_5697_);
v_textDocument_x3f_5732_ = lean_ctor_get(v_caps_5690_, 0);
if (lean_obj_tag(v_textDocument_x3f_5732_) == 0)
{
goto v___jp_5728_;
}
else
{
lean_object* v_val_5733_; lean_object* v_completion_x3f_5734_; 
v_val_5733_ = lean_ctor_get(v_textDocument_x3f_5732_, 0);
v_completion_x3f_5734_ = lean_ctor_get(v_val_5733_, 0);
if (lean_obj_tag(v_completion_x3f_5734_) == 0)
{
goto v___jp_5728_;
}
else
{
lean_object* v_val_5735_; 
v_val_5735_ = lean_ctor_get(v_completion_x3f_5734_, 0);
if (lean_obj_tag(v_val_5735_) == 0)
{
goto v___jp_5728_;
}
else
{
lean_object* v_val_5736_; 
v_val_5736_ = lean_ctor_get(v_val_5735_, 0);
if (lean_obj_tag(v_val_5736_) == 0)
{
goto v___jp_5728_;
}
else
{
lean_object* v_val_5737_; uint8_t v___x_5738_; 
v_val_5737_ = lean_ctor_get(v_val_5736_, 0);
v___x_5738_ = lean_unbox(v_val_5737_);
if (v___x_5738_ == 0)
{
goto v___jp_5728_;
}
else
{
goto v___jp_5716_;
}
}
}
}
}
}
v___jp_5699_:
{
lean_object* v___x_5701_; lean_object* v_items_5702_; 
lean_inc_ref(v_mkItem_5685_);
v___x_5701_ = lean_apply_3(v_mkItem_5685_, v_k_5693_, v_v_5694_, v___y_5700_);
v_items_5702_ = lean_array_push(v_a_5698_, v___x_5701_);
v_init_5691_ = v_items_5702_;
v_x_5692_ = v_r_5696_;
goto _start;
}
v___jp_5706_:
{
lean_object* v_toCommandContextInfo_5709_; lean_object* v_fileMap_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v_range_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; 
v_toCommandContextInfo_5709_ = lean_ctor_get(v_ctx_5687_, 0);
v_fileMap_5710_ = lean_ctor_get(v_toCommandContextInfo_5709_, 2);
lean_inc_ref_n(v_fileMap_5710_, 2);
v___x_5711_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5710_, v___y_5707_);
lean_dec(v___y_5707_);
v___x_5712_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5710_, v___y_5708_);
lean_dec(v___y_5708_);
v_range_5713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5713_, 0, v___x_5711_);
lean_ctor_set(v_range_5713_, 1, v___x_5712_);
lean_inc_ref(v_range_5713_);
v___x_5714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5705_);
lean_ctor_set(v___x_5714_, 1, v_range_5713_);
lean_ctor_set(v___x_5714_, 2, v_range_5713_);
v___x_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
v___y_5700_ = v___x_5715_;
goto v___jp_5699_;
}
v___jp_5716_:
{
uint8_t v___x_5717_; lean_object* v___x_5718_; 
v___x_5717_ = 0;
v___x_5718_ = l_Lean_Syntax_getRange_x3f(v_stx_5686_, v___x_5717_);
if (lean_obj_tag(v___x_5718_) == 1)
{
lean_object* v_val_5719_; 
v_val_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc(v_val_5719_);
lean_dec_ref_known(v___x_5718_, 1);
if (v_snd_5688_ == 0)
{
lean_object* v_start_5720_; lean_object* v_stop_5721_; 
v_start_5720_ = lean_ctor_get(v_val_5719_, 0);
lean_inc(v_start_5720_);
v_stop_5721_ = lean_ctor_get(v_val_5719_, 1);
lean_inc(v_stop_5721_);
lean_dec(v_val_5719_);
v___y_5707_ = v_start_5720_;
v___y_5708_ = v_stop_5721_;
goto v___jp_5706_;
}
else
{
lean_object* v_start_5722_; lean_object* v_stop_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; 
v_start_5722_ = lean_ctor_get(v_val_5719_, 0);
lean_inc(v_start_5722_);
v_stop_5723_ = lean_ctor_get(v_val_5719_, 1);
lean_inc(v_stop_5723_);
lean_dec(v_val_5719_);
v___x_5724_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5725_ = lean_nat_add(v_stop_5723_, v___x_5724_);
lean_dec(v_stop_5723_);
v___y_5707_ = v_start_5722_;
v___y_5708_ = v___x_5725_;
goto v___jp_5706_;
}
}
else
{
lean_object* v___x_5726_; 
lean_dec(v___x_5718_);
lean_dec_ref(v___x_5705_);
v___x_5726_ = lean_box(0);
v___y_5700_ = v___x_5726_;
goto v___jp_5699_;
}
}
v___jp_5728_:
{
if (v___x_5727_ == 0)
{
goto v___jp_5716_;
}
else
{
lean_object* v___x_5729_; 
lean_dec_ref(v___x_5705_);
v___x_5729_ = lean_box(0);
v___y_5700_ = v___x_5729_;
goto v___jp_5699_;
}
}
}
else
{
lean_object* v___x_5739_; 
lean_dec_ref(v_ctx_5687_);
lean_dec_ref(v_mkItem_5685_);
v___x_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5739_, 0, v_init_5691_);
return v___x_5739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5740_, lean_object* v_stx_5741_, lean_object* v_ctx_5742_, lean_object* v_snd_5743_, lean_object* v_fst_5744_, lean_object* v_caps_5745_, lean_object* v_init_5746_, lean_object* v_x_5747_){
_start:
{
uint8_t v_snd_1415__boxed_5748_; lean_object* v_res_5749_; 
v_snd_1415__boxed_5748_ = lean_unbox(v_snd_5743_);
v_res_5749_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5740_, v_stx_5741_, v_ctx_5742_, v_snd_1415__boxed_5748_, v_fst_5744_, v_caps_5745_, v_init_5746_, v_x_5747_);
lean_dec_ref(v_caps_5745_);
lean_dec_ref(v_fst_5744_);
lean_dec(v_stx_5741_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5750_, lean_object* v_stx_5751_, lean_object* v_caps_5752_, lean_object* v_ctx_5753_, lean_object* v_mkItem_5754_){
_start:
{
lean_object* v_fst_5756_; uint8_t v_snd_5757_; uint8_t v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = 0;
v___x_5762_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5751_, v___x_5761_, v___x_5761_);
if (lean_obj_tag(v___x_5762_) == 0)
{
lean_object* v___x_5763_; 
v___x_5763_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5756_ = v___x_5763_;
v_snd_5757_ = v___x_5761_;
goto v___jp_5755_;
}
else
{
lean_object* v_val_5764_; lean_object* v_str_5765_; lean_object* v_startPos_5766_; lean_object* v_stopPos_5767_; uint8_t v___y_5769_; uint8_t v___x_5771_; 
v_val_5764_ = lean_ctor_get(v___x_5762_, 0);
lean_inc(v_val_5764_);
lean_dec_ref_known(v___x_5762_, 1);
v_str_5765_ = lean_ctor_get(v_val_5764_, 0);
lean_inc_ref(v_str_5765_);
v_startPos_5766_ = lean_ctor_get(v_val_5764_, 1);
lean_inc(v_startPos_5766_);
v_stopPos_5767_ = lean_ctor_get(v_val_5764_, 2);
lean_inc(v_stopPos_5767_);
lean_dec(v_val_5764_);
v___x_5771_ = lean_string_utf8_at_end(v_str_5765_, v_stopPos_5767_);
if (v___x_5771_ == 0)
{
uint32_t v___x_5772_; uint32_t v___x_5773_; uint8_t v___x_5774_; 
v___x_5772_ = lean_string_utf8_get(v_str_5765_, v_stopPos_5767_);
v___x_5773_ = 46;
v___x_5774_ = lean_uint32_dec_eq(v___x_5772_, v___x_5773_);
if (v___x_5774_ == 0)
{
v___y_5769_ = v___x_5774_;
goto v___jp_5768_;
}
else
{
lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; 
v___x_5775_ = lean_string_utf8_extract(v_str_5765_, v_startPos_5766_, v_stopPos_5767_);
lean_dec(v_stopPos_5767_);
lean_dec(v_startPos_5766_);
lean_dec_ref(v_str_5765_);
v___x_5776_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5777_ = lean_string_append(v___x_5775_, v___x_5776_);
v_fst_5756_ = v___x_5777_;
v_snd_5757_ = v___x_5774_;
goto v___jp_5755_;
}
}
else
{
v___y_5769_ = v___x_5761_;
goto v___jp_5768_;
}
v___jp_5768_:
{
lean_object* v___x_5770_; 
v___x_5770_ = lean_string_utf8_extract(v_str_5765_, v_startPos_5766_, v_stopPos_5767_);
lean_dec(v_stopPos_5767_);
lean_dec(v_startPos_5766_);
lean_dec_ref(v_str_5765_);
v_fst_5756_ = v___x_5770_;
v_snd_5757_ = v___y_5769_;
goto v___jp_5755_;
}
}
v___jp_5755_:
{
lean_object* v_items_5758_; lean_object* v___x_5759_; lean_object* v_a_5760_; 
v_items_5758_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5759_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5754_, v_stx_5751_, v_ctx_5753_, v_snd_5757_, v_fst_5756_, v_caps_5752_, v_items_5758_, v_entries_5750_);
lean_dec_ref(v_fst_5756_);
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc(v_a_5760_);
lean_dec_ref(v___x_5759_);
return v_a_5760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object* v_entries_5778_, lean_object* v_stx_5779_, lean_object* v_caps_5780_, lean_object* v_ctx_5781_, lean_object* v_mkItem_5782_){
_start:
{
lean_object* v_res_5783_; 
v_res_5783_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_entries_5778_, v_stx_5779_, v_caps_5780_, v_ctx_5781_, v_mkItem_5782_);
lean_dec_ref(v_caps_5780_);
lean_dec(v_stx_5779_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object* v_completionInfoPos_5784_, lean_object* v_uri_5785_, lean_object* v_pos_5786_, lean_object* v_stx_5787_, lean_object* v_caps_5788_, lean_object* v_ctx_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_){
_start:
{
lean_object* v___x_5795_; 
v___x_5795_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5808_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5808_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_5808_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5808_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v_options_5800_; lean_object* v___f_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5806_; 
v_options_5800_ = lean_ctor_get(v___y_5792_, 2);
lean_inc_ref(v_options_5800_);
lean_dec_ref(v___y_5792_);
v___f_5801_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5801_, 0, v_options_5800_);
lean_closure_set(v___f_5801_, 1, v_completionInfoPos_5784_);
lean_closure_set(v___f_5801_, 2, v_uri_5785_);
lean_closure_set(v___f_5801_, 3, v_pos_5786_);
v___x_5802_ = lean_unsigned_to_nat(1u);
v___x_5803_ = l_Lean_Syntax_getArg(v_stx_5787_, v___x_5802_);
v___x_5804_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_a_5796_, v___x_5803_, v_caps_5788_, v_ctx_5789_, v___f_5801_);
lean_dec(v___x_5803_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_5804_);
v___x_5806_ = v___x_5798_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5804_);
v___x_5806_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
return v___x_5806_;
}
}
}
else
{
lean_object* v_a_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5821_; 
lean_dec_ref(v_ctx_5789_);
lean_dec_ref(v_pos_5786_);
lean_dec_ref(v_uri_5785_);
lean_dec(v_completionInfoPos_5784_);
v_a_5809_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5821_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5821_ == 0)
{
v___x_5811_ = v___x_5795_;
v_isShared_5812_ = v_isSharedCheck_5821_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_a_5809_);
lean_dec(v___x_5795_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5821_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v_ref_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5819_; 
v_ref_5813_ = lean_ctor_get(v___y_5792_, 5);
lean_inc(v_ref_5813_);
lean_dec_ref(v___y_5792_);
v___x_5814_ = lean_io_error_to_string(v_a_5809_);
v___x_5815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5815_, 0, v___x_5814_);
v___x_5816_ = l_Lean_MessageData_ofFormat(v___x_5815_);
v___x_5817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5817_, 0, v_ref_5813_);
lean_ctor_set(v___x_5817_, 1, v___x_5816_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 0, v___x_5817_);
v___x_5819_ = v___x_5811_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v___x_5817_);
v___x_5819_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
return v___x_5819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object* v_completionInfoPos_5822_, lean_object* v_uri_5823_, lean_object* v_pos_5824_, lean_object* v_stx_5825_, lean_object* v_caps_5826_, lean_object* v_ctx_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_){
_start:
{
lean_object* v_res_5833_; 
v_res_5833_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5822_, v_uri_5823_, v_pos_5824_, v_stx_5825_, v_caps_5826_, v_ctx_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_);
lean_dec(v___y_5831_);
lean_dec(v___y_5829_);
lean_dec_ref(v___y_5828_);
lean_dec_ref(v_caps_5826_);
lean_dec(v_stx_5825_);
return v_res_5833_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__0(void){
_start:
{
lean_object* v___x_5834_; 
v___x_5834_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5834_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1(void){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5835_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__0, &l_Lean_Server_Completion_optionCompletion___closed__0_once, _init_l_Lean_Server_Completion_optionCompletion___closed__0);
v___x_5836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5835_);
return v___x_5836_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2(void){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5837_ = lean_unsigned_to_nat(32u);
v___x_5838_ = lean_mk_empty_array_with_capacity(v___x_5837_);
v___x_5839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5839_, 0, v___x_5838_);
return v___x_5839_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3(void){
_start:
{
size_t v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5840_ = ((size_t)5ULL);
v___x_5841_ = lean_unsigned_to_nat(0u);
v___x_5842_ = lean_unsigned_to_nat(32u);
v___x_5843_ = lean_mk_empty_array_with_capacity(v___x_5842_);
v___x_5844_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__2, &l_Lean_Server_Completion_optionCompletion___closed__2_once, _init_l_Lean_Server_Completion_optionCompletion___closed__2);
v___x_5845_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5845_, 0, v___x_5844_);
lean_ctor_set(v___x_5845_, 1, v___x_5843_);
lean_ctor_set(v___x_5845_, 2, v___x_5841_);
lean_ctor_set(v___x_5845_, 3, v___x_5841_);
lean_ctor_set_usize(v___x_5845_, 4, v___x_5840_);
return v___x_5845_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4(void){
_start:
{
lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5846_ = lean_box(1);
v___x_5847_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__3, &l_Lean_Server_Completion_optionCompletion___closed__3_once, _init_l_Lean_Server_Completion_optionCompletion___closed__3);
v___x_5848_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__1, &l_Lean_Server_Completion_optionCompletion___closed__1_once, _init_l_Lean_Server_Completion_optionCompletion___closed__1);
v___x_5849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5849_, 0, v___x_5848_);
lean_ctor_set(v___x_5849_, 1, v___x_5847_);
lean_ctor_set(v___x_5849_, 2, v___x_5846_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* v_uri_5850_, lean_object* v_pos_5851_, lean_object* v_completionInfoPos_5852_, lean_object* v_ctx_5853_, lean_object* v_stx_5854_, lean_object* v_caps_5855_){
_start:
{
lean_object* v___f_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
lean_inc_ref(v_ctx_5853_);
v___f_5857_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__1___boxed), 11, 6);
lean_closure_set(v___f_5857_, 0, v_completionInfoPos_5852_);
lean_closure_set(v___f_5857_, 1, v_uri_5850_);
lean_closure_set(v___f_5857_, 2, v_pos_5851_);
lean_closure_set(v___f_5857_, 3, v_stx_5854_);
lean_closure_set(v___f_5857_, 4, v_caps_5855_);
lean_closure_set(v___f_5857_, 5, v_ctx_5853_);
v___x_5858_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5859_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5853_, v___x_5858_, v___f_5857_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* v_uri_5860_, lean_object* v_pos_5861_, lean_object* v_completionInfoPos_5862_, lean_object* v_ctx_5863_, lean_object* v_stx_5864_, lean_object* v_caps_5865_, lean_object* v_a_5866_){
_start:
{
lean_object* v_res_5867_; 
v_res_5867_ = l_Lean_Server_Completion_optionCompletion(v_uri_5860_, v_pos_5861_, v_completionInfoPos_5862_, v_ctx_5863_, v_stx_5864_, v_caps_5865_);
return v_res_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object* v_completionInfoPos_5877_, lean_object* v_uri_5878_, lean_object* v_pos_5879_, lean_object* v_name_5880_, lean_object* v_explan_5881_, lean_object* v_textEdit_x3f_5882_){
_start:
{
lean_object* v_metadata_5883_; lean_object* v_removedVersion_x3f_5884_; uint8_t v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; uint8_t v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; 
v_metadata_5883_ = lean_ctor_get(v_explan_5881_, 1);
v_removedVersion_x3f_5884_ = lean_ctor_get(v_metadata_5883_, 2);
v___x_5885_ = 1;
v___x_5886_ = l_Lean_Name_toString(v_name_5880_, v___x_5885_);
v___x_5887_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1));
v___x_5888_ = 1;
v___x_5889_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_5881_);
v___x_5890_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5890_, 0, v___x_5889_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*1, v___x_5888_);
v___x_5891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5891_, 0, v___x_5890_);
v___x_5892_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5893_ = lean_box(0);
v___x_5894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5894_, 0, v_completionInfoPos_5877_);
v___x_5895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5895_, 0, v_uri_5878_);
lean_ctor_set(v___x_5895_, 1, v_pos_5879_);
lean_ctor_set(v___x_5895_, 2, v___x_5894_);
lean_ctor_set(v___x_5895_, 3, v___x_5893_);
v___x_5896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5895_);
if (lean_obj_tag(v_removedVersion_x3f_5884_) == 0)
{
lean_object* v___x_5897_; 
v___x_5897_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5886_);
lean_ctor_set(v___x_5897_, 1, v___x_5887_);
lean_ctor_set(v___x_5897_, 2, v___x_5891_);
lean_ctor_set(v___x_5897_, 3, v___x_5892_);
lean_ctor_set(v___x_5897_, 4, v_textEdit_x3f_5882_);
lean_ctor_set(v___x_5897_, 5, v___x_5893_);
lean_ctor_set(v___x_5897_, 6, v___x_5896_);
lean_ctor_set(v___x_5897_, 7, v___x_5893_);
return v___x_5897_;
}
else
{
lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5898_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3));
v___x_5899_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5886_);
lean_ctor_set(v___x_5899_, 1, v___x_5887_);
lean_ctor_set(v___x_5899_, 2, v___x_5891_);
lean_ctor_set(v___x_5899_, 3, v___x_5892_);
lean_ctor_set(v___x_5899_, 4, v_textEdit_x3f_5882_);
lean_ctor_set(v___x_5899_, 5, v___x_5893_);
lean_ctor_set(v___x_5899_, 6, v___x_5896_);
lean_ctor_set(v___x_5899_, 7, v___x_5898_);
return v___x_5899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object* v_completionInfoPos_5900_, lean_object* v_uri_5901_, lean_object* v_pos_5902_, lean_object* v_name_5903_, lean_object* v_explan_5904_, lean_object* v_textEdit_x3f_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l_Lean_Server_Completion_errorNameCompletion___lam__0(v_completionInfoPos_5900_, v_uri_5901_, v_pos_5902_, v_name_5903_, v_explan_5904_, v_textEdit_x3f_5905_);
lean_dec_ref(v_explan_5904_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object* v_init_5907_, lean_object* v_x_5908_){
_start:
{
if (lean_obj_tag(v_x_5908_) == 0)
{
lean_object* v_k_5909_; lean_object* v_v_5910_; lean_object* v_l_5911_; lean_object* v_r_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; 
v_k_5909_ = lean_ctor_get(v_x_5908_, 1);
v_v_5910_ = lean_ctor_get(v_x_5908_, 2);
v_l_5911_ = lean_ctor_get(v_x_5908_, 3);
v_r_5912_ = lean_ctor_get(v_x_5908_, 4);
v___x_5913_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5907_, v_l_5911_);
lean_inc(v_v_5910_);
lean_inc(v_k_5909_);
v___x_5914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5914_, 0, v_k_5909_);
lean_ctor_set(v___x_5914_, 1, v_v_5910_);
v___x_5915_ = lean_array_push(v___x_5913_, v___x_5914_);
v_init_5907_ = v___x_5915_;
v_x_5908_ = v_r_5912_;
goto _start;
}
else
{
return v_init_5907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5917_, lean_object* v_x_5918_){
_start:
{
lean_object* v_res_5919_; 
v_res_5919_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5917_, v_x_5918_);
lean_dec(v_x_5918_);
return v_res_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object* v_hi_5920_, lean_object* v_pivot_5921_, lean_object* v_as_5922_, lean_object* v_i_5923_, lean_object* v_k_5924_){
_start:
{
uint8_t v___x_5925_; 
v___x_5925_ = lean_nat_dec_lt(v_k_5924_, v_hi_5920_);
if (v___x_5925_ == 0)
{
lean_object* v___x_5926_; lean_object* v___x_5927_; 
lean_dec(v_k_5924_);
lean_dec_ref(v_pivot_5921_);
v___x_5926_ = lean_array_fswap(v_as_5922_, v_i_5923_, v_hi_5920_);
v___x_5927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5927_, 0, v_i_5923_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
return v___x_5927_;
}
else
{
lean_object* v___x_5928_; lean_object* v_fst_5929_; lean_object* v_fst_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; uint8_t v___x_5933_; 
v___x_5928_ = lean_array_fget_borrowed(v_as_5922_, v_k_5924_);
v_fst_5929_ = lean_ctor_get(v___x_5928_, 0);
v_fst_5930_ = lean_ctor_get(v_pivot_5921_, 0);
lean_inc(v_fst_5929_);
v___x_5931_ = l_Lean_Name_toString(v_fst_5929_, v___x_5925_);
lean_inc(v_fst_5930_);
v___x_5932_ = l_Lean_Name_toString(v_fst_5930_, v___x_5925_);
v___x_5933_ = lean_string_dec_lt(v___x_5931_, v___x_5932_);
lean_dec_ref(v___x_5932_);
lean_dec_ref(v___x_5931_);
if (v___x_5933_ == 0)
{
lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5934_ = lean_unsigned_to_nat(1u);
v___x_5935_ = lean_nat_add(v_k_5924_, v___x_5934_);
lean_dec(v_k_5924_);
v_k_5924_ = v___x_5935_;
goto _start;
}
else
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5937_ = lean_array_fswap(v_as_5922_, v_i_5923_, v_k_5924_);
v___x_5938_ = lean_unsigned_to_nat(1u);
v___x_5939_ = lean_nat_add(v_i_5923_, v___x_5938_);
lean_dec(v_i_5923_);
v___x_5940_ = lean_nat_add(v_k_5924_, v___x_5938_);
lean_dec(v_k_5924_);
v_as_5922_ = v___x_5937_;
v_i_5923_ = v___x_5939_;
v_k_5924_ = v___x_5940_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_hi_5942_, lean_object* v_pivot_5943_, lean_object* v_as_5944_, lean_object* v_i_5945_, lean_object* v_k_5946_){
_start:
{
lean_object* v_res_5947_; 
v_res_5947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5942_, v_pivot_5943_, v_as_5944_, v_i_5945_, v_k_5946_);
lean_dec(v_hi_5942_);
return v_res_5947_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_5948_, lean_object* v_e_5949_, lean_object* v_e_x27_5950_){
_start:
{
lean_object* v_fst_5951_; lean_object* v_fst_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; uint8_t v___x_5955_; 
v_fst_5951_ = lean_ctor_get(v_e_5949_, 0);
lean_inc(v_fst_5951_);
lean_dec_ref(v_e_5949_);
v_fst_5952_ = lean_ctor_get(v_e_x27_5950_, 0);
lean_inc(v_fst_5952_);
lean_dec_ref(v_e_x27_5950_);
v___x_5953_ = l_Lean_Name_toString(v_fst_5951_, v___x_5948_);
v___x_5954_ = l_Lean_Name_toString(v_fst_5952_, v___x_5948_);
v___x_5955_ = lean_string_dec_lt(v___x_5953_, v___x_5954_);
lean_dec_ref(v___x_5954_);
lean_dec_ref(v___x_5953_);
return v___x_5955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_5956_, lean_object* v_e_5957_, lean_object* v_e_x27_5958_){
_start:
{
uint8_t v___x_1599__boxed_5959_; uint8_t v_res_5960_; lean_object* v_r_5961_; 
v___x_1599__boxed_5959_ = lean_unbox(v___x_5956_);
v_res_5960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1599__boxed_5959_, v_e_5957_, v_e_x27_5958_);
v_r_5961_ = lean_box(v_res_5960_);
return v_r_5961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_n_5962_, lean_object* v_as_5963_, lean_object* v_lo_5964_, lean_object* v_hi_5965_){
_start:
{
lean_object* v___y_5967_; uint8_t v___x_5977_; 
v___x_5977_ = lean_nat_dec_lt(v_lo_5964_, v_hi_5965_);
if (v___x_5977_ == 0)
{
lean_dec(v_lo_5964_);
return v_as_5963_;
}
else
{
lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v_mid_5980_; lean_object* v___y_5982_; lean_object* v___y_5988_; lean_object* v___x_5993_; lean_object* v___x_5994_; uint8_t v___x_5995_; 
v___x_5978_ = lean_nat_add(v_lo_5964_, v_hi_5965_);
v___x_5979_ = lean_unsigned_to_nat(1u);
v_mid_5980_ = lean_nat_shiftr(v___x_5978_, v___x_5979_);
lean_dec(v___x_5978_);
v___x_5993_ = lean_array_fget_borrowed(v_as_5963_, v_mid_5980_);
v___x_5994_ = lean_array_fget_borrowed(v_as_5963_, v_lo_5964_);
lean_inc(v___x_5994_);
lean_inc(v___x_5993_);
v___x_5995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5977_, v___x_5993_, v___x_5994_);
if (v___x_5995_ == 0)
{
v___y_5988_ = v_as_5963_;
goto v___jp_5987_;
}
else
{
lean_object* v___x_5996_; 
v___x_5996_ = lean_array_fswap(v_as_5963_, v_lo_5964_, v_mid_5980_);
v___y_5988_ = v___x_5996_;
goto v___jp_5987_;
}
v___jp_5981_:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; uint8_t v___x_5985_; 
v___x_5983_ = lean_array_fget_borrowed(v___y_5982_, v_mid_5980_);
v___x_5984_ = lean_array_fget_borrowed(v___y_5982_, v_hi_5965_);
lean_inc(v___x_5984_);
lean_inc(v___x_5983_);
v___x_5985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5977_, v___x_5983_, v___x_5984_);
if (v___x_5985_ == 0)
{
lean_dec(v_mid_5980_);
v___y_5967_ = v___y_5982_;
goto v___jp_5966_;
}
else
{
lean_object* v___x_5986_; 
v___x_5986_ = lean_array_fswap(v___y_5982_, v_mid_5980_, v_hi_5965_);
lean_dec(v_mid_5980_);
v___y_5967_ = v___x_5986_;
goto v___jp_5966_;
}
}
v___jp_5987_:
{
lean_object* v___x_5989_; lean_object* v___x_5990_; uint8_t v___x_5991_; 
v___x_5989_ = lean_array_fget_borrowed(v___y_5988_, v_hi_5965_);
v___x_5990_ = lean_array_fget_borrowed(v___y_5988_, v_lo_5964_);
lean_inc(v___x_5990_);
lean_inc(v___x_5989_);
v___x_5991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5977_, v___x_5989_, v___x_5990_);
if (v___x_5991_ == 0)
{
v___y_5982_ = v___y_5988_;
goto v___jp_5981_;
}
else
{
lean_object* v___x_5992_; 
v___x_5992_ = lean_array_fswap(v___y_5988_, v_lo_5964_, v_hi_5965_);
v___y_5982_ = v___x_5992_;
goto v___jp_5981_;
}
}
}
v___jp_5966_:
{
lean_object* v_pivot_5968_; lean_object* v___x_5969_; lean_object* v_fst_5970_; lean_object* v_snd_5971_; uint8_t v___x_5972_; 
v_pivot_5968_ = lean_array_fget(v___y_5967_, v_hi_5965_);
lean_inc_n(v_lo_5964_, 2);
v___x_5969_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5965_, v_pivot_5968_, v___y_5967_, v_lo_5964_, v_lo_5964_);
v_fst_5970_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_fst_5970_);
v_snd_5971_ = lean_ctor_get(v___x_5969_, 1);
lean_inc(v_snd_5971_);
lean_dec_ref(v___x_5969_);
v___x_5972_ = lean_nat_dec_le(v_hi_5965_, v_fst_5970_);
if (v___x_5972_ == 0)
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5962_, v_snd_5971_, v_lo_5964_, v_fst_5970_);
v___x_5974_ = lean_unsigned_to_nat(1u);
v___x_5975_ = lean_nat_add(v_fst_5970_, v___x_5974_);
lean_dec(v_fst_5970_);
v_as_5963_ = v___x_5973_;
v_lo_5964_ = v___x_5975_;
goto _start;
}
else
{
lean_dec(v_fst_5970_);
lean_dec(v_lo_5964_);
return v_snd_5971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_n_5997_, lean_object* v_as_5998_, lean_object* v_lo_5999_, lean_object* v_hi_6000_){
_start:
{
lean_object* v_res_6001_; 
v_res_6001_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5997_, v_as_5998_, v_lo_5999_, v_hi_6000_);
lean_dec(v_hi_6000_);
lean_dec(v_n_5997_);
return v_res_6001_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_6004_){
_start:
{
lean_object* v___x_6006_; lean_object* v_env_6007_; lean_object* v___x_6008_; lean_object* v_toEnvExtension_6009_; lean_object* v_asyncMode_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___y_6019_; lean_object* v___y_6020_; uint8_t v___x_6023_; 
v___x_6006_ = lean_st_ref_get(v___y_6004_);
v_env_6007_ = lean_ctor_get(v___x_6006_, 0);
lean_inc_ref(v_env_6007_);
lean_dec(v___x_6006_);
v___x_6008_ = l_Lean_errorExplanationExt;
v_toEnvExtension_6009_ = lean_ctor_get(v___x_6008_, 0);
v_asyncMode_6010_ = lean_ctor_get(v_toEnvExtension_6009_, 2);
v___x_6011_ = lean_box(1);
v___x_6012_ = lean_box(0);
v___x_6013_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6011_, v___x_6008_, v_env_6007_, v_asyncMode_6010_, v___x_6012_);
v___x_6014_ = lean_unsigned_to_nat(0u);
v___x_6015_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_6016_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_6015_, v___x_6013_);
lean_dec(v___x_6013_);
v___x_6017_ = lean_array_get_size(v___x_6016_);
v___x_6023_ = lean_nat_dec_eq(v___x_6017_, v___x_6014_);
if (v___x_6023_ == 0)
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___y_6027_; uint8_t v___x_6029_; 
v___x_6024_ = lean_unsigned_to_nat(1u);
v___x_6025_ = lean_nat_sub(v___x_6017_, v___x_6024_);
v___x_6029_ = lean_nat_dec_le(v___x_6014_, v___x_6025_);
if (v___x_6029_ == 0)
{
lean_inc(v___x_6025_);
v___y_6027_ = v___x_6025_;
goto v___jp_6026_;
}
else
{
v___y_6027_ = v___x_6014_;
goto v___jp_6026_;
}
v___jp_6026_:
{
uint8_t v___x_6028_; 
v___x_6028_ = lean_nat_dec_le(v___y_6027_, v___x_6025_);
if (v___x_6028_ == 0)
{
lean_dec(v___x_6025_);
lean_inc(v___y_6027_);
v___y_6019_ = v___y_6027_;
v___y_6020_ = v___y_6027_;
goto v___jp_6018_;
}
else
{
v___y_6019_ = v___y_6027_;
v___y_6020_ = v___x_6025_;
goto v___jp_6018_;
}
}
}
else
{
lean_object* v___x_6030_; 
v___x_6030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6016_);
return v___x_6030_;
}
v___jp_6018_:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_6017_, v___x_6016_, v___y_6019_, v___y_6020_);
lean_dec(v___y_6020_);
v___x_6022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
return v___x_6022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_6031_, lean_object* v___y_6032_){
_start:
{
lean_object* v_res_6033_; 
v_res_6033_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6031_);
lean_dec(v___y_6031_);
return v_res_6033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_6034_, lean_object* v_stx_6035_, lean_object* v_ctx_6036_, uint8_t v_snd_6037_, lean_object* v_fst_6038_, lean_object* v_caps_6039_, lean_object* v_as_6040_, size_t v_sz_6041_, size_t v_i_6042_, lean_object* v_b_6043_){
_start:
{
lean_object* v_a_6045_; uint8_t v___x_6049_; 
v___x_6049_ = lean_usize_dec_lt(v_i_6042_, v_sz_6041_);
if (v___x_6049_ == 0)
{
lean_dec_ref(v_ctx_6036_);
lean_dec_ref(v_mkItem_6034_);
return v_b_6043_;
}
else
{
lean_object* v_a_6050_; lean_object* v_fst_6051_; lean_object* v_snd_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6094_; 
v_a_6050_ = lean_array_uget(v_as_6040_, v_i_6042_);
v_fst_6051_ = lean_ctor_get(v_a_6050_, 0);
v_snd_6052_ = lean_ctor_get(v_a_6050_, 1);
v_isSharedCheck_6094_ = !lean_is_exclusive(v_a_6050_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6054_ = v_a_6050_;
v_isShared_6055_ = v_isSharedCheck_6094_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_snd_6052_);
lean_inc(v_fst_6051_);
lean_dec(v_a_6050_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6094_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v___y_6057_; lean_object* v___x_6060_; lean_object* v___y_6062_; lean_object* v___y_6063_; uint8_t v___x_6084_; 
lean_inc(v_fst_6051_);
v___x_6060_ = l_Lean_Name_toString(v_fst_6051_, v___x_6049_);
v___x_6084_ = l_String_charactersIn(v_fst_6038_, v___x_6060_);
if (v___x_6084_ == 0)
{
lean_dec_ref(v___x_6060_);
lean_del_object(v___x_6054_);
lean_dec(v_snd_6052_);
lean_dec(v_fst_6051_);
v_a_6045_ = v_b_6043_;
goto v___jp_6044_;
}
else
{
lean_object* v_textDocument_x3f_6087_; 
v_textDocument_x3f_6087_ = lean_ctor_get(v_caps_6039_, 0);
if (lean_obj_tag(v_textDocument_x3f_6087_) == 0)
{
goto v___jp_6085_;
}
else
{
lean_object* v_val_6088_; lean_object* v_completion_x3f_6089_; 
v_val_6088_ = lean_ctor_get(v_textDocument_x3f_6087_, 0);
v_completion_x3f_6089_ = lean_ctor_get(v_val_6088_, 0);
if (lean_obj_tag(v_completion_x3f_6089_) == 0)
{
goto v___jp_6085_;
}
else
{
lean_object* v_val_6090_; 
v_val_6090_ = lean_ctor_get(v_completion_x3f_6089_, 0);
if (lean_obj_tag(v_val_6090_) == 0)
{
goto v___jp_6085_;
}
else
{
lean_object* v_val_6091_; 
v_val_6091_ = lean_ctor_get(v_val_6090_, 0);
if (lean_obj_tag(v_val_6091_) == 0)
{
goto v___jp_6085_;
}
else
{
lean_object* v_val_6092_; uint8_t v___x_6093_; 
v_val_6092_ = lean_ctor_get(v_val_6091_, 0);
v___x_6093_ = lean_unbox(v_val_6092_);
if (v___x_6093_ == 0)
{
goto v___jp_6085_;
}
else
{
goto v___jp_6073_;
}
}
}
}
}
}
v___jp_6056_:
{
lean_object* v___x_6058_; lean_object* v_items_6059_; 
lean_inc_ref(v_mkItem_6034_);
v___x_6058_ = lean_apply_3(v_mkItem_6034_, v_fst_6051_, v_snd_6052_, v___y_6057_);
v_items_6059_ = lean_array_push(v_b_6043_, v___x_6058_);
v_a_6045_ = v_items_6059_;
goto v___jp_6044_;
}
v___jp_6061_:
{
lean_object* v_toCommandContextInfo_6064_; lean_object* v_fileMap_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v_range_6069_; 
v_toCommandContextInfo_6064_ = lean_ctor_get(v_ctx_6036_, 0);
v_fileMap_6065_ = lean_ctor_get(v_toCommandContextInfo_6064_, 2);
lean_inc_ref_n(v_fileMap_6065_, 2);
v___x_6066_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6065_, v___y_6062_);
lean_dec(v___y_6062_);
v___x_6067_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6065_, v___y_6063_);
lean_dec(v___y_6063_);
if (v_isShared_6055_ == 0)
{
lean_ctor_set(v___x_6054_, 1, v___x_6067_);
lean_ctor_set(v___x_6054_, 0, v___x_6066_);
v_range_6069_ = v___x_6054_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v___x_6066_);
lean_ctor_set(v_reuseFailAlloc_6072_, 1, v___x_6067_);
v_range_6069_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; 
lean_inc_ref(v_range_6069_);
v___x_6070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6060_);
lean_ctor_set(v___x_6070_, 1, v_range_6069_);
lean_ctor_set(v___x_6070_, 2, v_range_6069_);
v___x_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
v___y_6057_ = v___x_6071_;
goto v___jp_6056_;
}
}
v___jp_6073_:
{
uint8_t v___x_6074_; lean_object* v___x_6075_; 
v___x_6074_ = 0;
v___x_6075_ = l_Lean_Syntax_getRange_x3f(v_stx_6035_, v___x_6074_);
if (lean_obj_tag(v___x_6075_) == 1)
{
lean_object* v_val_6076_; 
v_val_6076_ = lean_ctor_get(v___x_6075_, 0);
lean_inc(v_val_6076_);
lean_dec_ref_known(v___x_6075_, 1);
if (v_snd_6037_ == 0)
{
lean_object* v_start_6077_; lean_object* v_stop_6078_; 
v_start_6077_ = lean_ctor_get(v_val_6076_, 0);
lean_inc(v_start_6077_);
v_stop_6078_ = lean_ctor_get(v_val_6076_, 1);
lean_inc(v_stop_6078_);
lean_dec(v_val_6076_);
v___y_6062_ = v_start_6077_;
v___y_6063_ = v_stop_6078_;
goto v___jp_6061_;
}
else
{
lean_object* v_start_6079_; lean_object* v_stop_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
v_start_6079_ = lean_ctor_get(v_val_6076_, 0);
lean_inc(v_start_6079_);
v_stop_6080_ = lean_ctor_get(v_val_6076_, 1);
lean_inc(v_stop_6080_);
lean_dec(v_val_6076_);
v___x_6081_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_6082_ = lean_nat_add(v_stop_6080_, v___x_6081_);
lean_dec(v_stop_6080_);
v___y_6062_ = v_start_6079_;
v___y_6063_ = v___x_6082_;
goto v___jp_6061_;
}
}
else
{
lean_object* v___x_6083_; 
lean_dec(v___x_6075_);
lean_dec_ref(v___x_6060_);
lean_del_object(v___x_6054_);
v___x_6083_ = lean_box(0);
v___y_6057_ = v___x_6083_;
goto v___jp_6056_;
}
}
v___jp_6085_:
{
if (v___x_6084_ == 0)
{
goto v___jp_6073_;
}
else
{
lean_object* v___x_6086_; 
lean_dec_ref(v___x_6060_);
lean_del_object(v___x_6054_);
v___x_6086_ = lean_box(0);
v___y_6057_ = v___x_6086_;
goto v___jp_6056_;
}
}
}
}
v___jp_6044_:
{
size_t v___x_6046_; size_t v___x_6047_; 
v___x_6046_ = ((size_t)1ULL);
v___x_6047_ = lean_usize_add(v_i_6042_, v___x_6046_);
v_i_6042_ = v___x_6047_;
v_b_6043_ = v_a_6045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_6095_, lean_object* v_stx_6096_, lean_object* v_ctx_6097_, lean_object* v_snd_6098_, lean_object* v_fst_6099_, lean_object* v_caps_6100_, lean_object* v_as_6101_, lean_object* v_sz_6102_, lean_object* v_i_6103_, lean_object* v_b_6104_){
_start:
{
uint8_t v_snd_1724__boxed_6105_; size_t v_sz_boxed_6106_; size_t v_i_boxed_6107_; lean_object* v_res_6108_; 
v_snd_1724__boxed_6105_ = lean_unbox(v_snd_6098_);
v_sz_boxed_6106_ = lean_unbox_usize(v_sz_6102_);
lean_dec(v_sz_6102_);
v_i_boxed_6107_ = lean_unbox_usize(v_i_6103_);
lean_dec(v_i_6103_);
v_res_6108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6095_, v_stx_6096_, v_ctx_6097_, v_snd_1724__boxed_6105_, v_fst_6099_, v_caps_6100_, v_as_6101_, v_sz_boxed_6106_, v_i_boxed_6107_, v_b_6104_);
lean_dec_ref(v_as_6101_);
lean_dec_ref(v_caps_6100_);
lean_dec_ref(v_fst_6099_);
lean_dec(v_stx_6096_);
return v_res_6108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_6109_, lean_object* v_stx_6110_, lean_object* v_caps_6111_, lean_object* v_ctx_6112_, lean_object* v_mkItem_6113_){
_start:
{
lean_object* v_fst_6115_; uint8_t v_snd_6116_; uint8_t v___x_6121_; lean_object* v___x_6122_; 
v___x_6121_ = 0;
v___x_6122_ = l_Lean_Syntax_getSubstring_x3f(v_stx_6110_, v___x_6121_, v___x_6121_);
if (lean_obj_tag(v___x_6122_) == 0)
{
lean_object* v___x_6123_; 
v___x_6123_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_6115_ = v___x_6123_;
v_snd_6116_ = v___x_6121_;
goto v___jp_6114_;
}
else
{
lean_object* v_val_6124_; lean_object* v_str_6125_; lean_object* v_startPos_6126_; lean_object* v_stopPos_6127_; uint8_t v___y_6129_; uint8_t v___x_6131_; 
v_val_6124_ = lean_ctor_get(v___x_6122_, 0);
lean_inc(v_val_6124_);
lean_dec_ref_known(v___x_6122_, 1);
v_str_6125_ = lean_ctor_get(v_val_6124_, 0);
lean_inc_ref(v_str_6125_);
v_startPos_6126_ = lean_ctor_get(v_val_6124_, 1);
lean_inc(v_startPos_6126_);
v_stopPos_6127_ = lean_ctor_get(v_val_6124_, 2);
lean_inc(v_stopPos_6127_);
lean_dec(v_val_6124_);
v___x_6131_ = lean_string_utf8_at_end(v_str_6125_, v_stopPos_6127_);
if (v___x_6131_ == 0)
{
uint32_t v___x_6132_; uint32_t v___x_6133_; uint8_t v___x_6134_; 
v___x_6132_ = lean_string_utf8_get(v_str_6125_, v_stopPos_6127_);
v___x_6133_ = 46;
v___x_6134_ = lean_uint32_dec_eq(v___x_6132_, v___x_6133_);
if (v___x_6134_ == 0)
{
v___y_6129_ = v___x_6134_;
goto v___jp_6128_;
}
else
{
lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6135_ = lean_string_utf8_extract(v_str_6125_, v_startPos_6126_, v_stopPos_6127_);
lean_dec(v_stopPos_6127_);
lean_dec(v_startPos_6126_);
lean_dec_ref(v_str_6125_);
v___x_6136_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6137_ = lean_string_append(v___x_6135_, v___x_6136_);
v_fst_6115_ = v___x_6137_;
v_snd_6116_ = v___x_6134_;
goto v___jp_6114_;
}
}
else
{
v___y_6129_ = v___x_6121_;
goto v___jp_6128_;
}
v___jp_6128_:
{
lean_object* v___x_6130_; 
v___x_6130_ = lean_string_utf8_extract(v_str_6125_, v_startPos_6126_, v_stopPos_6127_);
lean_dec(v_stopPos_6127_);
lean_dec(v_startPos_6126_);
lean_dec_ref(v_str_6125_);
v_fst_6115_ = v___x_6130_;
v_snd_6116_ = v___y_6129_;
goto v___jp_6114_;
}
}
v___jp_6114_:
{
lean_object* v_items_6117_; size_t v_sz_6118_; size_t v___x_6119_; lean_object* v___x_6120_; 
v_items_6117_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_6118_ = lean_array_size(v_entries_6109_);
v___x_6119_ = ((size_t)0ULL);
v___x_6120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6113_, v_stx_6110_, v_ctx_6112_, v_snd_6116_, v_fst_6115_, v_caps_6111_, v_entries_6109_, v_sz_6118_, v___x_6119_, v_items_6117_);
lean_dec_ref(v_fst_6115_);
return v___x_6120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_6138_, lean_object* v_stx_6139_, lean_object* v_caps_6140_, lean_object* v_ctx_6141_, lean_object* v_mkItem_6142_){
_start:
{
lean_object* v_res_6143_; 
v_res_6143_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_6138_, v_stx_6139_, v_caps_6140_, v_ctx_6141_, v_mkItem_6142_);
lean_dec_ref(v_caps_6140_);
lean_dec(v_stx_6139_);
lean_dec_ref(v_entries_6138_);
return v_res_6143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_6144_, lean_object* v_caps_6145_, lean_object* v_ctx_6146_, lean_object* v___f_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_){
_start:
{
lean_object* v___x_6153_; lean_object* v_a_6154_; lean_object* v___x_6156_; uint8_t v_isShared_6157_; uint8_t v_isSharedCheck_6162_; 
v___x_6153_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6151_);
v_a_6154_ = lean_ctor_get(v___x_6153_, 0);
v_isSharedCheck_6162_ = !lean_is_exclusive(v___x_6153_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6156_ = v___x_6153_;
v_isShared_6157_ = v_isSharedCheck_6162_;
goto v_resetjp_6155_;
}
else
{
lean_inc(v_a_6154_);
lean_dec(v___x_6153_);
v___x_6156_ = lean_box(0);
v_isShared_6157_ = v_isSharedCheck_6162_;
goto v_resetjp_6155_;
}
v_resetjp_6155_:
{
lean_object* v___x_6158_; lean_object* v___x_6160_; 
v___x_6158_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_6154_, v_partialId_6144_, v_caps_6145_, v_ctx_6146_, v___f_6147_);
lean_dec(v_a_6154_);
if (v_isShared_6157_ == 0)
{
lean_ctor_set(v___x_6156_, 0, v___x_6158_);
v___x_6160_ = v___x_6156_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6161_; 
v_reuseFailAlloc_6161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6161_, 0, v___x_6158_);
v___x_6160_ = v_reuseFailAlloc_6161_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
return v___x_6160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_6163_, lean_object* v_caps_6164_, lean_object* v_ctx_6165_, lean_object* v___f_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_){
_start:
{
lean_object* v_res_6172_; 
v_res_6172_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6163_, v_caps_6164_, v_ctx_6165_, v___f_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_);
lean_dec(v___y_6170_);
lean_dec_ref(v___y_6169_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec_ref(v_caps_6164_);
lean_dec(v_partialId_6163_);
return v_res_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_6173_, lean_object* v_pos_6174_, lean_object* v_completionInfoPos_6175_, lean_object* v_ctx_6176_, lean_object* v_partialId_6177_, lean_object* v_caps_6178_){
_start:
{
lean_object* v___f_6180_; lean_object* v___f_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; 
v___f_6180_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6180_, 0, v_completionInfoPos_6175_);
lean_closure_set(v___f_6180_, 1, v_uri_6173_);
lean_closure_set(v___f_6180_, 2, v_pos_6174_);
lean_inc_ref(v_ctx_6176_);
v___f_6181_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_6181_, 0, v_partialId_6177_);
lean_closure_set(v___f_6181_, 1, v_caps_6178_);
lean_closure_set(v___f_6181_, 2, v_ctx_6176_);
lean_closure_set(v___f_6181_, 3, v___f_6180_);
v___x_6182_ = lean_unsigned_to_nat(32u);
v___x_6183_ = lean_mk_empty_array_with_capacity(v___x_6182_);
lean_dec_ref(v___x_6183_);
v___x_6184_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_6185_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6176_, v___x_6184_, v___f_6181_);
return v___x_6185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_6186_, lean_object* v_pos_6187_, lean_object* v_completionInfoPos_6188_, lean_object* v_ctx_6189_, lean_object* v_partialId_6190_, lean_object* v_caps_6191_, lean_object* v_a_6192_){
_start:
{
lean_object* v_res_6193_; 
v_res_6193_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6186_, v_pos_6187_, v_completionInfoPos_6188_, v_ctx_6189_, v_partialId_6190_, v_caps_6191_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_){
_start:
{
lean_object* v___x_6199_; 
v___x_6199_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6197_);
return v___x_6199_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_){
_start:
{
lean_object* v_res_6205_; 
v_res_6205_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6202_);
lean_dec(v___y_6201_);
lean_dec_ref(v___y_6200_);
return v_res_6205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6206_, lean_object* v_t_6207_){
_start:
{
lean_object* v___x_6208_; 
v___x_6208_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6206_, v_t_6207_);
return v___x_6208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6209_, lean_object* v_t_6210_){
_start:
{
lean_object* v_res_6211_; 
v_res_6211_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6209_, v_t_6210_);
lean_dec(v_t_6210_);
return v_res_6211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6212_, lean_object* v_as_6213_, lean_object* v_lo_6214_, lean_object* v_hi_6215_, lean_object* v_w_6216_, lean_object* v_hlo_6217_, lean_object* v_hhi_6218_){
_start:
{
lean_object* v___x_6219_; 
v___x_6219_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6212_, v_as_6213_, v_lo_6214_, v_hi_6215_);
return v___x_6219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6220_, lean_object* v_as_6221_, lean_object* v_lo_6222_, lean_object* v_hi_6223_, lean_object* v_w_6224_, lean_object* v_hlo_6225_, lean_object* v_hhi_6226_){
_start:
{
lean_object* v_res_6227_; 
v_res_6227_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6220_, v_as_6221_, v_lo_6222_, v_hi_6223_, v_w_6224_, v_hlo_6225_, v_hhi_6226_);
lean_dec(v_hi_6223_);
lean_dec(v_n_6220_);
return v_res_6227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(lean_object* v_n_6228_, lean_object* v_lo_6229_, lean_object* v_hi_6230_, lean_object* v_hhi_6231_, lean_object* v_pivot_6232_, lean_object* v_as_6233_, lean_object* v_i_6234_, lean_object* v_k_6235_, lean_object* v_ilo_6236_, lean_object* v_ik_6237_, lean_object* v_w_6238_){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6230_, v_pivot_6232_, v_as_6233_, v_i_6234_, v_k_6235_);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___boxed(lean_object* v_n_6240_, lean_object* v_lo_6241_, lean_object* v_hi_6242_, lean_object* v_hhi_6243_, lean_object* v_pivot_6244_, lean_object* v_as_6245_, lean_object* v_i_6246_, lean_object* v_k_6247_, lean_object* v_ilo_6248_, lean_object* v_ik_6249_, lean_object* v_w_6250_){
_start:
{
lean_object* v_res_6251_; 
v_res_6251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(v_n_6240_, v_lo_6241_, v_hi_6242_, v_hhi_6243_, v_pivot_6244_, v_as_6245_, v_i_6246_, v_k_6247_, v_ilo_6248_, v_ik_6249_, v_w_6250_);
lean_dec(v_hi_6242_);
lean_dec(v_lo_6241_);
lean_dec(v_n_6240_);
return v_res_6251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6252_, lean_object* v_uri_6253_, lean_object* v_pos_6254_, size_t v_sz_6255_, size_t v_i_6256_, lean_object* v_bs_6257_){
_start:
{
uint8_t v___x_6258_; 
v___x_6258_ = lean_usize_dec_lt(v_i_6256_, v_sz_6255_);
if (v___x_6258_ == 0)
{
lean_dec_ref(v_pos_6254_);
lean_dec_ref(v_uri_6253_);
lean_dec(v_completionInfoPos_6252_);
return v_bs_6257_;
}
else
{
lean_object* v_v_6259_; lean_object* v_userName_6260_; lean_object* v_docString_6261_; lean_object* v___x_6262_; lean_object* v_bs_x27_6263_; lean_object* v___x_6264_; lean_object* v___y_6266_; 
v_v_6259_ = lean_array_uget_borrowed(v_bs_6257_, v_i_6256_);
v_userName_6260_ = lean_ctor_get(v_v_6259_, 1);
lean_inc_ref(v_userName_6260_);
v_docString_6261_ = lean_ctor_get(v_v_6259_, 3);
lean_inc(v_docString_6261_);
v___x_6262_ = lean_unsigned_to_nat(0u);
v_bs_x27_6263_ = lean_array_uset(v_bs_6257_, v_i_6256_, v___x_6262_);
v___x_6264_ = lean_box(0);
if (lean_obj_tag(v_docString_6261_) == 0)
{
v___y_6266_ = v___x_6264_;
goto v___jp_6265_;
}
else
{
lean_object* v_val_6276_; lean_object* v___x_6278_; uint8_t v_isShared_6279_; uint8_t v_isSharedCheck_6285_; 
v_val_6276_ = lean_ctor_get(v_docString_6261_, 0);
v_isSharedCheck_6285_ = !lean_is_exclusive(v_docString_6261_);
if (v_isSharedCheck_6285_ == 0)
{
v___x_6278_ = v_docString_6261_;
v_isShared_6279_ = v_isSharedCheck_6285_;
goto v_resetjp_6277_;
}
else
{
lean_inc(v_val_6276_);
lean_dec(v_docString_6261_);
v___x_6278_ = lean_box(0);
v_isShared_6279_ = v_isSharedCheck_6285_;
goto v_resetjp_6277_;
}
v_resetjp_6277_:
{
uint8_t v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6283_; 
v___x_6280_ = 1;
v___x_6281_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6281_, 0, v_val_6276_);
lean_ctor_set_uint8(v___x_6281_, sizeof(void*)*1, v___x_6280_);
if (v_isShared_6279_ == 0)
{
lean_ctor_set(v___x_6278_, 0, v___x_6281_);
v___x_6283_ = v___x_6278_;
goto v_reusejp_6282_;
}
else
{
lean_object* v_reuseFailAlloc_6284_; 
v_reuseFailAlloc_6284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6284_, 0, v___x_6281_);
v___x_6283_ = v_reuseFailAlloc_6284_;
goto v_reusejp_6282_;
}
v_reusejp_6282_:
{
v___y_6266_ = v___x_6283_;
goto v___jp_6265_;
}
}
}
v___jp_6265_:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; size_t v___x_6272_; size_t v___x_6273_; lean_object* v___x_6274_; 
v___x_6267_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6252_);
v___x_6268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6268_, 0, v_completionInfoPos_6252_);
lean_inc_ref(v_pos_6254_);
lean_inc_ref(v_uri_6253_);
v___x_6269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6269_, 0, v_uri_6253_);
lean_ctor_set(v___x_6269_, 1, v_pos_6254_);
lean_ctor_set(v___x_6269_, 2, v___x_6268_);
lean_ctor_set(v___x_6269_, 3, v___x_6264_);
v___x_6270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6270_, 0, v___x_6269_);
v___x_6271_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6271_, 0, v_userName_6260_);
lean_ctor_set(v___x_6271_, 1, v___x_6264_);
lean_ctor_set(v___x_6271_, 2, v___y_6266_);
lean_ctor_set(v___x_6271_, 3, v___x_6267_);
lean_ctor_set(v___x_6271_, 4, v___x_6264_);
lean_ctor_set(v___x_6271_, 5, v___x_6264_);
lean_ctor_set(v___x_6271_, 6, v___x_6270_);
lean_ctor_set(v___x_6271_, 7, v___x_6264_);
v___x_6272_ = ((size_t)1ULL);
v___x_6273_ = lean_usize_add(v_i_6256_, v___x_6272_);
v___x_6274_ = lean_array_uset(v_bs_x27_6263_, v_i_6256_, v___x_6271_);
v_i_6256_ = v___x_6273_;
v_bs_6257_ = v___x_6274_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6286_, lean_object* v_uri_6287_, lean_object* v_pos_6288_, lean_object* v_sz_6289_, lean_object* v_i_6290_, lean_object* v_bs_6291_){
_start:
{
size_t v_sz_boxed_6292_; size_t v_i_boxed_6293_; lean_object* v_res_6294_; 
v_sz_boxed_6292_ = lean_unbox_usize(v_sz_6289_);
lean_dec(v_sz_6289_);
v_i_boxed_6293_ = lean_unbox_usize(v_i_6290_);
lean_dec(v_i_6290_);
v_res_6294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6286_, v_uri_6287_, v_pos_6288_, v_sz_boxed_6292_, v_i_boxed_6293_, v_bs_6291_);
return v_res_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6295_, lean_object* v_completionInfoPos_6296_, lean_object* v_uri_6297_, lean_object* v_pos_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_){
_start:
{
lean_object* v___x_6304_; 
v___x_6304_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6295_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_);
if (lean_obj_tag(v___x_6304_) == 0)
{
lean_object* v_a_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6315_; 
v_a_6305_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6315_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6315_ == 0)
{
v___x_6307_ = v___x_6304_;
v_isShared_6308_ = v_isSharedCheck_6315_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_a_6305_);
lean_dec(v___x_6304_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6315_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
size_t v_sz_6309_; size_t v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6313_; 
v_sz_6309_ = lean_array_size(v_a_6305_);
v___x_6310_ = ((size_t)0ULL);
v___x_6311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6296_, v_uri_6297_, v_pos_6298_, v_sz_6309_, v___x_6310_, v_a_6305_);
if (v_isShared_6308_ == 0)
{
lean_ctor_set(v___x_6307_, 0, v___x_6311_);
v___x_6313_ = v___x_6307_;
goto v_reusejp_6312_;
}
else
{
lean_object* v_reuseFailAlloc_6314_; 
v_reuseFailAlloc_6314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6314_, 0, v___x_6311_);
v___x_6313_ = v_reuseFailAlloc_6314_;
goto v_reusejp_6312_;
}
v_reusejp_6312_:
{
return v___x_6313_;
}
}
}
else
{
lean_object* v_a_6316_; lean_object* v___x_6318_; uint8_t v_isShared_6319_; uint8_t v_isSharedCheck_6323_; 
lean_dec_ref(v_pos_6298_);
lean_dec_ref(v_uri_6297_);
lean_dec(v_completionInfoPos_6296_);
v_a_6316_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6323_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6323_ == 0)
{
v___x_6318_ = v___x_6304_;
v_isShared_6319_ = v_isSharedCheck_6323_;
goto v_resetjp_6317_;
}
else
{
lean_inc(v_a_6316_);
lean_dec(v___x_6304_);
v___x_6318_ = lean_box(0);
v_isShared_6319_ = v_isSharedCheck_6323_;
goto v_resetjp_6317_;
}
v_resetjp_6317_:
{
lean_object* v___x_6321_; 
if (v_isShared_6319_ == 0)
{
v___x_6321_ = v___x_6318_;
goto v_reusejp_6320_;
}
else
{
lean_object* v_reuseFailAlloc_6322_; 
v_reuseFailAlloc_6322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6322_, 0, v_a_6316_);
v___x_6321_ = v_reuseFailAlloc_6322_;
goto v_reusejp_6320_;
}
v_reusejp_6320_:
{
return v___x_6321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6324_, lean_object* v_completionInfoPos_6325_, lean_object* v_uri_6326_, lean_object* v_pos_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_){
_start:
{
uint8_t v___x_495__boxed_6333_; lean_object* v_res_6334_; 
v___x_495__boxed_6333_ = lean_unbox(v___x_6324_);
v_res_6334_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_495__boxed_6333_, v_completionInfoPos_6325_, v_uri_6326_, v_pos_6327_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_);
lean_dec(v___y_6331_);
lean_dec_ref(v___y_6330_);
lean_dec(v___y_6329_);
lean_dec_ref(v___y_6328_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6335_, lean_object* v_pos_6336_, lean_object* v_completionInfoPos_6337_, lean_object* v_ctx_6338_){
_start:
{
lean_object* v___x_6340_; uint8_t v___x_6341_; lean_object* v___x_6342_; lean_object* v___f_6343_; lean_object* v___x_6344_; 
v___x_6340_ = l_Lean_LocalContext_empty;
v___x_6341_ = 0;
v___x_6342_ = lean_box(v___x_6341_);
v___f_6343_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6343_, 0, v___x_6342_);
lean_closure_set(v___f_6343_, 1, v_completionInfoPos_6337_);
lean_closure_set(v___f_6343_, 2, v_uri_6335_);
lean_closure_set(v___f_6343_, 3, v_pos_6336_);
v___x_6344_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6338_, v___x_6340_, v___f_6343_);
return v___x_6344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6345_, lean_object* v_pos_6346_, lean_object* v_completionInfoPos_6347_, lean_object* v_ctx_6348_, lean_object* v_a_6349_){
_start:
{
lean_object* v_res_6350_; 
v_res_6350_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6345_, v_pos_6346_, v_completionInfoPos_6347_, v_ctx_6348_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6351_, lean_object* v_b_6352_){
_start:
{
lean_object* v_array_6353_; lean_object* v_start_6354_; lean_object* v_stop_6355_; lean_object* v___x_6357_; uint8_t v_isShared_6358_; uint8_t v_isSharedCheck_6368_; 
v_array_6353_ = lean_ctor_get(v_a_6351_, 0);
v_start_6354_ = lean_ctor_get(v_a_6351_, 1);
v_stop_6355_ = lean_ctor_get(v_a_6351_, 2);
v_isSharedCheck_6368_ = !lean_is_exclusive(v_a_6351_);
if (v_isSharedCheck_6368_ == 0)
{
v___x_6357_ = v_a_6351_;
v_isShared_6358_ = v_isSharedCheck_6368_;
goto v_resetjp_6356_;
}
else
{
lean_inc(v_stop_6355_);
lean_inc(v_start_6354_);
lean_inc(v_array_6353_);
lean_dec(v_a_6351_);
v___x_6357_ = lean_box(0);
v_isShared_6358_ = v_isSharedCheck_6368_;
goto v_resetjp_6356_;
}
v_resetjp_6356_:
{
uint8_t v___x_6359_; 
v___x_6359_ = lean_nat_dec_lt(v_start_6354_, v_stop_6355_);
if (v___x_6359_ == 0)
{
lean_del_object(v___x_6357_);
lean_dec(v_stop_6355_);
lean_dec(v_start_6354_);
lean_dec_ref(v_array_6353_);
return v_b_6352_;
}
else
{
lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6363_; 
v___x_6360_ = lean_unsigned_to_nat(1u);
v___x_6361_ = lean_nat_add(v_start_6354_, v___x_6360_);
lean_inc_ref(v_array_6353_);
if (v_isShared_6358_ == 0)
{
lean_ctor_set(v___x_6357_, 1, v___x_6361_);
v___x_6363_ = v___x_6357_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6367_; 
v_reuseFailAlloc_6367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6367_, 0, v_array_6353_);
lean_ctor_set(v_reuseFailAlloc_6367_, 1, v___x_6361_);
lean_ctor_set(v_reuseFailAlloc_6367_, 2, v_stop_6355_);
v___x_6363_ = v_reuseFailAlloc_6367_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; 
v___x_6364_ = lean_array_fget(v_array_6353_, v_start_6354_);
lean_dec(v_start_6354_);
lean_dec_ref(v_array_6353_);
v___x_6365_ = lean_array_push(v_b_6352_, v___x_6364_);
v_a_6351_ = v___x_6363_;
v_b_6352_ = v___x_6365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6371_, lean_object* v_idx_6372_){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; 
v___x_6373_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6374_ = lean_array_get_size(v_scopeNames_6371_);
v___x_6375_ = l_Array_toSubarray___redArg(v_scopeNames_6371_, v_idx_6372_, v___x_6374_);
v___x_6376_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6377_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6375_, v___x_6376_);
v___x_6378_ = lean_array_to_list(v___x_6377_);
v___x_6379_ = l_String_intercalate(v___x_6373_, v___x_6378_);
return v___x_6379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6380_, lean_object* v_R_6381_, lean_object* v_a_6382_, lean_object* v_b_6383_){
_start:
{
lean_object* v___x_6384_; 
v___x_6384_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6382_, v_b_6383_);
return v___x_6384_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6385_, lean_object* v_next_6386_, lean_object* v_scopeNames_6387_, lean_object* v_idComponents_6388_, lean_object* v_a_6389_, uint8_t v_b_6390_){
_start:
{
uint8_t v___x_6391_; 
v___x_6391_ = lean_nat_dec_lt(v_a_6389_, v_upperBound_6385_);
if (v___x_6391_ == 0)
{
lean_dec(v_a_6389_);
return v_b_6390_;
}
else
{
uint8_t v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; uint8_t v___x_6395_; 
v___x_6392_ = 0;
v___x_6393_ = lean_nat_add(v_next_6386_, v_a_6389_);
v___x_6394_ = lean_array_get_size(v_scopeNames_6387_);
v___x_6395_ = lean_nat_dec_lt(v___x_6393_, v___x_6394_);
if (v___x_6395_ == 0)
{
lean_dec(v___x_6393_);
lean_dec(v_a_6389_);
return v___x_6392_;
}
else
{
lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; uint8_t v___x_6399_; 
v___x_6396_ = lean_array_fget_borrowed(v_scopeNames_6387_, v___x_6393_);
lean_dec(v___x_6393_);
v___x_6397_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6398_ = lean_array_get_borrowed(v___x_6397_, v_idComponents_6388_, v_a_6389_);
v___x_6399_ = lean_string_dec_eq(v___x_6398_, v___x_6396_);
if (v___x_6399_ == 0)
{
lean_dec(v_a_6389_);
return v___x_6392_;
}
else
{
lean_object* v___x_6400_; lean_object* v___x_6401_; 
v___x_6400_ = lean_unsigned_to_nat(1u);
v___x_6401_ = lean_nat_add(v_a_6389_, v___x_6400_);
lean_dec(v_a_6389_);
v_a_6389_ = v___x_6401_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6403_, lean_object* v_next_6404_, lean_object* v_scopeNames_6405_, lean_object* v_idComponents_6406_, lean_object* v_a_6407_, lean_object* v_b_6408_){
_start:
{
uint8_t v_b_boxed_6409_; uint8_t v_res_6410_; lean_object* v_r_6411_; 
v_b_boxed_6409_ = lean_unbox(v_b_6408_);
v_res_6410_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6403_, v_next_6404_, v_scopeNames_6405_, v_idComponents_6406_, v_a_6407_, v_b_boxed_6409_);
lean_dec_ref(v_idComponents_6406_);
lean_dec_ref(v_scopeNames_6405_);
lean_dec(v_next_6404_);
lean_dec(v_upperBound_6403_);
v_r_6411_ = lean_box(v_res_6410_);
return v_r_6411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6412_, lean_object* v_idComponents_6413_, lean_object* v_scopeNames_6414_, lean_object* v_a_6415_, lean_object* v_b_6416_){
_start:
{
lean_object* v_a_6418_; uint8_t v___x_6422_; 
v___x_6422_ = lean_nat_dec_lt(v_a_6415_, v_upperBound_6412_);
if (v___x_6422_ == 0)
{
lean_dec(v_a_6415_);
lean_dec_ref(v_scopeNames_6414_);
return v_b_6416_;
}
else
{
lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; uint8_t v___x_6426_; 
v___x_6423_ = lean_array_get_size(v_idComponents_6413_);
v___x_6424_ = lean_unsigned_to_nat(1u);
v___x_6425_ = lean_nat_sub(v___x_6423_, v___x_6424_);
v___x_6426_ = lean_nat_dec_lt(v___x_6425_, v___x_6423_);
if (v___x_6426_ == 0)
{
lean_object* v___x_6427_; lean_object* v___x_6428_; 
lean_dec(v___x_6425_);
lean_inc(v_a_6415_);
lean_inc_ref(v_scopeNames_6414_);
v___x_6427_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6414_, v_a_6415_);
v___x_6428_ = lean_array_push(v_b_6416_, v___x_6427_);
v_a_6418_ = v___x_6428_;
goto v___jp_6417_;
}
else
{
lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; uint8_t v___x_6432_; 
v___x_6429_ = lean_nat_add(v_a_6415_, v___x_6423_);
v___x_6430_ = lean_nat_sub(v___x_6429_, v___x_6424_);
lean_dec(v___x_6429_);
v___x_6431_ = lean_array_get_size(v_scopeNames_6414_);
v___x_6432_ = lean_nat_dec_lt(v___x_6430_, v___x_6431_);
if (v___x_6432_ == 0)
{
lean_dec(v___x_6430_);
lean_dec(v___x_6425_);
v_a_6418_ = v_b_6416_;
goto v___jp_6417_;
}
else
{
lean_object* v___x_6433_; lean_object* v___x_6434_; uint8_t v___x_6435_; 
v___x_6433_ = lean_array_fget_borrowed(v_idComponents_6413_, v___x_6425_);
v___x_6434_ = lean_array_fget_borrowed(v_scopeNames_6414_, v___x_6430_);
v___x_6435_ = l_String_charactersIn(v___x_6433_, v___x_6434_);
if (v___x_6435_ == 0)
{
lean_dec(v___x_6430_);
lean_dec(v___x_6425_);
v_a_6418_ = v_b_6416_;
goto v___jp_6417_;
}
else
{
lean_object* v___x_6436_; uint8_t v___x_6437_; 
v___x_6436_ = lean_unsigned_to_nat(0u);
v___x_6437_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6425_, v_a_6415_, v_scopeNames_6414_, v_idComponents_6413_, v___x_6436_, v___x_6435_);
lean_dec(v___x_6425_);
if (v___x_6437_ == 0)
{
lean_dec(v___x_6430_);
v_a_6418_ = v_b_6416_;
goto v___jp_6417_;
}
else
{
lean_object* v___x_6438_; lean_object* v___x_6439_; 
lean_inc_ref(v_scopeNames_6414_);
v___x_6438_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6414_, v___x_6430_);
v___x_6439_ = lean_array_push(v_b_6416_, v___x_6438_);
v_a_6418_ = v___x_6439_;
goto v___jp_6417_;
}
}
}
}
}
v___jp_6417_:
{
lean_object* v___x_6419_; lean_object* v___x_6420_; 
v___x_6419_ = lean_unsigned_to_nat(1u);
v___x_6420_ = lean_nat_add(v_a_6415_, v___x_6419_);
lean_dec(v_a_6415_);
v_a_6415_ = v___x_6420_;
v_b_6416_ = v_a_6418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6440_, lean_object* v_idComponents_6441_, lean_object* v_scopeNames_6442_, lean_object* v_a_6443_, lean_object* v_b_6444_){
_start:
{
lean_object* v_res_6445_; 
v_res_6445_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6440_, v_idComponents_6441_, v_scopeNames_6442_, v_a_6443_, v_b_6444_);
lean_dec_ref(v_idComponents_6441_);
lean_dec(v_upperBound_6440_);
return v_res_6445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6446_, lean_object* v_scopeNames_6447_){
_start:
{
lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v_r_6450_; lean_object* v___x_6451_; 
v___x_6448_ = lean_unsigned_to_nat(0u);
v___x_6449_ = lean_array_get_size(v_scopeNames_6447_);
v_r_6450_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6451_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6449_, v_idComponents_6446_, v_scopeNames_6447_, v___x_6448_, v_r_6450_);
return v___x_6451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6452_, lean_object* v_scopeNames_6453_){
_start:
{
lean_object* v_res_6454_; 
v_res_6454_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6452_, v_scopeNames_6453_);
lean_dec_ref(v_idComponents_6452_);
return v_res_6454_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6455_, lean_object* v_next_6456_, lean_object* v_scopeNames_6457_, lean_object* v_idComponents_6458_, lean_object* v_inst_6459_, lean_object* v_R_6460_, lean_object* v_a_6461_, uint8_t v_b_6462_, lean_object* v_c_6463_){
_start:
{
uint8_t v___x_6464_; 
v___x_6464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6455_, v_next_6456_, v_scopeNames_6457_, v_idComponents_6458_, v_a_6461_, v_b_6462_);
return v___x_6464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6465_, lean_object* v_next_6466_, lean_object* v_scopeNames_6467_, lean_object* v_idComponents_6468_, lean_object* v_inst_6469_, lean_object* v_R_6470_, lean_object* v_a_6471_, lean_object* v_b_6472_, lean_object* v_c_6473_){
_start:
{
uint8_t v_b_boxed_6474_; uint8_t v_res_6475_; lean_object* v_r_6476_; 
v_b_boxed_6474_ = lean_unbox(v_b_6472_);
v_res_6475_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6465_, v_next_6466_, v_scopeNames_6467_, v_idComponents_6468_, v_inst_6469_, v_R_6470_, v_a_6471_, v_b_boxed_6474_, v_c_6473_);
lean_dec_ref(v_idComponents_6468_);
lean_dec_ref(v_scopeNames_6467_);
lean_dec(v_next_6466_);
lean_dec(v_upperBound_6465_);
v_r_6476_ = lean_box(v_res_6475_);
return v_r_6476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6477_, lean_object* v_idComponents_6478_, lean_object* v_scopeNames_6479_, lean_object* v_inst_6480_, lean_object* v_R_6481_, lean_object* v_a_6482_, lean_object* v_b_6483_, lean_object* v_c_6484_){
_start:
{
lean_object* v___x_6485_; 
v___x_6485_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6477_, v_idComponents_6478_, v_scopeNames_6479_, v_a_6482_, v_b_6483_);
return v___x_6485_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6486_, lean_object* v_idComponents_6487_, lean_object* v_scopeNames_6488_, lean_object* v_inst_6489_, lean_object* v_R_6490_, lean_object* v_a_6491_, lean_object* v_b_6492_, lean_object* v_c_6493_){
_start:
{
lean_object* v_res_6494_; 
v_res_6494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6486_, v_idComponents_6487_, v_scopeNames_6488_, v_inst_6489_, v_R_6490_, v_a_6491_, v_b_6492_, v_c_6493_);
lean_dec_ref(v_idComponents_6487_);
lean_dec(v_upperBound_6486_);
return v_res_6494_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6495_){
_start:
{
lean_object* v___x_6496_; lean_object* v___x_6497_; uint8_t v___x_6498_; 
v___x_6496_ = lean_string_utf8_byte_size(v_x_6495_);
v___x_6497_ = lean_unsigned_to_nat(0u);
v___x_6498_ = lean_nat_dec_eq(v___x_6496_, v___x_6497_);
if (v___x_6498_ == 0)
{
uint8_t v___x_6499_; 
v___x_6499_ = 1;
return v___x_6499_;
}
else
{
uint8_t v___x_6500_; 
v___x_6500_ = 0;
return v___x_6500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6501_){
_start:
{
uint8_t v_res_6502_; lean_object* v_r_6503_; 
v_res_6502_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6501_);
lean_dec_ref(v_x_6501_);
v_r_6503_ = lean_box(v_res_6502_);
return v_r_6503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6504_, size_t v_i_6505_, lean_object* v_bs_6506_){
_start:
{
uint8_t v___x_6507_; 
v___x_6507_ = lean_usize_dec_lt(v_i_6505_, v_sz_6504_);
if (v___x_6507_ == 0)
{
return v_bs_6506_;
}
else
{
lean_object* v_v_6508_; lean_object* v___x_6509_; lean_object* v_bs_x27_6510_; lean_object* v___x_6511_; size_t v___x_6512_; size_t v___x_6513_; lean_object* v___x_6514_; 
v_v_6508_ = lean_array_uget(v_bs_6506_, v_i_6505_);
v___x_6509_ = lean_unsigned_to_nat(0u);
v_bs_x27_6510_ = lean_array_uset(v_bs_6506_, v_i_6505_, v___x_6509_);
v___x_6511_ = l_Lean_Name_toString(v_v_6508_, v___x_6507_);
v___x_6512_ = ((size_t)1ULL);
v___x_6513_ = lean_usize_add(v_i_6505_, v___x_6512_);
v___x_6514_ = lean_array_uset(v_bs_x27_6510_, v_i_6505_, v___x_6511_);
v_i_6505_ = v___x_6513_;
v_bs_6506_ = v___x_6514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6516_, lean_object* v_i_6517_, lean_object* v_bs_6518_){
_start:
{
size_t v_sz_boxed_6519_; size_t v_i_boxed_6520_; lean_object* v_res_6521_; 
v_sz_boxed_6519_ = lean_unbox_usize(v_sz_6516_);
lean_dec(v_sz_6516_);
v_i_boxed_6520_ = lean_unbox_usize(v_i_6517_);
lean_dec(v_i_6517_);
v_res_6521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6519_, v_i_boxed_6520_, v_bs_6518_);
return v_res_6521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6522_, lean_object* v_uri_6523_, lean_object* v_pos_6524_, size_t v_sz_6525_, size_t v_i_6526_, lean_object* v_bs_6527_){
_start:
{
uint8_t v___x_6528_; 
v___x_6528_ = lean_usize_dec_lt(v_i_6526_, v_sz_6525_);
if (v___x_6528_ == 0)
{
lean_dec_ref(v_pos_6524_);
lean_dec_ref(v_uri_6523_);
lean_dec(v_completionInfoPos_6522_);
return v_bs_6527_;
}
else
{
lean_object* v_v_6529_; lean_object* v___x_6530_; lean_object* v_bs_x27_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; size_t v___x_6538_; size_t v___x_6539_; lean_object* v___x_6540_; 
v_v_6529_ = lean_array_uget(v_bs_6527_, v_i_6526_);
v___x_6530_ = lean_unsigned_to_nat(0u);
v_bs_x27_6531_ = lean_array_uset(v_bs_6527_, v_i_6526_, v___x_6530_);
v___x_6532_ = lean_box(0);
v___x_6533_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6522_);
v___x_6534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6534_, 0, v_completionInfoPos_6522_);
lean_inc_ref(v_pos_6524_);
lean_inc_ref(v_uri_6523_);
v___x_6535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6535_, 0, v_uri_6523_);
lean_ctor_set(v___x_6535_, 1, v_pos_6524_);
lean_ctor_set(v___x_6535_, 2, v___x_6534_);
lean_ctor_set(v___x_6535_, 3, v___x_6532_);
v___x_6536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6536_, 0, v___x_6535_);
v___x_6537_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6537_, 0, v_v_6529_);
lean_ctor_set(v___x_6537_, 1, v___x_6532_);
lean_ctor_set(v___x_6537_, 2, v___x_6532_);
lean_ctor_set(v___x_6537_, 3, v___x_6533_);
lean_ctor_set(v___x_6537_, 4, v___x_6532_);
lean_ctor_set(v___x_6537_, 5, v___x_6532_);
lean_ctor_set(v___x_6537_, 6, v___x_6536_);
lean_ctor_set(v___x_6537_, 7, v___x_6532_);
v___x_6538_ = ((size_t)1ULL);
v___x_6539_ = lean_usize_add(v_i_6526_, v___x_6538_);
v___x_6540_ = lean_array_uset(v_bs_x27_6531_, v_i_6526_, v___x_6537_);
v_i_6526_ = v___x_6539_;
v_bs_6527_ = v___x_6540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6542_, lean_object* v_uri_6543_, lean_object* v_pos_6544_, lean_object* v_sz_6545_, lean_object* v_i_6546_, lean_object* v_bs_6547_){
_start:
{
size_t v_sz_boxed_6548_; size_t v_i_boxed_6549_; lean_object* v_res_6550_; 
v_sz_boxed_6548_ = lean_unbox_usize(v_sz_6545_);
lean_dec(v_sz_6545_);
v_i_boxed_6549_ = lean_unbox_usize(v_i_6546_);
lean_dec(v_i_6546_);
v_res_6550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6542_, v_uri_6543_, v_pos_6544_, v_sz_boxed_6548_, v_i_boxed_6549_, v_bs_6547_);
return v_res_6550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6552_, lean_object* v_pos_6553_, lean_object* v_completionInfoPos_6554_, lean_object* v_id_x3f_6555_, uint8_t v_danglingDot_6556_, lean_object* v_scopeNames_6557_){
_start:
{
lean_object* v___f_6559_; lean_object* v_idComponents_6561_; lean_object* v___y_6572_; 
v___f_6559_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6555_) == 0)
{
lean_object* v___x_6575_; 
v___x_6575_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6572_ = v___x_6575_;
goto v___jp_6571_;
}
else
{
lean_object* v_val_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; size_t v_sz_6579_; size_t v___x_6580_; lean_object* v___x_6581_; 
v_val_6576_ = lean_ctor_get(v_id_x3f_6555_, 0);
lean_inc(v_val_6576_);
lean_dec_ref_known(v_id_x3f_6555_, 1);
v___x_6577_ = l_Lean_Name_components(v_val_6576_);
v___x_6578_ = lean_array_mk(v___x_6577_);
v_sz_6579_ = lean_array_size(v___x_6578_);
v___x_6580_ = ((size_t)0ULL);
v___x_6581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6579_, v___x_6580_, v___x_6578_);
v___y_6572_ = v___x_6581_;
goto v___jp_6571_;
}
v___jp_6560_:
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v_scopeNames_6565_; lean_object* v_candidates_6566_; size_t v_sz_6567_; size_t v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; 
v___x_6562_ = lean_array_mk(v_scopeNames_6557_);
v___x_6563_ = lean_array_pop(v___x_6562_);
v___x_6564_ = l_Array_takeWhile___redArg(v___f_6559_, v___x_6563_);
lean_dec_ref(v___x_6563_);
v_scopeNames_6565_ = l_Array_reverse___redArg(v___x_6564_);
v_candidates_6566_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6561_, v_scopeNames_6565_);
lean_dec_ref(v_idComponents_6561_);
v_sz_6567_ = lean_array_size(v_candidates_6566_);
v___x_6568_ = ((size_t)0ULL);
v___x_6569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6554_, v_uri_6552_, v_pos_6553_, v_sz_6567_, v___x_6568_, v_candidates_6566_);
v___x_6570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6570_, 0, v___x_6569_);
return v___x_6570_;
}
v___jp_6571_:
{
if (v_danglingDot_6556_ == 0)
{
v_idComponents_6561_ = v___y_6572_;
goto v___jp_6560_;
}
else
{
lean_object* v___x_6573_; lean_object* v_idComponents_6574_; 
v___x_6573_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6574_ = lean_array_push(v___y_6572_, v___x_6573_);
v_idComponents_6561_ = v_idComponents_6574_;
goto v___jp_6560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6582_, lean_object* v_pos_6583_, lean_object* v_completionInfoPos_6584_, lean_object* v_id_x3f_6585_, lean_object* v_danglingDot_6586_, lean_object* v_scopeNames_6587_, lean_object* v_a_6588_){
_start:
{
uint8_t v_danglingDot_boxed_6589_; lean_object* v_res_6590_; 
v_danglingDot_boxed_6589_ = lean_unbox(v_danglingDot_6586_);
v_res_6590_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6582_, v_pos_6583_, v_completionInfoPos_6584_, v_id_x3f_6585_, v_danglingDot_boxed_6589_, v_scopeNames_6587_);
return v_res_6590_;
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
