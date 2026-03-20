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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_isPrivatePrefix(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_RequestCancellation_requestCancelled;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_getAliasState(lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* lean_data_value_to_string(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCoreUnfoldingAnnotations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
lean_object* l_Lean_Server_Completion_getEligibleHeaderDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionTagsForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___boxed(lean_object**);
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
lean_inc(v_a_121_);
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
lean_dec(v_a_121_);
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
lean_dec(v_a_121_);
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
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
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
lean_inc(v_toBind_597_);
lean_inc(v_toPure_596_);
v___f_602_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1), 7, 5);
lean_closure_set(v___f_602_, 0, v_f_595_);
lean_closure_set(v___f_602_, 1, v_decl_599_);
lean_closure_set(v___f_602_, 2, v_ci_600_);
lean_closure_set(v___f_602_, 3, v_toPure_596_);
lean_closure_set(v___f_602_, 4, v_toBind_597_);
lean_inc_ref(v___f_602_);
v___f_603_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_603_, 0, v___f_602_);
lean_inc(v_toBind_597_);
lean_inc(v_toPure_596_);
v___f_604_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_604_, 0, v_toPure_596_);
lean_closure_set(v___f_604_, 1, v_toBind_597_);
lean_closure_set(v___f_604_, 2, v___f_603_);
lean_inc(v_toBind_597_);
lean_inc(v_toPure_596_);
v___f_605_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_605_, 0, v___f_602_);
lean_closure_set(v___f_605_, 1, v_toPure_596_);
lean_closure_set(v___f_605_, 2, v_toBind_597_);
lean_closure_set(v___f_605_, 3, v_inst_598_);
lean_closure_set(v___f_605_, 4, v___f_604_);
lean_inc(v_toBind_597_);
lean_inc(v_toPure_596_);
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
lean_inc_ref(v_inst_628_);
v___f_635_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_635_, 0, v_inst_628_);
lean_inc_ref(v_inst_628_);
v___f_636_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_636_, 0, v_inst_628_);
lean_inc_ref(v_inst_628_);
v___f_637_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_637_, 0, v_inst_628_);
lean_inc_ref(v_inst_628_);
v___f_638_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_638_, 0, v_inst_628_);
lean_inc_ref(v_inst_628_);
v___x_639_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_639_, 0, lean_box(0));
lean_closure_set(v___x_639_, 1, lean_box(0));
lean_closure_set(v___x_639_, 2, v_inst_628_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___f_635_);
lean_inc_ref(v_inst_628_);
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
lean_inc_ref(v_inst_628_);
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
lean_inc(v_toPure_655_);
lean_dec_ref(v_toApplicative_633_);
lean_inc(v_toBind_634_);
lean_inc(v_toPure_655_);
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
v___x_692_ = lean_panic_fn(v___x_691_, v_msg_690_);
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
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
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
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_matchUsingNamespace_734_);
return v___x_746_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
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
lean_inc(v_a_929_);
lean_inc_ref(v_a_928_);
lean_inc(v_a_927_);
lean_inc_ref(v_a_926_);
lean_inc_ref(v_a_925_);
lean_inc(v_a_924_);
lean_inc_ref(v_a_923_);
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
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
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
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_id_921_);
v___y_932_ = v___x_985_;
goto v___jp_931_;
}
else
{
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
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
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___lam__0(lean_object* v_ctx_1070_, lean_object* v_id_1071_, uint8_t v_danglingDot_1072_, lean_object* v_env_1073_, lean_object* v_a_1074_, lean_object* v_x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
uint8_t v___y_1085_; uint8_t v___x_1120_; 
v___x_1120_ = l_Lean_Name_isInternal(v_a_1074_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = 1;
lean_inc(v_a_1074_);
v___x_1122_ = l_Lean_Environment_contains(v_env_1073_, v_a_1074_, v___x_1121_);
v___y_1085_ = v___x_1122_;
goto v___jp_1084_;
}
else
{
lean_dec_ref(v_env_1073_);
v___y_1085_ = v___x_1120_;
goto v___jp_1084_;
}
v___jp_1084_:
{
if (v___y_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
v___x_1086_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_1070_, v_a_1074_, v_id_1071_, v_danglingDot_1072_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1109_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1109_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1109_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
if (lean_obj_tag(v_a_1087_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
v_a_1091_ = lean_ctor_get(v_a_1087_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1093_ = v_a_1087_;
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v_a_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1096_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1102_; 
v_a_1102_ = lean_ctor_get(v_a_1087_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v_a_1087_);
if (lean_obj_tag(v_a_1102_) == 1)
{
lean_object* v_val_1103_; lean_object* v___x_1104_; 
lean_del_object(v___x_1089_);
v_val_1103_ = lean_ctor_get(v_a_1102_, 0);
lean_inc(v_val_1103_);
lean_dec_ref(v_a_1102_);
v___x_1104_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_val_1103_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_dec(v_a_1102_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
v___x_1105_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1105_);
v___x_1107_ = v___x_1089_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
v_a_1110_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1086_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1086_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v_a_1074_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v___x_1118_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___lam__0___boxed(lean_object* v_ctx_1123_, lean_object* v_id_1124_, lean_object* v_danglingDot_1125_, lean_object* v_env_1126_, lean_object* v_a_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_danglingDot_boxed_1137_; lean_object* v_res_1138_; 
v_danglingDot_boxed_1137_ = lean_unbox(v_danglingDot_1125_);
v_res_1138_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___lam__0(v_ctx_1123_, v_id_1124_, v_danglingDot_boxed_1137_, v_env_1126_, v_a_1127_, v_x_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_1139_, lean_object* v_keys_1140_, lean_object* v_vals_1141_, lean_object* v_i_1142_, lean_object* v_acc_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_array_get_size(v_keys_1140_);
v___x_1153_ = lean_nat_dec_lt(v_i_1142_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_i_1142_);
lean_dec_ref(v_f_1139_);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_acc_1143_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v_k_1156_; lean_object* v_v_1157_; lean_object* v___x_1158_; 
v_k_1156_ = lean_array_fget_borrowed(v_keys_1140_, v_i_1142_);
v_v_1157_ = lean_array_fget_borrowed(v_vals_1141_, v_i_1142_);
lean_inc_ref(v_f_1139_);
lean_inc(v___y_1150_);
lean_inc_ref(v___y_1149_);
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc_ref(v___y_1146_);
lean_inc(v___y_1145_);
lean_inc_ref(v___y_1144_);
lean_inc(v_v_1157_);
lean_inc(v_k_1156_);
v___x_1158_ = lean_apply_11(v_f_1139_, v_acc_1143_, v_k_1156_, v_v_1157_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
if (lean_obj_tag(v_a_1159_) == 0)
{
lean_dec_ref(v_a_1159_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_i_1142_);
lean_dec_ref(v_f_1139_);
return v___x_1158_;
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v___x_1158_);
v_a_1160_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v_a_1159_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_i_1142_, v___x_1161_);
lean_dec(v_i_1142_);
v_i_1142_ = v___x_1162_;
v_acc_1143_ = v_a_1160_;
goto _start;
}
}
else
{
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_i_1142_);
lean_dec_ref(v_f_1139_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_1164_, lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_i_1167_, lean_object* v_acc_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1164_, v_keys_1165_, v_vals_1166_, v_i_1167_, v_acc_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec_ref(v_vals_1166_);
lean_dec_ref(v_keys_1165_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_object* v_es_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1211_; 
v_es_1189_ = lean_ctor_get(v_x_1179_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1191_ = v_x_1179_;
v_isShared_1192_ = v_isSharedCheck_1211_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_es_1189_);
lean_dec(v_x_1179_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1211_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_array_get_size(v_es_1189_);
v___x_1195_ = lean_nat_dec_lt(v___x_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v_es_1189_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_f_1178_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set_tag(v___x_1191_, 1);
lean_ctor_set(v___x_1191_, 0, v_x_1180_);
v___x_1197_ = v___x_1191_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_x_1180_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
else
{
uint8_t v___x_1200_; 
v___x_1200_ = lean_nat_dec_le(v___x_1194_, v___x_1194_);
if (v___x_1200_ == 0)
{
if (v___x_1195_ == 0)
{
lean_object* v___x_1202_; 
lean_dec_ref(v_es_1189_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_f_1178_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set_tag(v___x_1191_, 1);
lean_ctor_set(v___x_1191_, 0, v_x_1180_);
v___x_1202_ = v___x_1191_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_x_1180_);
v___x_1202_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
lean_del_object(v___x_1191_);
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = lean_usize_of_nat(v___x_1194_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1178_, v_es_1189_, v___x_1205_, v___x_1206_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v_es_1189_);
return v___x_1207_;
}
}
else
{
size_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
lean_del_object(v___x_1191_);
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = lean_usize_of_nat(v___x_1194_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1178_, v_es_1189_, v___x_1208_, v___x_1209_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v_es_1189_);
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_ks_1212_; lean_object* v_vs_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_ks_1212_ = lean_ctor_get(v_x_1179_, 0);
lean_inc_ref(v_ks_1212_);
v_vs_1213_ = lean_ctor_get(v_x_1179_, 1);
lean_inc_ref(v_vs_1213_);
lean_dec_ref(v_x_1179_);
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1178_, v_ks_1212_, v_vs_1213_, v___x_1214_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v_vs_1213_);
lean_dec_ref(v_ks_1212_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1216_, lean_object* v_as_1217_, size_t v_i_1218_, size_t v_stop_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_a_1230_; lean_object* v___y_1235_; uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_eq(v_i_1218_, v_stop_1219_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_array_uget_borrowed(v_as_1217_, v_i_1218_);
switch(lean_obj_tag(v___x_1239_))
{
case 0:
{
lean_object* v_key_1240_; lean_object* v_val_1241_; lean_object* v___x_1242_; 
v_key_1240_ = lean_ctor_get(v___x_1239_, 0);
v_val_1241_ = lean_ctor_get(v___x_1239_, 1);
lean_inc_ref(v_f_1216_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v_val_1241_);
lean_inc(v_key_1240_);
v___x_1242_ = lean_apply_11(v_f_1216_, v_b_1220_, v_key_1240_, v_val_1241_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
v___y_1235_ = v___x_1242_;
goto v___jp_1234_;
}
case 1:
{
lean_object* v_node_1243_; lean_object* v___x_1244_; 
v_node_1243_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v_node_1243_);
lean_inc_ref(v_f_1216_);
v___x_1244_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1216_, v_node_1243_, v_b_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
v___y_1235_ = v___x_1244_;
goto v___jp_1234_;
}
default: 
{
v_a_1230_ = v_b_1220_;
goto v___jp_1229_;
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v_f_1216_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_b_1220_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
v___jp_1229_:
{
size_t v___x_1231_; size_t v___x_1232_; 
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_add(v_i_1218_, v___x_1231_);
v_i_1218_ = v___x_1232_;
v_b_1220_ = v_a_1230_;
goto _start;
}
v___jp_1234_:
{
if (lean_obj_tag(v___y_1235_) == 0)
{
lean_object* v_a_1236_; 
v_a_1236_ = lean_ctor_get(v___y_1235_, 0);
if (lean_obj_tag(v_a_1236_) == 0)
{
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v_f_1216_);
return v___y_1235_;
}
else
{
lean_object* v_a_1237_; 
lean_inc_ref(v_a_1236_);
lean_dec_ref(v___y_1235_);
v_a_1237_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v_a_1236_);
v_a_1230_ = v_a_1237_;
goto v___jp_1229_;
}
}
else
{
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v_f_1216_);
return v___y_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_1247_, lean_object* v_as_1248_, lean_object* v_i_1249_, lean_object* v_stop_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
size_t v_i_boxed_1260_; size_t v_stop_boxed_1261_; lean_object* v_res_1262_; 
v_i_boxed_1260_ = lean_unbox_usize(v_i_1249_);
lean_dec(v_i_1249_);
v_stop_boxed_1261_ = lean_unbox_usize(v_stop_1250_);
lean_dec(v_stop_1250_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1247_, v_as_1248_, v_i_boxed_1260_, v_stop_boxed_1261_, v_b_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec_ref(v_as_1248_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1263_, v_x_1264_, v_x_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_apply_10(v_f_1275_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, lean_box(0));
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_f_1288_, lean_object* v_x_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___lam__0(v_f_1288_, v_x_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(lean_object* v_map_1301_, lean_object* v_f_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1311_, 0, v_f_1302_);
v___x_1312_ = lean_box(0);
v___x_1313_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1311_, v_map_1301_, v___x_1312_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_map_1314_, lean_object* v_f_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(v_map_1314_, v_f_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg(lean_object* v_f_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
if (lean_obj_tag(v_x_1327_) == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_f_1325_);
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_x_1326_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
else
{
lean_object* v_key_1338_; lean_object* v_value_1339_; lean_object* v_tail_1340_; lean_object* v___x_1341_; 
v_key_1338_ = lean_ctor_get(v_x_1327_, 0);
lean_inc(v_key_1338_);
v_value_1339_ = lean_ctor_get(v_x_1327_, 1);
lean_inc(v_value_1339_);
v_tail_1340_ = lean_ctor_get(v_x_1327_, 2);
lean_inc(v_tail_1340_);
lean_dec_ref(v_x_1327_);
lean_inc_ref(v_f_1325_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
v___x_1341_ = lean_apply_10(v_f_1325_, v_key_1338_, v_value_1339_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, lean_box(0));
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
if (lean_obj_tag(v_a_1342_) == 0)
{
lean_dec_ref(v_a_1342_);
lean_dec(v_tail_1340_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_f_1325_);
return v___x_1341_;
}
else
{
lean_object* v_a_1343_; 
lean_dec_ref(v___x_1341_);
v_a_1343_ = lean_ctor_get(v_a_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v_a_1342_);
v_x_1326_ = v_a_1343_;
v_x_1327_ = v_tail_1340_;
goto _start;
}
}
else
{
lean_dec(v_tail_1340_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_f_1325_);
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg___boxed(lean_object* v_f_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg(v_f_1345_, v_x_1346_, v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg(lean_object* v_f_1357_, lean_object* v_as_1358_, size_t v_i_1359_, size_t v_stop_1360_, lean_object* v_b_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_usize_dec_eq(v_i_1359_, v_stop_1360_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_array_uget_borrowed(v_as_1358_, v_i_1359_);
v___x_1372_ = lean_box(0);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc_ref(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___x_1371_);
lean_inc_ref(v_f_1357_);
v___x_1373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg(v_f_1357_, v___x_1372_, v___x_1371_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
if (lean_obj_tag(v_a_1374_) == 0)
{
lean_dec_ref(v_a_1374_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec_ref(v_f_1357_);
return v___x_1373_;
}
else
{
lean_object* v_a_1375_; size_t v___x_1376_; size_t v___x_1377_; 
lean_dec_ref(v___x_1373_);
v_a_1375_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref(v_a_1374_);
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1359_, v___x_1376_);
v_i_1359_ = v___x_1377_;
v_b_1361_ = v_a_1375_;
goto _start;
}
}
else
{
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec_ref(v_f_1357_);
return v___x_1373_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec_ref(v_f_1357_);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_b_1361_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg___boxed(lean_object* v_f_1381_, lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_stop_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
size_t v_i_boxed_1394_; size_t v_stop_boxed_1395_; lean_object* v_res_1396_; 
v_i_boxed_1394_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_stop_boxed_1395_ = lean_unbox_usize(v_stop_1384_);
lean_dec(v_stop_1384_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg(v_f_1381_, v_as_1382_, v_i_boxed_1394_, v_stop_boxed_1395_, v_b_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec_ref(v_as_1382_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object* v_s_1397_, lean_object* v_f_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_map_u2081_1407_; lean_object* v_map_u2082_1408_; lean_object* v_buckets_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_map_u2081_1407_ = lean_ctor_get(v_s_1397_, 0);
lean_inc_ref(v_map_u2081_1407_);
v_map_u2082_1408_ = lean_ctor_get(v_s_1397_, 1);
lean_inc_ref(v_map_u2082_1408_);
lean_dec_ref(v_s_1397_);
v_buckets_1409_ = lean_ctor_get(v_map_u2081_1407_, 1);
lean_inc_ref(v_buckets_1409_);
lean_dec_ref(v_map_u2081_1407_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_array_get_size(v_buckets_1409_);
v___x_1412_ = lean_nat_dec_lt(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_buckets_1409_);
v___x_1413_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(v_map_u2082_1408_, v_f_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_nat_dec_le(v___x_1411_, v___x_1411_);
if (v___x_1415_ == 0)
{
if (v___x_1412_ == 0)
{
lean_object* v___x_1416_; 
lean_dec_ref(v_buckets_1409_);
v___x_1416_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(v_map_u2082_1408_, v_f_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1416_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1411_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc_ref(v_f_1398_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg(v_f_1398_, v_buckets_1409_, v___x_1417_, v___x_1418_, v___x_1414_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref(v_buckets_1409_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
if (lean_obj_tag(v_a_1420_) == 0)
{
lean_dec_ref(v_a_1420_);
lean_dec_ref(v_map_u2082_1408_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_f_1398_);
return v___x_1419_;
}
else
{
lean_object* v___x_1421_; 
lean_dec_ref(v_a_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(v_map_u2082_1408_, v_f_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1421_;
}
}
else
{
lean_dec_ref(v_map_u2082_1408_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_f_1398_);
return v___x_1419_;
}
}
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1411_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc_ref(v_f_1398_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg(v_f_1398_, v_buckets_1409_, v___x_1422_, v___x_1423_, v___x_1414_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref(v_buckets_1409_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
if (lean_obj_tag(v_a_1425_) == 0)
{
lean_dec_ref(v_a_1425_);
lean_dec_ref(v_map_u2082_1408_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_f_1398_);
return v___x_1424_;
}
else
{
lean_object* v___x_1426_; 
lean_dec_ref(v_a_1425_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(v_map_u2082_1408_, v_f_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1426_;
}
}
else
{
lean_dec_ref(v_map_u2082_1408_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_f_1398_);
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object* v_s_1427_, lean_object* v_f_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_s_1427_, v_f_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object* v_ctx_1438_, lean_object* v_id_1439_, uint8_t v_danglingDot_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_env_1450_; lean_object* v___x_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = lean_st_ref_get(v_a_1447_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_ref(v_env_1450_);
lean_dec(v___x_1449_);
v___x_1451_ = lean_box(v_danglingDot_1440_);
lean_inc_ref(v_env_1450_);
v___f_1452_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1452_, 0, v_ctx_1438_);
lean_closure_set(v___f_1452_, 1, v_id_1439_);
lean_closure_set(v___f_1452_, 2, v___x_1451_);
lean_closure_set(v___f_1452_, 3, v_env_1450_);
v___x_1453_ = l_Lean_Environment_getNamespaceSet(v_env_1450_);
v___x_1454_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v___x_1453_, v___f_1452_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object* v_ctx_1455_, lean_object* v_id_1456_, lean_object* v_danglingDot_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
uint8_t v_danglingDot_boxed_1466_; lean_object* v_res_1467_; 
v_danglingDot_boxed_1466_ = lean_unbox(v_danglingDot_1457_);
v_res_1467_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1455_, v_id_1456_, v_danglingDot_boxed_1466_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object* v_00_u03b2_1468_, lean_object* v_s_1469_, lean_object* v_f_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_s_1469_, v_f_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object* v_00_u03b2_1480_, lean_object* v_s_1481_, lean_object* v_f_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_00_u03b2_1480_, v_s_1481_, v_f_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0(lean_object* v_00_u03b2_1492_, lean_object* v_f_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___redArg(v_f_1493_, v_x_1494_, v_x_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1505_, lean_object* v_f_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__0(v_00_u03b2_1505_, v_f_1506_, v_x_1507_, v_x_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1(lean_object* v_00_u03b2_1518_, lean_object* v_map_1519_, lean_object* v_f_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___redArg(v_map_1519_, v_f_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1530_, lean_object* v_map_1531_, lean_object* v_f_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1(v_00_u03b2_1530_, v_map_1531_, v_f_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2(lean_object* v_00_u03b2_1542_, lean_object* v_f_1543_, lean_object* v_as_1544_, size_t v_i_1545_, size_t v_stop_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___redArg(v_f_1543_, v_as_1544_, v_i_1545_, v_stop_1546_, v_b_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_f_1558_, lean_object* v_as_1559_, lean_object* v_i_1560_, lean_object* v_stop_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
size_t v_i_boxed_1571_; size_t v_stop_boxed_1572_; lean_object* v_res_1573_; 
v_i_boxed_1571_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_stop_boxed_1572_ = lean_unbox_usize(v_stop_1561_);
lean_dec(v_stop_1561_);
v_res_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__2(v_00_u03b2_1557_, v_f_1558_, v_as_1559_, v_i_boxed_1571_, v_stop_boxed_1572_, v_b_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec_ref(v_as_1559_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1574_, lean_object* v_f_1575_, lean_object* v_init_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1575_, v_map_1574_, v_init_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1586_, lean_object* v_f_1587_, lean_object* v_init_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___redArg(v_map_1586_, v_f_1587_, v_init_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1598_, lean_object* v_00_u03b2_1599_, lean_object* v_map_1600_, lean_object* v_f_1601_, lean_object* v_init_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1601_, v_map_1600_, v_init_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1612_, lean_object* v_00_u03b2_1613_, lean_object* v_map_1614_, lean_object* v_f_1615_, lean_object* v_init_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2(v_00_u03c3_1612_, v_00_u03b2_1613_, v_map_1614_, v_f_1615_, v_init_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1626_, lean_object* v_00_u03b1_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_f_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1629_, v_x_1630_, v_x_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1641_, lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_f_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1641_, v_00_u03b1_1642_, v_00_u03b2_1643_, v_f_1644_, v_x_1645_, v_x_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_00_u03c3_1658_, lean_object* v_f_1659_, lean_object* v_as_1660_, size_t v_i_1661_, size_t v_stop_1662_, lean_object* v_b_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1659_, v_as_1660_, v_i_1661_, v_stop_1662_, v_b_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_00_u03c3_1675_, lean_object* v_f_1676_, lean_object* v_as_1677_, lean_object* v_i_1678_, lean_object* v_stop_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
size_t v_i_boxed_1689_; size_t v_stop_boxed_1690_; lean_object* v_res_1691_; 
v_i_boxed_1689_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_stop_boxed_1690_ = lean_unbox_usize(v_stop_1679_);
lean_dec(v_stop_1679_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1673_, v_00_u03b2_1674_, v_00_u03c3_1675_, v_f_1676_, v_as_1677_, v_i_boxed_1689_, v_stop_boxed_1690_, v_b_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec_ref(v_as_1677_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1692_, lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_f_1695_, lean_object* v_keys_1696_, lean_object* v_vals_1697_, lean_object* v_heq_1698_, lean_object* v_i_1699_, lean_object* v_acc_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1695_, v_keys_1696_, v_vals_1697_, v_i_1699_, v_acc_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_00_u03c3_1710_ = _args[0];
lean_object* v_00_u03b1_1711_ = _args[1];
lean_object* v_00_u03b2_1712_ = _args[2];
lean_object* v_f_1713_ = _args[3];
lean_object* v_keys_1714_ = _args[4];
lean_object* v_vals_1715_ = _args[5];
lean_object* v_heq_1716_ = _args[6];
lean_object* v_i_1717_ = _args[7];
lean_object* v_acc_1718_ = _args[8];
lean_object* v___y_1719_ = _args[9];
lean_object* v___y_1720_ = _args[10];
lean_object* v___y_1721_ = _args[11];
lean_object* v___y_1722_ = _args[12];
lean_object* v___y_1723_ = _args[13];
lean_object* v___y_1724_ = _args[14];
lean_object* v___y_1725_ = _args[15];
lean_object* v___y_1726_ = _args[16];
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1710_, v_00_u03b1_1711_, v_00_u03b2_1712_, v_f_1713_, v_keys_1714_, v_vals_1715_, v_heq_1716_, v_i_1717_, v_acc_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec_ref(v_vals_1715_);
lean_dec_ref(v_keys_1714_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* v_n_1728_){
_start:
{
if (lean_obj_tag(v_n_1728_) == 2)
{
lean_object* v_i_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_i_1729_ = lean_ctor_get(v_n_1728_, 1);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = lean_nat_dec_eq(v_i_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_inc_ref(v_n_1728_);
return v_n_1728_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Lean_isPrivatePrefix(v_n_1728_);
if (v___x_1732_ == 0)
{
lean_inc_ref(v_n_1728_);
return v_n_1728_;
}
else
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_box(0);
return v___x_1733_;
}
}
}
else
{
lean_inc(v_n_1728_);
return v_n_1728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* v_n_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_1734_);
lean_dec(v_n_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* v_n_u2081_1736_, lean_object* v_n_u2082_1737_){
_start:
{
lean_object* v_n_u2081_1738_; lean_object* v_n_u2082_1739_; 
v_n_u2081_1738_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2081_1736_);
lean_dec(v_n_u2081_1736_);
v_n_u2082_1739_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2082_1737_);
lean_dec(v_n_u2082_1737_);
switch(lean_obj_tag(v_n_u2081_1738_))
{
case 0:
{
if (lean_obj_tag(v_n_u2082_1739_) == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = 1;
return v___x_1740_;
}
else
{
uint8_t v___x_1741_; 
lean_dec(v_n_u2082_1739_);
v___x_1741_ = 0;
return v___x_1741_;
}
}
case 1:
{
if (lean_obj_tag(v_n_u2082_1739_) == 1)
{
lean_object* v_pre_1742_; lean_object* v_str_1743_; lean_object* v_pre_1744_; lean_object* v_str_1745_; uint8_t v___x_1746_; 
v_pre_1742_ = lean_ctor_get(v_n_u2081_1738_, 0);
lean_inc(v_pre_1742_);
v_str_1743_ = lean_ctor_get(v_n_u2081_1738_, 1);
lean_inc_ref(v_str_1743_);
lean_dec_ref(v_n_u2081_1738_);
v_pre_1744_ = lean_ctor_get(v_n_u2082_1739_, 0);
lean_inc(v_pre_1744_);
v_str_1745_ = lean_ctor_get(v_n_u2082_1739_, 1);
lean_inc_ref(v_str_1745_);
lean_dec_ref(v_n_u2082_1739_);
v___x_1746_ = lean_string_dec_lt(v_str_1743_, v_str_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_string_dec_eq(v_str_1743_, v_str_1745_);
lean_dec_ref(v_str_1745_);
lean_dec_ref(v_str_1743_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
lean_dec(v_pre_1744_);
lean_dec(v_pre_1742_);
v___x_1748_ = 2;
return v___x_1748_;
}
else
{
v_n_u2081_1736_ = v_pre_1742_;
v_n_u2082_1737_ = v_pre_1744_;
goto _start;
}
}
else
{
uint8_t v___x_1750_; 
lean_dec_ref(v_str_1745_);
lean_dec(v_pre_1744_);
lean_dec_ref(v_str_1743_);
lean_dec(v_pre_1742_);
v___x_1750_ = 0;
return v___x_1750_;
}
}
else
{
uint8_t v___x_1751_; 
lean_dec_ref(v_n_u2081_1738_);
lean_dec(v_n_u2082_1739_);
v___x_1751_ = 2;
return v___x_1751_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1739_))
{
case 0:
{
uint8_t v___x_1752_; 
lean_dec_ref(v_n_u2081_1738_);
v___x_1752_ = 2;
return v___x_1752_;
}
case 1:
{
uint8_t v___x_1753_; 
lean_dec_ref(v_n_u2082_1739_);
lean_dec_ref(v_n_u2081_1738_);
v___x_1753_ = 0;
return v___x_1753_;
}
default: 
{
lean_object* v_pre_1754_; lean_object* v_i_1755_; lean_object* v_pre_1756_; lean_object* v_i_1757_; uint8_t v___x_1758_; 
v_pre_1754_ = lean_ctor_get(v_n_u2081_1738_, 0);
lean_inc(v_pre_1754_);
v_i_1755_ = lean_ctor_get(v_n_u2081_1738_, 1);
lean_inc(v_i_1755_);
lean_dec_ref(v_n_u2081_1738_);
v_pre_1756_ = lean_ctor_get(v_n_u2082_1739_, 0);
lean_inc(v_pre_1756_);
v_i_1757_ = lean_ctor_get(v_n_u2082_1739_, 1);
lean_inc(v_i_1757_);
lean_dec_ref(v_n_u2082_1739_);
v___x_1758_ = lean_nat_dec_lt(v_i_1755_, v_i_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_nat_dec_eq(v_i_1755_, v_i_1757_);
lean_dec(v_i_1757_);
lean_dec(v_i_1755_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
lean_dec(v_pre_1756_);
lean_dec(v_pre_1754_);
v___x_1760_ = 2;
return v___x_1760_;
}
else
{
v_n_u2081_1736_ = v_pre_1754_;
v_n_u2082_1737_ = v_pre_1756_;
goto _start;
}
}
else
{
uint8_t v___x_1762_; 
lean_dec(v_i_1757_);
lean_dec(v_pre_1756_);
lean_dec(v_i_1755_);
lean_dec(v_pre_1754_);
v___x_1762_ = 0;
return v___x_1762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1763_, lean_object* v_n_u2082_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1763_, v_n_u2082_1764_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1768_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1770_ = l_Std_TreeSet_ofArray___redArg(v_names_1768_, v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1771_);
lean_dec_ref(v_names_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1773_, lean_object* v_t_1774_){
_start:
{
if (lean_obj_tag(v_t_1774_) == 0)
{
lean_object* v_k_1775_; lean_object* v_l_1776_; lean_object* v_r_1777_; uint8_t v___x_1778_; 
v_k_1775_ = lean_ctor_get(v_t_1774_, 1);
lean_inc(v_k_1775_);
v_l_1776_ = lean_ctor_get(v_t_1774_, 3);
lean_inc(v_l_1776_);
v_r_1777_ = lean_ctor_get(v_t_1774_, 4);
lean_inc(v_r_1777_);
lean_dec_ref(v_t_1774_);
lean_inc(v_k_1773_);
v___x_1778_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1773_, v_k_1775_);
switch(v___x_1778_)
{
case 0:
{
lean_dec(v_r_1777_);
v_t_1774_ = v_l_1776_;
goto _start;
}
case 1:
{
uint8_t v___x_1780_; 
lean_dec(v_r_1777_);
lean_dec(v_l_1776_);
lean_dec(v_k_1773_);
v___x_1780_ = 1;
return v___x_1780_;
}
default: 
{
lean_dec(v_l_1776_);
v_t_1774_ = v_r_1777_;
goto _start;
}
}
}
else
{
uint8_t v___x_1782_; 
lean_dec(v_k_1773_);
v___x_1782_ = 0;
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1783_, lean_object* v_t_1784_){
_start:
{
uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_res_1785_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1783_, v_t_1784_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1787_, lean_object* v_v_1788_, lean_object* v_t_1789_){
_start:
{
if (lean_obj_tag(v_t_1789_) == 0)
{
lean_object* v_size_1790_; lean_object* v_k_1791_; lean_object* v_v_1792_; lean_object* v_l_1793_; lean_object* v_r_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_2074_; 
v_size_1790_ = lean_ctor_get(v_t_1789_, 0);
v_k_1791_ = lean_ctor_get(v_t_1789_, 1);
v_v_1792_ = lean_ctor_get(v_t_1789_, 2);
v_l_1793_ = lean_ctor_get(v_t_1789_, 3);
v_r_1794_ = lean_ctor_get(v_t_1789_, 4);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_t_1789_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_1796_ = v_t_1789_;
v_isShared_1797_ = v_isSharedCheck_2074_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_r_1794_);
lean_inc(v_l_1793_);
lean_inc(v_v_1792_);
lean_inc(v_k_1791_);
lean_inc(v_size_1790_);
lean_dec(v_t_1789_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_2074_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
uint8_t v___x_1798_; 
lean_inc(v_k_1791_);
lean_inc(v_k_1787_);
v___x_1798_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1787_, v_k_1791_);
switch(v___x_1798_)
{
case 0:
{
lean_object* v_impl_1799_; lean_object* v___x_1800_; 
lean_dec(v_size_1790_);
v_impl_1799_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1787_, v_v_1788_, v_l_1793_);
v___x_1800_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1794_) == 0)
{
lean_object* v_size_1801_; lean_object* v_size_1802_; lean_object* v_k_1803_; lean_object* v_v_1804_; lean_object* v_l_1805_; lean_object* v_r_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_size_1801_ = lean_ctor_get(v_r_1794_, 0);
v_size_1802_ = lean_ctor_get(v_impl_1799_, 0);
lean_inc(v_size_1802_);
v_k_1803_ = lean_ctor_get(v_impl_1799_, 1);
lean_inc(v_k_1803_);
v_v_1804_ = lean_ctor_get(v_impl_1799_, 2);
lean_inc(v_v_1804_);
v_l_1805_ = lean_ctor_get(v_impl_1799_, 3);
lean_inc(v_l_1805_);
v_r_1806_ = lean_ctor_get(v_impl_1799_, 4);
lean_inc(v_r_1806_);
v___x_1807_ = lean_unsigned_to_nat(3u);
v___x_1808_ = lean_nat_mul(v___x_1807_, v_size_1801_);
v___x_1809_ = lean_nat_dec_lt(v___x_1808_, v_size_1802_);
lean_dec(v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec(v_r_1806_);
lean_dec(v_l_1805_);
lean_dec(v_v_1804_);
lean_dec(v_k_1803_);
v___x_1810_ = lean_nat_add(v___x_1800_, v_size_1802_);
lean_dec(v_size_1802_);
v___x_1811_ = lean_nat_add(v___x_1810_, v_size_1801_);
lean_dec(v___x_1810_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 3, v_impl_1799_);
lean_ctor_set(v___x_1796_, 0, v___x_1811_);
v___x_1813_ = v___x_1796_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_impl_1799_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_r_1794_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
else
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1880_; 
v_isSharedCheck_1880_ = !lean_is_exclusive(v_impl_1799_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; lean_object* v_unused_1885_; 
v_unused_1881_ = lean_ctor_get(v_impl_1799_, 4);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_impl_1799_, 3);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_impl_1799_, 2);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_impl_1799_, 1);
lean_dec(v_unused_1884_);
v_unused_1885_ = lean_ctor_get(v_impl_1799_, 0);
lean_dec(v_unused_1885_);
v___x_1816_ = v_impl_1799_;
v_isShared_1817_ = v_isSharedCheck_1880_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v_impl_1799_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1880_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_size_1818_; lean_object* v_size_1819_; lean_object* v_k_1820_; lean_object* v_v_1821_; lean_object* v_l_1822_; lean_object* v_r_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_size_1818_ = lean_ctor_get(v_l_1805_, 0);
v_size_1819_ = lean_ctor_get(v_r_1806_, 0);
v_k_1820_ = lean_ctor_get(v_r_1806_, 1);
v_v_1821_ = lean_ctor_get(v_r_1806_, 2);
v_l_1822_ = lean_ctor_get(v_r_1806_, 3);
v_r_1823_ = lean_ctor_get(v_r_1806_, 4);
v___x_1824_ = lean_unsigned_to_nat(2u);
v___x_1825_ = lean_nat_mul(v___x_1824_, v_size_1818_);
v___x_1826_ = lean_nat_dec_lt(v_size_1819_, v___x_1825_);
lean_dec(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1855_; 
lean_inc(v_r_1823_);
lean_inc(v_l_1822_);
lean_inc(v_v_1821_);
lean_inc(v_k_1820_);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_r_1806_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1856_ = lean_ctor_get(v_r_1806_, 4);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_r_1806_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_r_1806_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_r_1806_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_r_1806_, 0);
lean_dec(v_unused_1860_);
v___x_1828_ = v_r_1806_;
v_isShared_1829_ = v_isSharedCheck_1855_;
goto v_resetjp_1827_;
}
else
{
lean_dec(v_r_1806_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1855_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___x_1843_; lean_object* v___y_1845_; 
v___x_1830_ = lean_nat_add(v___x_1800_, v_size_1802_);
lean_dec(v_size_1802_);
v___x_1831_ = lean_nat_add(v___x_1830_, v_size_1801_);
lean_dec(v___x_1830_);
v___x_1843_ = lean_nat_add(v___x_1800_, v_size_1818_);
if (lean_obj_tag(v_l_1822_) == 0)
{
lean_object* v_size_1853_; 
v_size_1853_ = lean_ctor_get(v_l_1822_, 0);
lean_inc(v_size_1853_);
v___y_1845_ = v_size_1853_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_unsigned_to_nat(0u);
v___y_1845_ = v___x_1854_;
goto v___jp_1844_;
}
v___jp_1832_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_nat_add(v___y_1833_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec(v___y_1833_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 4, v_r_1794_);
lean_ctor_set(v___x_1828_, 3, v_r_1823_);
lean_ctor_set(v___x_1828_, 2, v_v_1792_);
lean_ctor_set(v___x_1828_, 1, v_k_1791_);
lean_ctor_set(v___x_1828_, 0, v___x_1836_);
v___x_1838_ = v___x_1828_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_r_1823_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_r_1794_);
v___x_1838_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 4, v___x_1838_);
lean_ctor_set(v___x_1816_, 3, v___y_1834_);
lean_ctor_set(v___x_1816_, 2, v_v_1821_);
lean_ctor_set(v___x_1816_, 1, v_k_1820_);
lean_ctor_set(v___x_1816_, 0, v___x_1831_);
v___x_1840_ = v___x_1816_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_k_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_v_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v___y_1834_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
v___jp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_nat_add(v___x_1843_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec(v___x_1843_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_l_1822_);
lean_ctor_set(v___x_1796_, 3, v_l_1805_);
lean_ctor_set(v___x_1796_, 2, v_v_1804_);
lean_ctor_set(v___x_1796_, 1, v_k_1803_);
lean_ctor_set(v___x_1796_, 0, v___x_1846_);
v___x_1848_ = v___x_1796_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_k_1803_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_v_1804_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_l_1805_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v_l_1822_);
v___x_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_nat_add(v___x_1800_, v_size_1801_);
if (lean_obj_tag(v_r_1823_) == 0)
{
lean_object* v_size_1850_; 
v_size_1850_ = lean_ctor_get(v_r_1823_, 0);
lean_inc(v_size_1850_);
v___y_1833_ = v___x_1849_;
v___y_1834_ = v___x_1848_;
v___y_1835_ = v_size_1850_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
v___y_1833_ = v___x_1849_;
v___y_1834_ = v___x_1848_;
v___y_1835_ = v___x_1851_;
goto v___jp_1832_;
}
}
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_del_object(v___x_1796_);
v___x_1861_ = lean_nat_add(v___x_1800_, v_size_1802_);
lean_dec(v_size_1802_);
v___x_1862_ = lean_nat_add(v___x_1861_, v_size_1801_);
lean_dec(v___x_1861_);
v___x_1863_ = lean_nat_add(v___x_1800_, v_size_1801_);
v___x_1864_ = lean_nat_add(v___x_1863_, v_size_1819_);
lean_dec(v___x_1863_);
lean_inc_ref(v_r_1794_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 4, v_r_1794_);
lean_ctor_set(v___x_1816_, 3, v_r_1806_);
lean_ctor_set(v___x_1816_, 2, v_v_1792_);
lean_ctor_set(v___x_1816_, 1, v_k_1791_);
lean_ctor_set(v___x_1816_, 0, v___x_1864_);
v___x_1866_ = v___x_1816_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_r_1806_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_r_1794_);
v___x_1866_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_isSharedCheck_1873_ = !lean_is_exclusive(v_r_1794_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; lean_object* v_unused_1875_; lean_object* v_unused_1876_; lean_object* v_unused_1877_; lean_object* v_unused_1878_; 
v_unused_1874_ = lean_ctor_get(v_r_1794_, 4);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_r_1794_, 3);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v_r_1794_, 2);
lean_dec(v_unused_1876_);
v_unused_1877_ = lean_ctor_get(v_r_1794_, 1);
lean_dec(v_unused_1877_);
v_unused_1878_ = lean_ctor_get(v_r_1794_, 0);
lean_dec(v_unused_1878_);
v___x_1868_ = v_r_1794_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_dec(v_r_1794_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 4, v___x_1866_);
lean_ctor_set(v___x_1868_, 3, v_l_1805_);
lean_ctor_set(v___x_1868_, 2, v_v_1804_);
lean_ctor_set(v___x_1868_, 1, v_k_1803_);
lean_ctor_set(v___x_1868_, 0, v___x_1862_);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_k_1803_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_v_1804_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_l_1805_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v___x_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1886_; 
v_l_1886_ = lean_ctor_get(v_impl_1799_, 3);
lean_inc(v_l_1886_);
if (lean_obj_tag(v_l_1886_) == 0)
{
lean_object* v_r_1887_; lean_object* v_k_1888_; lean_object* v_v_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1900_; 
v_r_1887_ = lean_ctor_get(v_impl_1799_, 4);
v_k_1888_ = lean_ctor_get(v_impl_1799_, 1);
v_v_1889_ = lean_ctor_get(v_impl_1799_, 2);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_impl_1799_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1901_ = lean_ctor_get(v_impl_1799_, 3);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_impl_1799_, 0);
lean_dec(v_unused_1902_);
v___x_1891_ = v_impl_1799_;
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_r_1887_);
lean_inc(v_v_1889_);
lean_inc(v_k_1888_);
lean_dec(v_impl_1799_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1887_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 3, v_r_1887_);
lean_ctor_set(v___x_1891_, 2, v_v_1792_);
lean_ctor_set(v___x_1891_, 1, v_k_1791_);
lean_ctor_set(v___x_1891_, 0, v___x_1800_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_r_1887_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_r_1887_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v___x_1895_);
lean_ctor_set(v___x_1796_, 3, v_l_1886_);
lean_ctor_set(v___x_1796_, 2, v_v_1889_);
lean_ctor_set(v___x_1796_, 1, v_k_1888_);
lean_ctor_set(v___x_1796_, 0, v___x_1893_);
v___x_1897_ = v___x_1796_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_k_1888_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_v_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_l_1886_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_r_1903_; 
v_r_1903_ = lean_ctor_get(v_impl_1799_, 4);
lean_inc(v_r_1903_);
if (lean_obj_tag(v_r_1903_) == 0)
{
lean_object* v_k_1904_; lean_object* v_v_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1928_; 
v_k_1904_ = lean_ctor_get(v_impl_1799_, 1);
v_v_1905_ = lean_ctor_get(v_impl_1799_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_impl_1799_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; 
v_unused_1929_ = lean_ctor_get(v_impl_1799_, 4);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_impl_1799_, 3);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_impl_1799_, 0);
lean_dec(v_unused_1931_);
v___x_1907_ = v_impl_1799_;
v_isShared_1908_ = v_isSharedCheck_1928_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_v_1905_);
lean_inc(v_k_1904_);
lean_dec(v_impl_1799_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1928_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_k_1909_; lean_object* v_v_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1924_; 
v_k_1909_ = lean_ctor_get(v_r_1903_, 1);
v_v_1910_ = lean_ctor_get(v_r_1903_, 2);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_r_1903_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1925_ = lean_ctor_get(v_r_1903_, 4);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_r_1903_, 3);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_r_1903_, 0);
lean_dec(v_unused_1927_);
v___x_1912_ = v_r_1903_;
v_isShared_1913_ = v_isSharedCheck_1924_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_v_1910_);
lean_inc(v_k_1909_);
lean_dec(v_r_1903_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1924_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(3u);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 4, v_l_1886_);
lean_ctor_set(v___x_1912_, 3, v_l_1886_);
lean_ctor_set(v___x_1912_, 2, v_v_1905_);
lean_ctor_set(v___x_1912_, 1, v_k_1904_);
lean_ctor_set(v___x_1912_, 0, v___x_1800_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1904_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1905_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_l_1886_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_l_1886_);
v___x_1916_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v_l_1886_);
lean_ctor_set(v___x_1907_, 2, v_v_1792_);
lean_ctor_set(v___x_1907_, 1, v_k_1791_);
lean_ctor_set(v___x_1907_, 0, v___x_1800_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_l_1886_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_l_1886_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v___x_1918_);
lean_ctor_set(v___x_1796_, 3, v___x_1916_);
lean_ctor_set(v___x_1796_, 2, v_v_1910_);
lean_ctor_set(v___x_1796_, 1, v_k_1909_);
lean_ctor_set(v___x_1796_, 0, v___x_1914_);
v___x_1920_ = v___x_1796_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1909_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1910_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_unsigned_to_nat(2u);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_r_1903_);
lean_ctor_set(v___x_1796_, 3, v_impl_1799_);
lean_ctor_set(v___x_1796_, 0, v___x_1932_);
v___x_1934_ = v___x_1796_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_impl_1799_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_r_1903_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1937_; 
lean_dec(v_v_1792_);
lean_dec(v_k_1791_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 2, v_v_1788_);
lean_ctor_set(v___x_1796_, 1, v_k_1787_);
v___x_1937_ = v___x_1796_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_size_1790_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_k_1787_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_v_1788_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_l_1793_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_r_1794_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
default: 
{
lean_object* v_impl_1939_; lean_object* v___x_1940_; 
lean_dec(v_size_1790_);
v_impl_1939_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1787_, v_v_1788_, v_r_1794_);
v___x_1940_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1793_) == 0)
{
lean_object* v_size_1941_; lean_object* v_size_1942_; lean_object* v_k_1943_; lean_object* v_v_1944_; lean_object* v_l_1945_; lean_object* v_r_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v_size_1941_ = lean_ctor_get(v_l_1793_, 0);
v_size_1942_ = lean_ctor_get(v_impl_1939_, 0);
lean_inc(v_size_1942_);
v_k_1943_ = lean_ctor_get(v_impl_1939_, 1);
lean_inc(v_k_1943_);
v_v_1944_ = lean_ctor_get(v_impl_1939_, 2);
lean_inc(v_v_1944_);
v_l_1945_ = lean_ctor_get(v_impl_1939_, 3);
lean_inc(v_l_1945_);
v_r_1946_ = lean_ctor_get(v_impl_1939_, 4);
lean_inc(v_r_1946_);
v___x_1947_ = lean_unsigned_to_nat(3u);
v___x_1948_ = lean_nat_mul(v___x_1947_, v_size_1941_);
v___x_1949_ = lean_nat_dec_lt(v___x_1948_, v_size_1942_);
lean_dec(v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
lean_dec(v_r_1946_);
lean_dec(v_l_1945_);
lean_dec(v_v_1944_);
lean_dec(v_k_1943_);
v___x_1950_ = lean_nat_add(v___x_1940_, v_size_1941_);
v___x_1951_ = lean_nat_add(v___x_1950_, v_size_1942_);
lean_dec(v_size_1942_);
lean_dec(v___x_1950_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_impl_1939_);
lean_ctor_set(v___x_1796_, 0, v___x_1951_);
v___x_1953_ = v___x_1796_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_l_1793_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_impl_1939_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
else
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2018_; 
v_isSharedCheck_2018_ = !lean_is_exclusive(v_impl_1939_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; 
v_unused_2019_ = lean_ctor_get(v_impl_1939_, 4);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_impl_1939_, 3);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_impl_1939_, 2);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_impl_1939_, 1);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_impl_1939_, 0);
lean_dec(v_unused_2023_);
v___x_1956_ = v_impl_1939_;
v_isShared_1957_ = v_isSharedCheck_2018_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v_impl_1939_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2018_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_size_1958_; lean_object* v_k_1959_; lean_object* v_v_1960_; lean_object* v_l_1961_; lean_object* v_r_1962_; lean_object* v_size_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_size_1958_ = lean_ctor_get(v_l_1945_, 0);
v_k_1959_ = lean_ctor_get(v_l_1945_, 1);
v_v_1960_ = lean_ctor_get(v_l_1945_, 2);
v_l_1961_ = lean_ctor_get(v_l_1945_, 3);
v_r_1962_ = lean_ctor_get(v_l_1945_, 4);
v_size_1963_ = lean_ctor_get(v_r_1946_, 0);
v___x_1964_ = lean_unsigned_to_nat(2u);
v___x_1965_ = lean_nat_mul(v___x_1964_, v_size_1963_);
v___x_1966_ = lean_nat_dec_lt(v_size_1958_, v___x_1965_);
lean_dec(v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1994_; 
lean_inc(v_r_1962_);
lean_inc(v_l_1961_);
lean_inc(v_v_1960_);
lean_inc(v_k_1959_);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_l_1945_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; lean_object* v_unused_1997_; lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1995_ = lean_ctor_get(v_l_1945_, 4);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_l_1945_, 3);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_l_1945_, 2);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_l_1945_, 1);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_l_1945_, 0);
lean_dec(v_unused_1999_);
v___x_1968_ = v_l_1945_;
v_isShared_1969_ = v_isSharedCheck_1994_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v_l_1945_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1994_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1984_; 
v___x_1970_ = lean_nat_add(v___x_1940_, v_size_1941_);
v___x_1971_ = lean_nat_add(v___x_1970_, v_size_1942_);
lean_dec(v_size_1942_);
if (lean_obj_tag(v_l_1961_) == 0)
{
lean_object* v_size_1992_; 
v_size_1992_ = lean_ctor_get(v_l_1961_, 0);
lean_inc(v_size_1992_);
v___y_1984_ = v_size_1992_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_unsigned_to_nat(0u);
v___y_1984_ = v___x_1993_;
goto v___jp_1983_;
}
v___jp_1972_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_nat_add(v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec(v___y_1974_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_r_1946_);
lean_ctor_set(v___x_1968_, 3, v_r_1962_);
lean_ctor_set(v___x_1968_, 2, v_v_1944_);
lean_ctor_set(v___x_1968_, 1, v_k_1943_);
lean_ctor_set(v___x_1968_, 0, v___x_1976_);
v___x_1978_ = v___x_1968_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_k_1943_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_v_1944_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_r_1962_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v_r_1946_);
v___x_1978_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1980_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 4, v___x_1978_);
lean_ctor_set(v___x_1956_, 3, v___y_1973_);
lean_ctor_set(v___x_1956_, 2, v_v_1960_);
lean_ctor_set(v___x_1956_, 1, v_k_1959_);
lean_ctor_set(v___x_1956_, 0, v___x_1971_);
v___x_1980_ = v___x_1956_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_k_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_v_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v___y_1973_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
v___jp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_nat_add(v___x_1970_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec(v___x_1970_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_l_1961_);
lean_ctor_set(v___x_1796_, 0, v___x_1985_);
v___x_1987_ = v___x_1796_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_l_1793_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_l_1961_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_nat_add(v___x_1940_, v_size_1963_);
if (lean_obj_tag(v_r_1962_) == 0)
{
lean_object* v_size_1989_; 
v_size_1989_ = lean_ctor_get(v_r_1962_, 0);
lean_inc(v_size_1989_);
v___y_1973_ = v___x_1987_;
v___y_1974_ = v___x_1988_;
v___y_1975_ = v_size_1989_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v___y_1973_ = v___x_1987_;
v___y_1974_ = v___x_1988_;
v___y_1975_ = v___x_1990_;
goto v___jp_1972_;
}
}
}
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
lean_del_object(v___x_1796_);
v___x_2000_ = lean_nat_add(v___x_1940_, v_size_1941_);
v___x_2001_ = lean_nat_add(v___x_2000_, v_size_1942_);
lean_dec(v_size_1942_);
v___x_2002_ = lean_nat_add(v___x_2000_, v_size_1958_);
lean_dec(v___x_2000_);
lean_inc_ref(v_l_1793_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 4, v_l_1945_);
lean_ctor_set(v___x_1956_, 3, v_l_1793_);
lean_ctor_set(v___x_1956_, 2, v_v_1792_);
lean_ctor_set(v___x_1956_, 1, v_k_1791_);
lean_ctor_set(v___x_1956_, 0, v___x_2002_);
v___x_2004_ = v___x_1956_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_l_1793_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_l_1945_);
v___x_2004_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_isSharedCheck_2011_ = !lean_is_exclusive(v_l_1793_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; lean_object* v_unused_2013_; lean_object* v_unused_2014_; lean_object* v_unused_2015_; lean_object* v_unused_2016_; 
v_unused_2012_ = lean_ctor_get(v_l_1793_, 4);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_l_1793_, 3);
lean_dec(v_unused_2013_);
v_unused_2014_ = lean_ctor_get(v_l_1793_, 2);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_l_1793_, 1);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_l_1793_, 0);
lean_dec(v_unused_2016_);
v___x_2006_ = v_l_1793_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v_l_1793_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 4, v_r_1946_);
lean_ctor_set(v___x_2006_, 3, v___x_2004_);
lean_ctor_set(v___x_2006_, 2, v_v_1944_);
lean_ctor_set(v___x_2006_, 1, v_k_1943_);
lean_ctor_set(v___x_2006_, 0, v___x_2001_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_k_1943_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_v_1944_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_r_1946_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2024_; 
v_l_2024_ = lean_ctor_get(v_impl_1939_, 3);
lean_inc(v_l_2024_);
if (lean_obj_tag(v_l_2024_) == 0)
{
lean_object* v_r_2025_; lean_object* v_k_2026_; lean_object* v_v_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2050_; 
v_r_2025_ = lean_ctor_get(v_impl_1939_, 4);
v_k_2026_ = lean_ctor_get(v_impl_1939_, 1);
v_v_2027_ = lean_ctor_get(v_impl_1939_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_impl_1939_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2051_ = lean_ctor_get(v_impl_1939_, 3);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_impl_1939_, 0);
lean_dec(v_unused_2052_);
v___x_2029_ = v_impl_1939_;
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_r_2025_);
lean_inc(v_v_2027_);
lean_inc(v_k_2026_);
lean_dec(v_impl_1939_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_k_2031_; lean_object* v_v_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2046_; 
v_k_2031_ = lean_ctor_get(v_l_2024_, 1);
v_v_2032_ = lean_ctor_get(v_l_2024_, 2);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_l_2024_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; 
v_unused_2047_ = lean_ctor_get(v_l_2024_, 4);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_l_2024_, 3);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_l_2024_, 0);
lean_dec(v_unused_2049_);
v___x_2034_ = v_l_2024_;
v_isShared_2035_ = v_isSharedCheck_2046_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_v_2032_);
lean_inc(v_k_2031_);
lean_dec(v_l_2024_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2046_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2025_, 2);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_r_2025_);
lean_ctor_set(v___x_2034_, 3, v_r_2025_);
lean_ctor_set(v___x_2034_, 2, v_v_1792_);
lean_ctor_set(v___x_2034_, 1, v_k_1791_);
lean_ctor_set(v___x_2034_, 0, v___x_1940_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_r_2025_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_r_2025_);
v___x_2038_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
lean_inc(v_r_2025_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 3, v_r_2025_);
lean_ctor_set(v___x_2029_, 0, v___x_1940_);
v___x_2040_ = v___x_2029_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_2026_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_2027_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_r_2025_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_r_2025_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v___x_2040_);
lean_ctor_set(v___x_1796_, 3, v___x_2038_);
lean_ctor_set(v___x_1796_, 2, v_v_2032_);
lean_ctor_set(v___x_1796_, 1, v_k_2031_);
lean_ctor_set(v___x_1796_, 0, v___x_2036_);
v___x_2042_ = v___x_1796_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
else
{
lean_object* v_r_2053_; 
v_r_2053_ = lean_ctor_get(v_impl_1939_, 4);
lean_inc(v_r_2053_);
if (lean_obj_tag(v_r_2053_) == 0)
{
lean_object* v_k_2054_; lean_object* v_v_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
v_k_2054_ = lean_ctor_get(v_impl_1939_, 1);
v_v_2055_ = lean_ctor_get(v_impl_1939_, 2);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_impl_1939_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; 
v_unused_2067_ = lean_ctor_get(v_impl_1939_, 4);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_impl_1939_, 3);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_impl_1939_, 0);
lean_dec(v_unused_2069_);
v___x_2057_ = v_impl_1939_;
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
lean_dec(v_impl_1939_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_unsigned_to_nat(3u);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 4, v_l_2024_);
lean_ctor_set(v___x_2057_, 2, v_v_1792_);
lean_ctor_set(v___x_2057_, 1, v_k_1791_);
lean_ctor_set(v___x_2057_, 0, v___x_1940_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_l_2024_);
lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_l_2024_);
v___x_2061_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_r_2053_);
lean_ctor_set(v___x_1796_, 3, v___x_2061_);
lean_ctor_set(v___x_1796_, 2, v_v_2055_);
lean_ctor_set(v___x_1796_, 1, v_k_2054_);
lean_ctor_set(v___x_1796_, 0, v___x_2059_);
v___x_2063_ = v___x_1796_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_r_2053_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(2u);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_impl_1939_);
lean_ctor_set(v___x_1796_, 3, v_r_2053_);
lean_ctor_set(v___x_1796_, 0, v___x_2070_);
v___x_2072_ = v___x_1796_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_r_2053_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_impl_1939_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
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
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_k_1787_);
lean_ctor_set(v___x_2076_, 2, v_v_1788_);
lean_ctor_set(v___x_2076_, 3, v_t_1789_);
lean_ctor_set(v___x_2076_, 4, v_t_1789_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_2077_, size_t v_sz_2078_, size_t v_i_2079_, lean_object* v_b_2080_){
_start:
{
lean_object* v___y_2083_; uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_lt(v_i_2079_, v_sz_2078_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_b_2080_);
return v___x_2088_;
}
else
{
lean_object* v_a_2089_; uint8_t v___x_2090_; 
v_a_2089_ = lean_array_uget_borrowed(v_as_2077_, v_i_2079_);
lean_inc(v_b_2080_);
lean_inc(v_a_2089_);
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_2089_, v_b_2080_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(0);
lean_inc(v_a_2089_);
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_2089_, v___x_2091_, v_b_2080_);
v___y_2083_ = v___x_2092_;
goto v___jp_2082_;
}
else
{
v___y_2083_ = v_b_2080_;
goto v___jp_2082_;
}
}
v___jp_2082_:
{
size_t v___x_2084_; size_t v___x_2085_; 
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_add(v_i_2079_, v___x_2084_);
v_i_2079_ = v___x_2085_;
v_b_2080_ = v___y_2083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_2093_, lean_object* v_sz_2094_, lean_object* v_i_2095_, lean_object* v_b_2096_, lean_object* v___y_2097_){
_start:
{
size_t v_sz_boxed_2098_; size_t v_i_boxed_2099_; lean_object* v_res_2100_; 
v_sz_boxed_2098_ = lean_unbox_usize(v_sz_2094_);
lean_dec(v_sz_2094_);
v_i_boxed_2099_ = lean_unbox_usize(v_i_2095_);
lean_dec(v_i_2095_);
v_res_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_2093_, v_sz_boxed_2098_, v_i_boxed_2099_, v_b_2096_);
lean_dec_ref(v_as_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v_set_2109_; size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
v_set_2109_ = lean_box(1);
v_sz_2110_ = lean_array_size(v_a_2108_);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_2108_, v_sz_2110_, v___x_2111_, v_set_2109_);
lean_dec(v_a_2108_);
return v___x_2112_;
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_a_2113_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2107_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2107_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_2128_, lean_object* v_k_2129_, lean_object* v_t_2130_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_2129_, v_t_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_2132_, lean_object* v_k_2133_, lean_object* v_t_2134_){
_start:
{
uint8_t v_res_2135_; lean_object* v_r_2136_; 
v_res_2135_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_2132_, v_k_2133_, v_t_2134_);
v_r_2136_ = lean_box(v_res_2135_);
return v_r_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_2137_, lean_object* v_k_2138_, lean_object* v_v_2139_, lean_object* v_t_2140_, lean_object* v_hl_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_2138_, v_v_2139_, v_t_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_2143_, size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_2143_, v_sz_2144_, v_i_2145_, v_b_2146_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_2153_, v_sz_boxed_2162_, v_i_boxed_2163_, v_b_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v_as_2153_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_2165_, lean_object* v_declName_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
uint8_t v___y_2173_; uint8_t v___y_2195_; lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Expr_getAppFn(v_e_2165_);
if (lean_obj_tag(v___x_2198_) == 4)
{
lean_object* v_declName_2199_; lean_object* v___x_2200_; 
v_declName_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_declName_2199_);
lean_dec_ref(v___x_2198_);
lean_inc(v_declName_2199_);
v___x_2200_ = lean_private_to_user_name(v_declName_2199_);
if (lean_obj_tag(v___x_2200_) == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = lean_name_eq(v_declName_2199_, v_declName_2166_);
lean_dec(v_declName_2199_);
v___y_2195_ = v___x_2201_;
goto v___jp_2194_;
}
else
{
lean_object* v_val_2202_; uint8_t v___x_2203_; 
lean_dec(v_declName_2199_);
v_val_2202_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_val_2202_);
lean_dec_ref(v___x_2200_);
v___x_2203_ = lean_name_eq(v_val_2202_, v_declName_2166_);
lean_dec(v_val_2202_);
v___y_2195_ = v___x_2203_;
goto v___jp_2194_;
}
}
else
{
uint8_t v___x_2204_; 
lean_dec_ref(v___x_2198_);
v___x_2204_ = 0;
v___y_2173_ = v___x_2204_;
goto v___jp_2172_;
}
v___jp_2172_:
{
lean_object* v___x_2174_; 
lean_inc(v_a_2170_);
lean_inc_ref(v_a_2169_);
lean_inc(v_a_2168_);
lean_inc_ref(v_a_2167_);
v___x_2174_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_2165_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2185_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_val_2179_; 
lean_del_object(v___x_2177_);
v_val_2179_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_val_2179_);
lean_dec_ref(v_a_2175_);
v_e_2165_ = v_val_2179_;
goto _start;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v_a_2175_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
v___x_2181_ = lean_box(v___y_2173_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2181_);
v___x_2183_ = v___x_2177_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
v_a_2186_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2174_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2174_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
v___jp_2194_:
{
if (v___y_2195_ == 0)
{
v___y_2173_ = v___y_2195_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec_ref(v_e_2165_);
v___x_2196_ = lean_box(v___y_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_2205_, lean_object* v_declName_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_2205_, v_declName_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_declName_2206_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_2213_, lean_object* v_b_2214_, lean_object* v_c_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_apply_7(v_k_2213_, v_b_2214_, v_c_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, lean_box(0));
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_2222_, lean_object* v_b_2223_, lean_object* v_c_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_2222_, v_b_2223_, v_c_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_2231_, lean_object* v_k_2232_, uint8_t v_cleanupAnnotations_2233_, uint8_t v_whnfType_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_2241_; 
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2240_, 0, v_k_2232_);
v___x_2241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2231_, v___f_2240_, v_cleanupAnnotations_2233_, v_whnfType_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2241_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2241_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_2258_, lean_object* v_k_2259_, lean_object* v_cleanupAnnotations_2260_, lean_object* v_whnfType_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2267_; uint8_t v_whnfType_boxed_2268_; lean_object* v_res_2269_; 
v_cleanupAnnotations_boxed_2267_ = lean_unbox(v_cleanupAnnotations_2260_);
v_whnfType_boxed_2268_ = lean_unbox(v_whnfType_2261_);
v_res_2269_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_2258_, v_k_2259_, v_cleanupAnnotations_boxed_2267_, v_whnfType_boxed_2268_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_2270_, lean_object* v_type_2271_, lean_object* v_k_2272_, uint8_t v_cleanupAnnotations_2273_, uint8_t v_whnfType_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_2271_, v_k_2272_, v_cleanupAnnotations_2273_, v_whnfType_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_2281_, lean_object* v_type_2282_, lean_object* v_k_2283_, lean_object* v_cleanupAnnotations_2284_, lean_object* v_whnfType_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2291_; uint8_t v_whnfType_boxed_2292_; lean_object* v_res_2293_; 
v_cleanupAnnotations_boxed_2291_ = lean_unbox(v_cleanupAnnotations_2284_);
v_whnfType_boxed_2292_ = lean_unbox(v_whnfType_2285_);
v_res_2293_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_2281_, v_type_2282_, v_k_2283_, v_cleanupAnnotations_boxed_2291_, v_whnfType_boxed_2292_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_2297_, lean_object* v_as_2298_, size_t v_sz_2299_, size_t v_i_2300_, lean_object* v_b_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v___x_2307_; 
v___x_2307_ = lean_usize_dec_lt(v_i_2300_, v_sz_2299_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; 
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_b_2301_);
return v___x_2308_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec_ref(v_b_2301_);
v_a_2309_ = lean_array_uget_borrowed(v_as_2298_, v_i_2300_);
v___x_2310_ = l_Lean_Expr_fvarId_x21(v_a_2309_);
lean_inc_ref(v___y_2302_);
v___x_2311_ = l_Lean_FVarId_getDecl___redArg(v___x_2310_, v___y_2302_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = l_Lean_LocalDecl_type(v_a_2312_);
lean_dec(v_a_2312_);
v___x_2314_ = l_Lean_Expr_consumeMData(v___x_2313_);
lean_dec_ref(v___x_2313_);
lean_inc(v___y_2305_);
lean_inc_ref(v___y_2304_);
lean_inc(v___y_2303_);
lean_inc_ref(v___y_2302_);
v___x_2315_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_2314_, v_typeName_2297_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2331_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2331_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2331_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_unbox(v_a_2316_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; 
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
v___x_2322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2300_, v___x_2323_);
v_i_2300_ = v___x_2324_;
v_b_2301_ = v___x_2322_;
goto _start;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_a_2316_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2320_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2327_);
v___x_2329_ = v___x_2318_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
v_a_2332_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2315_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2315_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
v_a_2340_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2311_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2311_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_2348_, lean_object* v_as_2349_, lean_object* v_sz_2350_, lean_object* v_i_2351_, lean_object* v_b_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
size_t v_sz_boxed_2358_; size_t v_i_boxed_2359_; lean_object* v_res_2360_; 
v_sz_boxed_2358_ = lean_unbox_usize(v_sz_2350_);
lean_dec(v_sz_2350_);
v_i_boxed_2359_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_res_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_2348_, v_as_2349_, v_sz_boxed_2358_, v_i_boxed_2359_, v_b_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec_ref(v_as_2349_);
lean_dec(v_typeName_2348_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_2361_, lean_object* v_xs_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; size_t v_sz_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_2370_ = lean_array_size(v_xs_2362_);
v___x_2371_ = ((size_t)0ULL);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_2361_, v_xs_2362_, v_sz_2370_, v___x_2371_, v___x_2369_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2387_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2387_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2387_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v_fst_2377_; 
v_fst_2377_ = lean_ctor_get(v_a_2373_, 0);
lean_inc(v_fst_2377_);
lean_dec(v_a_2373_);
if (lean_obj_tag(v_fst_2377_) == 0)
{
uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2378_ = 0;
v___x_2379_ = lean_box(v___x_2378_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2379_);
v___x_2381_ = v___x_2375_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
else
{
lean_object* v_val_2383_; lean_object* v___x_2385_; 
v_val_2383_ = lean_ctor_get(v_fst_2377_, 0);
lean_inc(v_val_2383_);
lean_dec_ref(v_fst_2377_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v_val_2383_);
v___x_2385_ = v___x_2375_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_val_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
v_a_2388_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2372_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2372_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_2396_, lean_object* v_xs_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_2396_, v_xs_2397_, v_x_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v_x_2398_);
lean_dec_ref(v_xs_2397_);
lean_dec(v_typeName_2396_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_2405_, lean_object* v_info_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___f_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___f_2412_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2412_, 0, v_typeName_2405_);
v___x_2413_ = l_Lean_ConstantInfo_type(v_info_2406_);
v___x_2414_ = 0;
v___x_2415_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_2413_, v___f_2412_, v___x_2414_, v___x_2414_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_2416_, lean_object* v_info_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2416_, v_info_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec_ref(v_info_2417_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = l_Lean_Expr_hasMVar(v_e_2424_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_e_2424_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; lean_object* v_mctx_2430_; lean_object* v___x_2431_; lean_object* v_fst_2432_; lean_object* v_snd_2433_; lean_object* v___x_2434_; lean_object* v_cache_2435_; lean_object* v_zetaDeltaFVarIds_2436_; lean_object* v_postponed_2437_; lean_object* v_diag_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2447_; 
v___x_2429_ = lean_st_ref_get(v___y_2425_);
v_mctx_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_ref(v_mctx_2430_);
lean_dec(v___x_2429_);
v___x_2431_ = l_Lean_instantiateMVarsCore(v_mctx_2430_, v_e_2424_);
v_fst_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_fst_2432_);
v_snd_2433_ = lean_ctor_get(v___x_2431_, 1);
lean_inc(v_snd_2433_);
lean_dec_ref(v___x_2431_);
v___x_2434_ = lean_st_ref_take(v___y_2425_);
v_cache_2435_ = lean_ctor_get(v___x_2434_, 1);
v_zetaDeltaFVarIds_2436_ = lean_ctor_get(v___x_2434_, 2);
v_postponed_2437_ = lean_ctor_get(v___x_2434_, 3);
v_diag_2438_ = lean_ctor_get(v___x_2434_, 4);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2434_, 0);
lean_dec(v_unused_2448_);
v___x_2440_ = v___x_2434_;
v_isShared_2441_ = v_isSharedCheck_2447_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_diag_2438_);
lean_inc(v_postponed_2437_);
lean_inc(v_zetaDeltaFVarIds_2436_);
lean_inc(v_cache_2435_);
lean_dec(v___x_2434_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2447_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_snd_2433_);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_snd_2433_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_cache_2435_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_zetaDeltaFVarIds_2436_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_postponed_2437_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_diag_2438_);
v___x_2443_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_st_ref_set(v___y_2425_, v___x_2443_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_fst_2432_);
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object* v_e_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2449_, v___y_2450_);
lean_dec(v___y_2450_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object* v_e_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2453_, v___y_2455_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object* v_e_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object* v_type_2467_, lean_object* v_k_2468_, uint8_t v_cleanupAnnotations_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___f_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2475_, 0, v_k_2468_);
v___x_2476_ = 0;
v___x_2477_ = lean_box(0);
v___x_2478_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2476_, v___x_2477_, v_type_2467_, v___f_2475_, v_cleanupAnnotations_2469_, v___x_2476_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2478_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2478_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object* v_type_2495_, lean_object* v_k_2496_, lean_object* v_cleanupAnnotations_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2503_; lean_object* v_res_2504_; 
v_cleanupAnnotations_boxed_2503_ = lean_unbox(v_cleanupAnnotations_2497_);
v_res_2504_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2495_, v_k_2496_, v_cleanupAnnotations_boxed_2503_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object* v_00_u03b1_2505_, lean_object* v_type_2506_, lean_object* v_k_2507_, uint8_t v_cleanupAnnotations_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2506_, v_k_2507_, v_cleanupAnnotations_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object* v_00_u03b1_2515_, lean_object* v_type_2516_, lean_object* v_k_2517_, lean_object* v_cleanupAnnotations_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2524_; lean_object* v_res_2525_; 
v_cleanupAnnotations_boxed_2524_ = lean_unbox(v_cleanupAnnotations_2518_);
v_res_2525_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(v_00_u03b1_2515_, v_type_2516_, v_k_2517_, v_cleanupAnnotations_boxed_2524_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object* v_typeNameSet_2526_, lean_object* v_x_2527_, lean_object* v_type_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2526_, v_x_2527_, v_type_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v_x_2527_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object* v_typeNameSet_2535_, lean_object* v_type_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___f_2542_; lean_object* v_a_2544_; lean_object* v___y_2594_; lean_object* v___x_2604_; 
lean_inc(v_typeNameSet_2535_);
v___f_2542_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2542_, 0, v_typeNameSet_2535_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc_ref(v_type_2536_);
v___x_2604_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(v_type_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_dec_ref(v_type_2536_);
v___y_2594_ = v___x_2604_;
goto v___jp_2593_;
}
else
{
lean_object* v_a_2605_; uint8_t v___y_2607_; uint8_t v___x_2608_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
v___x_2608_ = l_Lean_Exception_isInterrupt(v_a_2605_);
if (v___x_2608_ == 0)
{
uint8_t v___x_2609_; 
v___x_2609_ = l_Lean_Exception_isRuntime(v_a_2605_);
v___y_2607_ = v___x_2609_;
goto v___jp_2606_;
}
else
{
lean_dec(v_a_2605_);
v___y_2607_ = v___x_2608_;
goto v___jp_2606_;
}
v___jp_2606_:
{
if (v___y_2607_ == 0)
{
lean_dec_ref(v___x_2604_);
v_a_2544_ = v_type_2536_;
goto v___jp_2543_;
}
else
{
lean_dec_ref(v_type_2536_);
v___y_2594_ = v___x_2604_;
goto v___jp_2593_;
}
}
}
v___jp_2543_:
{
uint8_t v___x_2545_; 
v___x_2545_ = l_Lean_Expr_isForall(v_a_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
lean_dec_ref(v___f_2542_);
v___x_2546_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_a_2544_, v_a_2538_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2582_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2582_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2582_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Expr_getAppFn(v_a_2547_);
if (lean_obj_tag(v___x_2551_) == 4)
{
lean_object* v_declName_2552_; uint8_t v___x_2553_; 
v_declName_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_declName_2552_);
lean_dec_ref(v___x_2551_);
lean_inc(v_typeNameSet_2535_);
v___x_2553_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_declName_2552_, v_typeNameSet_2535_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_del_object(v___x_2549_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
v___x_2554_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_a_2547_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2565_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
if (lean_obj_tag(v_a_2555_) == 1)
{
lean_object* v_val_2559_; 
lean_del_object(v___x_2557_);
v_val_2559_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_val_2559_);
lean_dec_ref(v_a_2555_);
v_type_2536_ = v_val_2559_;
goto _start;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_dec(v_a_2555_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_typeNameSet_2535_);
v___x_2561_ = lean_box(v___x_2553_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2561_);
v___x_2563_ = v___x_2557_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_typeNameSet_2535_);
v_a_2566_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2554_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2554_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_dec(v_a_2547_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_typeNameSet_2535_);
v___x_2574_ = lean_box(v___x_2553_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2574_);
v___x_2576_ = v___x_2549_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
lean_dec_ref(v___x_2551_);
lean_dec(v_a_2547_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_typeNameSet_2535_);
v___x_2578_ = lean_box(v___x_2545_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2578_);
v___x_2580_ = v___x_2549_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_typeNameSet_2535_);
v_a_2583_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2546_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2546_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
uint8_t v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_typeNameSet_2535_);
v___x_2591_ = 0;
v___x_2592_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_a_2544_, v___f_2542_, v___x_2591_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
return v___x_2592_;
}
}
v___jp_2593_:
{
if (lean_obj_tag(v___y_2594_) == 0)
{
lean_object* v_a_2595_; 
v_a_2595_ = lean_ctor_get(v___y_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref(v___y_2594_);
v_a_2544_ = v_a_2595_;
goto v___jp_2543_;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec_ref(v___f_2542_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_typeNameSet_2535_);
v_a_2596_ = lean_ctor_get(v___y_2594_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___y_2594_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___y_2594_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___y_2594_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object* v_typeNameSet_2610_, lean_object* v_x_2611_, lean_object* v_type_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2610_, v_type_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object* v_typeNameSet_2619_, lean_object* v_type_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2619_, v_type_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* v_typeNameSet_2627_, lean_object* v_info_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = l_Lean_ConstantInfo_type(v_info_2628_);
v___x_2635_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2627_, v___x_2634_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* v_typeNameSet_2636_, lean_object* v_info_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2636_, v_info_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec_ref(v_info_2637_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* v_matchAlias_2644_, lean_object* v_addAlias_2645_, lean_object* v_alias_2646_, lean_object* v_declNames_2647_, lean_object* v_ns_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
lean_inc_ref(v_matchAlias_2644_);
lean_inc(v_alias_2646_);
lean_inc(v_ns_2648_);
v___x_2657_ = lean_apply_2(v_matchAlias_2644_, v_ns_2648_, v_alias_2646_);
v___x_2658_ = lean_unbox(v___x_2657_);
if (v___x_2658_ == 0)
{
if (lean_obj_tag(v_ns_2648_) == 1)
{
lean_object* v_pre_2659_; 
v_pre_2659_ = lean_ctor_get(v_ns_2648_, 0);
lean_inc(v_pre_2659_);
lean_dec_ref(v_ns_2648_);
v_ns_2648_ = v_pre_2659_;
goto _start;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_ns_2648_);
lean_dec(v_declNames_2647_);
lean_dec(v_alias_2646_);
lean_dec_ref(v_addAlias_2645_);
lean_dec_ref(v_matchAlias_2644_);
v___x_2661_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
}
else
{
lean_object* v___x_2663_; 
lean_dec(v_ns_2648_);
lean_dec_ref(v_matchAlias_2644_);
v___x_2663_ = lean_apply_10(v_addAlias_2645_, v_alias_2646_, v_declNames_2647_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, lean_box(0));
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object* v_matchAlias_2664_, lean_object* v_addAlias_2665_, lean_object* v_alias_2666_, lean_object* v_declNames_2667_, lean_object* v_ns_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2664_, v_addAlias_2665_, v_alias_2666_, v_declNames_2667_, v_ns_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object* v_a_2680_){
_start:
{
uint8_t v___x_2682_; 
v___x_2682_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_2680_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0));
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object* v_a_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2687_);
lean_dec_ref(v_a_2687_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object* v_a_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2690_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object* v_a_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_a_2697_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object* v_ctx_2704_, lean_object* v_id_2705_, uint8_t v_danglingDot_2706_, lean_object* v_declName_2707_, lean_object* v_decl_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v_declName_2707_);
v___x_2717_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_2704_, v_declName_2707_, v_id_2705_, v_danglingDot_2706_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2770_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2770_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2770_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
if (lean_obj_tag(v_a_2718_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_decl_2708_);
lean_dec(v_declName_2707_);
v_a_2722_ = lean_ctor_get(v_a_2718_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_a_2718_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2724_ = v_a_2718_;
v_isShared_2725_ = v_isSharedCheck_2732_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v_a_2718_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2732_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2729_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2727_);
v___x_2729_ = v___x_2720_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v_a_2733_; 
v_a_2733_ = lean_ctor_get(v_a_2718_, 0);
lean_inc(v_a_2733_);
lean_dec_ref(v_a_2718_);
if (lean_obj_tag(v_a_2733_) == 1)
{
lean_object* v_val_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2765_; 
lean_del_object(v___x_2720_);
v_val_2734_ = lean_ctor_get(v_a_2733_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_a_2733_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2736_ = v_a_2733_;
v_isShared_2737_ = v_isSharedCheck_2765_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_val_2734_);
lean_dec(v_a_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2765_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_kind_2738_; lean_object* v_tags_2739_; lean_object* v___x_2740_; 
v_kind_2738_ = lean_ctor_get(v_decl_2708_, 1);
lean_inc_ref(v_kind_2738_);
v_tags_2739_ = lean_ctor_get(v_decl_2708_, 2);
lean_inc_ref(v_tags_2739_);
lean_dec_ref(v_decl_2708_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
v___x_2740_ = lean_apply_5(v_kind_2738_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, lean_box(0));
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = lean_apply_5(v_tags_2739_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, lean_box(0));
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 0);
lean_ctor_set(v___x_2736_, 0, v_declName_2707_);
v___x_2745_ = v___x_2736_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_declName_2707_);
v___x_2745_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
uint8_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_unbox(v_a_2741_);
lean_dec(v_a_2741_);
v___x_2747_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_2734_, v___x_2745_, v___x_2746_, v_a_2743_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
return v___x_2747_;
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2741_);
lean_del_object(v___x_2736_);
lean_dec(v_val_2734_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_declName_2707_);
v_a_2749_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2742_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2742_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_tags_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_val_2734_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_declName_2707_);
v_a_2757_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2740_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2740_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_a_2733_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_decl_2708_);
lean_dec(v_declName_2707_);
v___x_2766_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2766_);
v___x_2768_ = v___x_2720_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_decl_2708_);
lean_dec(v_declName_2707_);
v_a_2771_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2717_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2717_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object* v_ctx_2779_, lean_object* v_id_2780_, lean_object* v_danglingDot_2781_, lean_object* v_declName_2782_, lean_object* v_decl_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v_danglingDot_boxed_2792_; lean_object* v_res_2793_; 
v_danglingDot_boxed_2792_ = lean_unbox(v_danglingDot_2781_);
v_res_2793_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2779_, v_id_2780_, v_danglingDot_boxed_2792_, v_declName_2782_, v_decl_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object* v_id_2794_, uint8_t v_danglingDot_2795_, lean_object* v_ns_2796_, lean_object* v_alias_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = l_Lean_Name_isPrefixOf(v_ns_2796_, v_alias_2797_);
if (v___x_2798_ == 0)
{
lean_dec(v_alias_2797_);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = l_Lean_Name_replacePrefix(v_alias_2797_, v_ns_2796_, v___x_2799_);
v___x_2801_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_2794_, v___x_2800_, v_danglingDot_2795_);
lean_dec(v___x_2800_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object* v_id_2802_, lean_object* v_danglingDot_2803_, lean_object* v_ns_2804_, lean_object* v_alias_2805_){
_start:
{
uint8_t v_danglingDot_boxed_2806_; uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_danglingDot_boxed_2806_ = lean_unbox(v_danglingDot_2803_);
v_res_2807_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2802_, v_danglingDot_boxed_2806_, v_ns_2804_, v_alias_2805_);
lean_dec(v_ns_2804_);
lean_dec(v_id_2802_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object* v_a_2809_, lean_object* v___x_2810_, lean_object* v_alias_2811_, lean_object* v_as_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
if (lean_obj_tag(v_as_2812_) == 0)
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec_ref(v___x_2810_);
v___x_2820_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
return v___x_2821_;
}
else
{
lean_object* v_head_2822_; lean_object* v_tail_2823_; uint8_t v___x_2824_; 
v_head_2822_ = lean_ctor_get(v_as_2812_, 0);
lean_inc(v_head_2822_);
v_tail_2823_ = lean_ctor_get(v_as_2812_, 1);
lean_inc(v_tail_2823_);
lean_dec_ref(v_as_2812_);
lean_inc(v_head_2822_);
lean_inc_ref(v___x_2810_);
v___x_2824_ = l_Lean_Server_Completion_allowCompletion(v_a_2809_, v___x_2810_, v_head_2822_);
if (v___x_2824_ == 0)
{
lean_dec(v_head_2822_);
v_as_2812_ = v_tail_2823_;
goto _start;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_Name_getString_x21(v_alias_2811_);
v___x_2827_ = lean_box(0);
v___x_2828_ = l_Lean_Name_str___override(v___x_2827_, v___x_2826_);
lean_inc(v___y_2818_);
lean_inc_ref(v___y_2817_);
lean_inc(v___y_2816_);
lean_inc_ref(v___y_2815_);
v___x_2829_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_2828_, v_head_2822_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_dec_ref(v___x_2829_);
v_as_2812_ = v_tail_2823_;
goto _start;
}
else
{
lean_dec(v_tail_2823_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec_ref(v___x_2810_);
return v___x_2829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object* v_a_2831_, lean_object* v___x_2832_, lean_object* v_alias_2833_, lean_object* v_as_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2831_, v___x_2832_, v_alias_2833_, v_as_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v_alias_2833_);
lean_dec_ref(v_a_2831_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object* v_a_2843_, lean_object* v_env_2844_, lean_object* v_alias_2845_, lean_object* v_declNames_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2843_, v_env_2844_, v_alias_2845_, v_declNames_2846_, v___y_2847_, v___y_2848_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object* v_a_2856_, lean_object* v_env_2857_, lean_object* v_alias_2858_, lean_object* v_declNames_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2856_, v_env_2857_, v_alias_2858_, v_declNames_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v_alias_2858_);
lean_dec_ref(v_a_2856_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object* v___f_2869_, lean_object* v___f_2870_, lean_object* v_currNamespace_2871_, lean_object* v_alias_2872_, lean_object* v_declNames_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v___f_2869_, v___f_2870_, v_alias_2872_, v_declNames_2873_, v_currNamespace_2871_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object* v___f_2883_, lean_object* v___f_2884_, lean_object* v_currNamespace_2885_, lean_object* v_alias_2886_, lean_object* v_declNames_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2883_, v___f_2884_, v_currNamespace_2885_, v_alias_2886_, v_declNames_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object* v_f_2897_, lean_object* v_decl_2898_, lean_object* v_ci_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___y_2910_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2948_ = lean_unsigned_to_nat(1u);
v___x_2949_ = lean_nat_add(v___y_2900_, v___x_2948_);
v___x_2950_ = lean_unsigned_to_nat(10000u);
v___x_2951_ = lean_nat_dec_le(v___x_2950_, v___x_2949_);
if (v___x_2951_ == 0)
{
v___y_2910_ = v___x_2949_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v___x_2949_);
v___x_2952_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_2903_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2969_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2969_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
if (lean_obj_tag(v_a_2953_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec_ref(v_ci_2899_);
lean_dec(v_decl_2898_);
lean_dec_ref(v_f_2897_);
v_a_2957_ = lean_ctor_get(v_a_2953_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2959_ = v_a_2953_;
v_isShared_2960_ = v_isSharedCheck_2967_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v_a_2953_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2967_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2964_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2962_);
v___x_2964_ = v___x_2955_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_object* v___x_2968_; 
lean_dec_ref(v_a_2953_);
lean_del_object(v___x_2955_);
v___x_2968_ = lean_unsigned_to_nat(0u);
v___y_2910_ = v___x_2968_;
goto v___jp_2909_;
}
}
}
v___jp_2909_:
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_apply_10(v_f_2897_, v_decl_2898_, v_ci_2899_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, lean_box(0));
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2939_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2939_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2939_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
if (lean_obj_tag(v_a_2912_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v___y_2910_);
v_a_2916_ = lean_ctor_get(v_a_2912_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2912_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2918_ = v_a_2912_;
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v_a_2912_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2923_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2921_);
v___x_2923_ = v___x_2914_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2938_; 
v_a_2927_ = lean_ctor_get(v_a_2912_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_a_2912_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2929_ = v_a_2912_;
v_isShared_2930_ = v_isSharedCheck_2938_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v_a_2912_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2938_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v_a_2927_);
lean_ctor_set(v___x_2931_, 1, v___y_2910_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2931_);
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2935_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2933_);
v___x_2935_ = v___x_2914_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v___y_2910_);
v_a_2940_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2911_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2911_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object* v_f_2970_, lean_object* v_decl_2971_, lean_object* v_ci_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2970_, v_decl_2971_, v_ci_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2973_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg(lean_object* v_f_2983_, lean_object* v_keys_2984_, lean_object* v_vals_2985_, lean_object* v_i_2986_, lean_object* v_acc_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = lean_array_get_size(v_keys_2984_);
v___x_2998_ = lean_nat_dec_lt(v_i_2986_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v_i_2986_);
lean_dec_ref(v_f_2983_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_acc_2987_);
lean_ctor_set(v___x_2999_, 1, v___y_2988_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
else
{
lean_object* v_k_3002_; lean_object* v_v_3003_; lean_object* v___x_3004_; 
v_k_3002_ = lean_array_fget_borrowed(v_keys_2984_, v_i_2986_);
v_v_3003_ = lean_array_fget_borrowed(v_vals_2985_, v_i_2986_);
lean_inc_ref(v_f_2983_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc(v___y_2993_);
lean_inc_ref(v___y_2992_);
lean_inc_ref(v___y_2991_);
lean_inc(v___y_2990_);
lean_inc_ref(v___y_2989_);
lean_inc(v_v_3003_);
lean_inc(v_k_3002_);
v___x_3004_ = lean_apply_12(v_f_2983_, v_acc_2987_, v_k_3002_, v_v_3003_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, lean_box(0));
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
if (lean_obj_tag(v_a_3005_) == 0)
{
lean_dec_ref(v_a_3005_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v_i_2986_);
lean_dec_ref(v_f_2983_);
return v___x_3004_;
}
else
{
lean_object* v_a_3006_; lean_object* v_fst_3007_; lean_object* v_snd_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref(v___x_3004_);
v_a_3006_ = lean_ctor_get(v_a_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v_a_3005_);
v_fst_3007_ = lean_ctor_get(v_a_3006_, 0);
lean_inc(v_fst_3007_);
v_snd_3008_ = lean_ctor_get(v_a_3006_, 1);
lean_inc(v_snd_3008_);
lean_dec(v_a_3006_);
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_nat_add(v_i_2986_, v___x_3009_);
lean_dec(v_i_2986_);
v_i_2986_ = v___x_3010_;
v_acc_2987_ = v_fst_3007_;
v___y_2988_ = v_snd_3008_;
goto _start;
}
}
else
{
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v_i_2986_);
lean_dec_ref(v_f_2983_);
return v___x_3004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg___boxed(lean_object* v_f_3012_, lean_object* v_keys_3013_, lean_object* v_vals_3014_, lean_object* v_i_3015_, lean_object* v_acc_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg(v_f_3012_, v_keys_3013_, v_vals_3014_, v_i_3015_, v_acc_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec_ref(v_vals_3014_);
lean_dec_ref(v_keys_3013_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(lean_object* v_f_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
if (lean_obj_tag(v_x_3028_) == 0)
{
lean_object* v_es_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3063_; 
v_es_3039_ = lean_ctor_get(v_x_3028_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_x_3028_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3041_ = v_x_3028_;
v_isShared_3042_ = v_isSharedCheck_3063_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_es_3039_);
lean_dec(v_x_3028_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3063_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_array_get_size(v_es_3039_);
v___x_3045_ = lean_nat_dec_lt(v___x_3043_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_dec_ref(v_es_3039_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v_f_3027_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v_x_3029_);
lean_ctor_set(v___x_3046_, 1, v___y_3030_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 1);
lean_ctor_set(v___x_3041_, 0, v___x_3046_);
v___x_3048_ = v___x_3041_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
else
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_le(v___x_3044_, v___x_3044_);
if (v___x_3051_ == 0)
{
if (v___x_3045_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_dec_ref(v_es_3039_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v_f_3027_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_x_3029_);
lean_ctor_set(v___x_3052_, 1, v___y_3030_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 1);
lean_ctor_set(v___x_3041_, 0, v___x_3052_);
v___x_3054_ = v___x_3041_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
lean_del_object(v___x_3041_);
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___x_3044_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg(v_f_3027_, v_es_3039_, v___x_3057_, v___x_3058_, v_x_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec_ref(v_es_3039_);
return v___x_3059_;
}
}
else
{
size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; 
lean_del_object(v___x_3041_);
v___x_3060_ = ((size_t)0ULL);
v___x_3061_ = lean_usize_of_nat(v___x_3044_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg(v_f_3027_, v_es_3039_, v___x_3060_, v___x_3061_, v_x_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec_ref(v_es_3039_);
return v___x_3062_;
}
}
}
}
else
{
lean_object* v_ks_3064_; lean_object* v_vs_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_ks_3064_ = lean_ctor_get(v_x_3028_, 0);
lean_inc_ref(v_ks_3064_);
v_vs_3065_ = lean_ctor_get(v_x_3028_, 1);
lean_inc_ref(v_vs_3065_);
lean_dec_ref(v_x_3028_);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg(v_f_3027_, v_ks_3064_, v_vs_3065_, v___x_3066_, v_x_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec_ref(v_vs_3065_);
lean_dec_ref(v_ks_3064_);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg(lean_object* v_f_3068_, lean_object* v_as_3069_, size_t v_i_3070_, size_t v_stop_3071_, lean_object* v_b_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_fst_3083_; lean_object* v_snd_3084_; lean_object* v___y_3089_; uint8_t v___x_3094_; 
v___x_3094_ = lean_usize_dec_eq(v_i_3070_, v_stop_3071_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_array_uget_borrowed(v_as_3069_, v_i_3070_);
switch(lean_obj_tag(v___x_3095_))
{
case 0:
{
lean_object* v_key_3096_; lean_object* v_val_3097_; lean_object* v___x_3098_; 
v_key_3096_ = lean_ctor_get(v___x_3095_, 0);
v_val_3097_ = lean_ctor_get(v___x_3095_, 1);
lean_inc_ref(v_f_3068_);
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v_val_3097_);
lean_inc(v_key_3096_);
v___x_3098_ = lean_apply_12(v_f_3068_, v_b_3072_, v_key_3096_, v_val_3097_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, lean_box(0));
v___y_3089_ = v___x_3098_;
goto v___jp_3088_;
}
case 1:
{
lean_object* v_node_3099_; lean_object* v___x_3100_; 
v_node_3099_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v_node_3099_);
lean_inc_ref(v_f_3068_);
v___x_3100_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(v_f_3068_, v_node_3099_, v_b_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
v___y_3089_ = v___x_3100_;
goto v___jp_3088_;
}
default: 
{
v_fst_3083_ = v_b_3072_;
v_snd_3084_ = v___y_3073_;
goto v___jp_3082_;
}
}
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v_f_3068_);
v___x_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3101_, 0, v_b_3072_);
lean_ctor_set(v___x_3101_, 1, v___y_3073_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
v___jp_3082_:
{
size_t v___x_3085_; size_t v___x_3086_; 
v___x_3085_ = ((size_t)1ULL);
v___x_3086_ = lean_usize_add(v_i_3070_, v___x_3085_);
v_i_3070_ = v___x_3086_;
v_b_3072_ = v_fst_3083_;
v___y_3073_ = v_snd_3084_;
goto _start;
}
v___jp_3088_:
{
if (lean_obj_tag(v___y_3089_) == 0)
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v___y_3089_, 0);
if (lean_obj_tag(v_a_3090_) == 0)
{
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v_f_3068_);
return v___y_3089_;
}
else
{
lean_object* v_a_3091_; lean_object* v_fst_3092_; lean_object* v_snd_3093_; 
lean_inc_ref(v_a_3090_);
lean_dec_ref(v___y_3089_);
v_a_3091_ = lean_ctor_get(v_a_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v_a_3090_);
v_fst_3092_ = lean_ctor_get(v_a_3091_, 0);
lean_inc(v_fst_3092_);
v_snd_3093_ = lean_ctor_get(v_a_3091_, 1);
lean_inc(v_snd_3093_);
lean_dec(v_a_3091_);
v_fst_3083_ = v_fst_3092_;
v_snd_3084_ = v_snd_3093_;
goto v___jp_3082_;
}
}
else
{
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v_f_3068_);
return v___y_3089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_f_3104_, lean_object* v_as_3105_, lean_object* v_i_3106_, lean_object* v_stop_3107_, lean_object* v_b_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
size_t v_i_boxed_3118_; size_t v_stop_boxed_3119_; lean_object* v_res_3120_; 
v_i_boxed_3118_ = lean_unbox_usize(v_i_3106_);
lean_dec(v_i_3106_);
v_stop_boxed_3119_ = lean_unbox_usize(v_stop_3107_);
lean_dec(v_stop_3107_);
v_res_3120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg(v_f_3104_, v_as_3105_, v_i_boxed_3118_, v_stop_boxed_3119_, v_b_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec_ref(v_as_3105_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_f_3121_, lean_object* v_x_3122_, lean_object* v_x_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(v_f_3121_, v_x_3122_, v_x_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_f_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_apply_11(v_f_3134_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, lean_box(0));
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_f_3148_, lean_object* v_x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_3148_, v_x_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_map_3162_, lean_object* v_f_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___f_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___f_3173_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3173_, 0, v_f_3163_);
v___x_3174_ = lean_box(0);
v___x_3175_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(v___f_3173_, v_map_3162_, v___x_3174_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_map_3176_, lean_object* v_f_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3176_, v_f_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object* v_f_3188_, lean_object* v_x_3189_, lean_object* v_x_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec_ref(v_f_3188_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_x_3189_);
lean_ctor_set(v___x_3200_, 1, v___y_3191_);
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
else
{
lean_object* v_key_3203_; lean_object* v_value_3204_; lean_object* v_tail_3205_; lean_object* v___x_3206_; 
v_key_3203_ = lean_ctor_get(v_x_3190_, 0);
lean_inc(v_key_3203_);
v_value_3204_ = lean_ctor_get(v_x_3190_, 1);
lean_inc(v_value_3204_);
v_tail_3205_ = lean_ctor_get(v_x_3190_, 2);
lean_inc(v_tail_3205_);
lean_dec_ref(v_x_3190_);
lean_inc_ref(v_f_3188_);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
v___x_3206_ = lean_apply_11(v_f_3188_, v_key_3203_, v_value_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, lean_box(0));
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
if (lean_obj_tag(v_a_3207_) == 0)
{
lean_dec_ref(v_a_3207_);
lean_dec(v_tail_3205_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec_ref(v_f_3188_);
return v___x_3206_;
}
else
{
lean_object* v_a_3208_; lean_object* v_fst_3209_; lean_object* v_snd_3210_; 
lean_dec_ref(v___x_3206_);
v_a_3208_ = lean_ctor_get(v_a_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v_a_3207_);
v_fst_3209_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_fst_3209_);
v_snd_3210_ = lean_ctor_get(v_a_3208_, 1);
lean_inc(v_snd_3210_);
lean_dec(v_a_3208_);
v_x_3189_ = v_fst_3209_;
v_x_3190_ = v_tail_3205_;
v___y_3191_ = v_snd_3210_;
goto _start;
}
}
else
{
lean_dec(v_tail_3205_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec_ref(v_f_3188_);
return v___x_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_f_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3212_, v_x_3213_, v_x_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(lean_object* v_f_3225_, lean_object* v_as_3226_, size_t v_i_3227_, size_t v_stop_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v___x_3239_; 
v___x_3239_ = lean_usize_dec_eq(v_i_3227_, v_stop_3228_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = lean_array_uget_borrowed(v_as_3226_, v_i_3227_);
v___x_3241_ = lean_box(0);
lean_inc(v___y_3237_);
lean_inc_ref(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
lean_inc_ref(v___y_3233_);
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
lean_inc(v___x_3240_);
lean_inc_ref(v_f_3225_);
v___x_3242_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3225_, v___x_3241_, v___x_3240_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
if (lean_obj_tag(v_a_3243_) == 0)
{
lean_dec_ref(v_a_3243_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v_f_3225_);
return v___x_3242_;
}
else
{
lean_object* v_a_3244_; lean_object* v_fst_3245_; lean_object* v_snd_3246_; size_t v___x_3247_; size_t v___x_3248_; 
lean_dec_ref(v___x_3242_);
v_a_3244_ = lean_ctor_get(v_a_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref(v_a_3243_);
v_fst_3245_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_fst_3245_);
v_snd_3246_ = lean_ctor_get(v_a_3244_, 1);
lean_inc(v_snd_3246_);
lean_dec(v_a_3244_);
v___x_3247_ = ((size_t)1ULL);
v___x_3248_ = lean_usize_add(v_i_3227_, v___x_3247_);
v_i_3227_ = v___x_3248_;
v_b_3229_ = v_fst_3245_;
v___y_3230_ = v_snd_3246_;
goto _start;
}
}
else
{
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v_f_3225_);
return v___x_3242_;
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v_f_3225_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_b_3229_);
lean_ctor_set(v___x_3250_, 1, v___y_3230_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4___boxed(lean_object* v_f_3253_, lean_object* v_as_3254_, lean_object* v_i_3255_, lean_object* v_stop_3256_, lean_object* v_b_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
size_t v_i_boxed_3267_; size_t v_stop_boxed_3268_; lean_object* v_res_3269_; 
v_i_boxed_3267_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_stop_boxed_3268_ = lean_unbox_usize(v_stop_3256_);
lean_dec(v_stop_3256_);
v_res_3269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3253_, v_as_3254_, v_i_boxed_3267_, v_stop_boxed_3268_, v_b_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec_ref(v_as_3254_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object* v_env_3270_, lean_object* v_f_3271_, lean_object* v_name_3272_, lean_object* v_c_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v___x_3283_; 
lean_inc(v_name_3272_);
v___x_3283_ = l_Lean_Meta_allowCompletion(v_env_3270_, v_name_3272_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v_c_3273_);
lean_dec(v_name_3272_);
lean_dec_ref(v_f_3271_);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___y_3274_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_inc_ref(v_c_3273_);
v___x_3288_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionKindForDecl___boxed), 6, 1);
lean_closure_set(v___x_3288_, 0, v_c_3273_);
lean_inc(v_name_3272_);
v___x_3289_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionTagsForDecl___boxed), 6, 1);
lean_closure_set(v___x_3289_, 0, v_name_3272_);
v___x_3290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3290_, 0, v_c_3273_);
lean_ctor_set(v___x_3290_, 1, v___x_3288_);
lean_ctor_set(v___x_3290_, 2, v___x_3289_);
v___x_3291_ = lean_apply_11(v_f_3271_, v_name_3272_, v___x_3290_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, lean_box(0));
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object* v_env_3292_, lean_object* v_f_3293_, lean_object* v_name_3294_, lean_object* v_c_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3292_, v_f_3293_, v_name_3294_, v_c_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object* v_f_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; lean_object* v_env_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_st_ref_get(v___y_3314_);
v_env_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc_ref(v_env_3317_);
lean_dec(v___x_3316_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc_ref(v_env_3317_);
v___x_3318_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_3317_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v_buckets_3320_; lean_object* v___f_3321_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref(v___x_3318_);
v_buckets_3320_ = lean_ctor_get(v_a_3319_, 1);
lean_inc_ref(v_buckets_3320_);
lean_dec(v_a_3319_);
lean_inc_ref(v_f_3306_);
lean_inc_ref(v_env_3317_);
v___f_3321_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3321_, 0, v_env_3317_);
lean_closure_set(v___f_3321_, 1, v_f_3306_);
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = lean_array_get_size(v_buckets_3320_);
v___x_3336_ = lean_nat_dec_lt(v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v_map_u2082_3338_; lean_object* v___x_3339_; 
lean_dec_ref(v_buckets_3320_);
lean_dec_ref(v_f_3306_);
v___x_3337_ = l_Lean_Environment_constants(v_env_3317_);
v_map_u2082_3338_ = lean_ctor_get(v___x_3337_, 1);
lean_inc_ref(v_map_u2082_3338_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3338_, v___f_3321_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
return v___x_3339_;
}
else
{
lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
if (v___x_3341_ == 0)
{
if (v___x_3336_ == 0)
{
lean_dec_ref(v_buckets_3320_);
lean_dec_ref(v_f_3306_);
v___y_3323_ = v___y_3307_;
v___y_3324_ = v___y_3308_;
v___y_3325_ = v___y_3309_;
v___y_3326_ = v___y_3310_;
v___y_3327_ = v___y_3311_;
v___y_3328_ = v___y_3312_;
v___y_3329_ = v___y_3313_;
v___y_3330_ = v___y_3314_;
goto v___jp_3322_;
}
else
{
size_t v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = lean_usize_of_nat(v___x_3335_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3306_, v_buckets_3320_, v___x_3342_, v___x_3343_, v___x_3340_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec_ref(v_buckets_3320_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
if (lean_obj_tag(v_a_3345_) == 0)
{
lean_dec_ref(v_a_3345_);
lean_dec_ref(v___f_3321_);
lean_dec_ref(v_env_3317_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v___x_3344_;
}
else
{
lean_object* v_a_3346_; lean_object* v_snd_3347_; 
lean_dec_ref(v___x_3344_);
v_a_3346_ = lean_ctor_get(v_a_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref(v_a_3345_);
v_snd_3347_ = lean_ctor_get(v_a_3346_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_a_3346_);
v___y_3323_ = v_snd_3347_;
v___y_3324_ = v___y_3308_;
v___y_3325_ = v___y_3309_;
v___y_3326_ = v___y_3310_;
v___y_3327_ = v___y_3311_;
v___y_3328_ = v___y_3312_;
v___y_3329_ = v___y_3313_;
v___y_3330_ = v___y_3314_;
goto v___jp_3322_;
}
}
else
{
lean_dec_ref(v___f_3321_);
lean_dec_ref(v_env_3317_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v___x_3344_;
}
}
}
else
{
size_t v___x_3348_; size_t v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((size_t)0ULL);
v___x_3349_ = lean_usize_of_nat(v___x_3335_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3306_, v_buckets_3320_, v___x_3348_, v___x_3349_, v___x_3340_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec_ref(v_buckets_3320_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
if (lean_obj_tag(v_a_3351_) == 0)
{
lean_dec_ref(v_a_3351_);
lean_dec_ref(v___f_3321_);
lean_dec_ref(v_env_3317_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v___x_3350_;
}
else
{
lean_object* v_a_3352_; lean_object* v_snd_3353_; 
lean_dec_ref(v___x_3350_);
v_a_3352_ = lean_ctor_get(v_a_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref(v_a_3351_);
v_snd_3353_ = lean_ctor_get(v_a_3352_, 1);
lean_inc(v_snd_3353_);
lean_dec(v_a_3352_);
v___y_3323_ = v_snd_3353_;
v___y_3324_ = v___y_3308_;
v___y_3325_ = v___y_3309_;
v___y_3326_ = v___y_3310_;
v___y_3327_ = v___y_3311_;
v___y_3328_ = v___y_3312_;
v___y_3329_ = v___y_3313_;
v___y_3330_ = v___y_3314_;
goto v___jp_3322_;
}
}
else
{
lean_dec_ref(v___f_3321_);
lean_dec_ref(v_env_3317_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v___x_3350_;
}
}
}
v___jp_3322_:
{
lean_object* v___x_3331_; lean_object* v_map_u2082_3332_; lean_object* v___x_3333_; 
v___x_3331_ = l_Lean_Environment_constants(v_env_3317_);
v_map_u2082_3332_ = lean_ctor_get(v___x_3331_, 1);
lean_inc_ref(v_map_u2082_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3332_, v___f_3321_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
return v___x_3333_;
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v_env_3317_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v_f_3306_);
v_a_3354_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3318_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3318_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object* v_f_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object* v_f_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___f_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___f_3382_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3382_, 0, v_f_3373_);
v___x_3383_ = lean_unsigned_to_nat(0u);
v___x_3384_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v___f_3382_, v___x_3383_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3404_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3404_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3404_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
if (lean_obj_tag(v_a_3385_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3399_; 
v_a_3389_ = lean_ctor_get(v_a_3385_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_a_3385_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3391_ = v_a_3385_;
v_isShared_3392_ = v_isSharedCheck_3399_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v_a_3385_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3399_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3396_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3394_);
v___x_3396_ = v___x_3387_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
lean_dec_ref(v_a_3385_);
v___x_3400_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3400_);
v___x_3402_ = v___x_3387_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
v_a_3405_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3384_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3384_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object* v_f_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg(lean_object* v_id_3425_, uint8_t v_danglingDot_3426_, lean_object* v_as_3427_, size_t v_sz_3428_, size_t v_i_3429_, lean_object* v_b_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_usize_dec_lt(v_i_3429_, v_sz_3428_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_b_3430_);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
else
{
lean_object* v_snd_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3490_; 
v_snd_3437_ = lean_ctor_get(v_b_3430_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_b_3430_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v_b_3430_, 0);
lean_dec(v_unused_3491_);
v___x_3439_ = v_b_3430_;
v_isShared_3440_ = v_isSharedCheck_3490_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_snd_3437_);
lean_dec(v_b_3430_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3490_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v_a_3443_; lean_object* v_a_3450_; 
v___x_3441_ = lean_box(0);
v_a_3450_ = lean_array_uget(v_as_3427_, v_i_3429_);
if (lean_obj_tag(v_a_3450_) == 0)
{
v_a_3443_ = v_snd_3437_;
goto v___jp_3442_;
}
else
{
lean_object* v_val_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3489_; 
lean_dec(v_snd_3437_);
v_val_3451_ = lean_ctor_get(v_a_3450_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_a_3450_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3453_ = v_a_3450_;
v_isShared_3454_ = v_isSharedCheck_3489_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_val_3451_);
lean_dec(v_a_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3489_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3455_ = lean_box(0);
v___x_3456_ = l_Lean_LocalDecl_userName(v_val_3451_);
v___x_3457_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3425_, v___x_3456_, v_danglingDot_3426_);
if (v___x_3457_ == 0)
{
lean_dec(v___x_3456_);
lean_del_object(v___x_3453_);
lean_dec(v_val_3451_);
v_a_3443_ = v___x_3455_;
goto v___jp_3442_;
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3458_ = l_Lean_LocalDecl_fvarId(v_val_3451_);
lean_dec(v_val_3451_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3458_);
v___x_3460_ = v___x_3453_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
uint8_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = 5;
v___x_3462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0));
v___x_3463_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3456_, v___x_3460_, v___x_3461_, v___x_3462_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3479_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3479_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3479_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
if (lean_obj_tag(v_a_3464_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3478_; 
lean_del_object(v___x_3439_);
v_a_3468_ = lean_ctor_get(v_a_3464_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_a_3464_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3470_ = v_a_3464_;
v_isShared_3471_ = v_isSharedCheck_3478_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v_a_3464_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3478_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3473_);
v___x_3475_ = v___x_3466_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_dec_ref(v_a_3464_);
lean_del_object(v___x_3466_);
v_a_3443_ = v___x_3455_;
goto v___jp_3442_;
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_del_object(v___x_3439_);
v_a_3480_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3463_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3463_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
}
}
v___jp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v_a_3443_);
lean_ctor_set(v___x_3439_, 0, v___x_3441_);
v___x_3445_ = v___x_3439_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_a_3443_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
size_t v___x_3446_; size_t v___x_3447_; 
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_add(v_i_3429_, v___x_3446_);
v_i_3429_ = v___x_3447_;
v_b_3430_ = v___x_3445_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_id_3492_, lean_object* v_danglingDot_3493_, lean_object* v_as_3494_, lean_object* v_sz_3495_, lean_object* v_i_3496_, lean_object* v_b_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
uint8_t v_danglingDot_boxed_3501_; size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_danglingDot_boxed_3501_ = lean_unbox(v_danglingDot_3493_);
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3495_);
lean_dec(v_sz_3495_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3496_);
lean_dec(v_i_3496_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg(v_id_3492_, v_danglingDot_boxed_3501_, v_as_3494_, v_sz_boxed_3502_, v_i_boxed_3503_, v_b_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v_as_3494_);
lean_dec(v_id_3492_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8(lean_object* v_id_3505_, uint8_t v_danglingDot_3506_, lean_object* v_as_3507_, size_t v_sz_3508_, size_t v_i_3509_, lean_object* v_b_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v___x_3519_; 
v___x_3519_ = lean_usize_dec_lt(v_i_3509_, v_sz_3508_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_b_3510_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
else
{
lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3575_; 
v_snd_3522_ = lean_ctor_get(v_b_3510_, 1);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_b_3510_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v_b_3510_, 0);
lean_dec(v_unused_3576_);
v___x_3524_ = v_b_3510_;
v_isShared_3525_ = v_isSharedCheck_3575_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_dec(v_b_3510_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3575_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v_a_3528_; lean_object* v_a_3535_; 
v___x_3526_ = lean_box(0);
v_a_3535_ = lean_array_uget(v_as_3507_, v_i_3509_);
if (lean_obj_tag(v_a_3535_) == 0)
{
v_a_3528_ = v_snd_3522_;
goto v___jp_3527_;
}
else
{
lean_object* v_val_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_snd_3522_);
v_val_3536_ = lean_ctor_get(v_a_3535_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_a_3535_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3538_ = v_a_3535_;
v_isShared_3539_ = v_isSharedCheck_3574_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_val_3536_);
lean_dec(v_a_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3574_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3540_ = lean_box(0);
v___x_3541_ = l_Lean_LocalDecl_userName(v_val_3536_);
v___x_3542_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3505_, v___x_3541_, v_danglingDot_3506_);
if (v___x_3542_ == 0)
{
lean_dec(v___x_3541_);
lean_del_object(v___x_3538_);
lean_dec(v_val_3536_);
v_a_3528_ = v___x_3540_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = l_Lean_LocalDecl_fvarId(v_val_3536_);
lean_dec(v_val_3536_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3543_);
v___x_3545_ = v___x_3538_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
uint8_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = 5;
v___x_3547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0));
v___x_3548_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3541_, v___x_3545_, v___x_3546_, v___x_3547_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3564_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3564_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3564_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
if (lean_obj_tag(v_a_3549_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3524_);
v_a_3553_ = lean_ctor_get(v_a_3549_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_a_3549_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3555_ = v_a_3549_;
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v_a_3549_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3560_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3558_);
v___x_3560_ = v___x_3551_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_dec_ref(v_a_3549_);
lean_del_object(v___x_3551_);
v_a_3528_ = v___x_3540_;
goto v___jp_3527_;
}
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_del_object(v___x_3524_);
v_a_3565_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3548_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3548_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
}
v___jp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v_a_3528_);
lean_ctor_set(v___x_3524_, 0, v___x_3526_);
v___x_3530_ = v___x_3524_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_a_3528_);
v___x_3530_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
size_t v___x_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = ((size_t)1ULL);
v___x_3532_ = lean_usize_add(v_i_3509_, v___x_3531_);
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg(v_id_3505_, v_danglingDot_3506_, v_as_3507_, v_sz_3508_, v___x_3532_, v___x_3530_, v___y_3511_, v___y_3512_);
return v___x_3533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8___boxed(lean_object* v_id_3577_, lean_object* v_danglingDot_3578_, lean_object* v_as_3579_, lean_object* v_sz_3580_, lean_object* v_i_3581_, lean_object* v_b_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
uint8_t v_danglingDot_boxed_3591_; size_t v_sz_boxed_3592_; size_t v_i_boxed_3593_; lean_object* v_res_3594_; 
v_danglingDot_boxed_3591_ = lean_unbox(v_danglingDot_3578_);
v_sz_boxed_3592_ = lean_unbox_usize(v_sz_3580_);
lean_dec(v_sz_3580_);
v_i_boxed_3593_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_res_3594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8(v_id_3577_, v_danglingDot_boxed_3591_, v_as_3579_, v_sz_boxed_3592_, v_i_boxed_3593_, v_b_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v_as_3579_);
lean_dec(v_id_3577_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg(lean_object* v_id_3595_, uint8_t v_danglingDot_3596_, lean_object* v_as_3597_, size_t v_sz_3598_, size_t v_i_3599_, lean_object* v_b_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
uint8_t v___x_3604_; 
v___x_3604_ = lean_usize_dec_lt(v_i_3599_, v_sz_3598_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3605_, 0, v_b_3600_);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
}
else
{
lean_object* v_snd_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3660_; 
v_snd_3607_ = lean_ctor_get(v_b_3600_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_b_3600_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v_b_3600_, 0);
lean_dec(v_unused_3661_);
v___x_3609_ = v_b_3600_;
v_isShared_3610_ = v_isSharedCheck_3660_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_snd_3607_);
lean_dec(v_b_3600_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3660_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v_a_3613_; lean_object* v_a_3620_; 
v___x_3611_ = lean_box(0);
v_a_3620_ = lean_array_uget(v_as_3597_, v_i_3599_);
if (lean_obj_tag(v_a_3620_) == 0)
{
v_a_3613_ = v_snd_3607_;
goto v___jp_3612_;
}
else
{
lean_object* v_val_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3659_; 
lean_dec(v_snd_3607_);
v_val_3621_ = lean_ctor_get(v_a_3620_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3620_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3623_ = v_a_3620_;
v_isShared_3624_ = v_isSharedCheck_3659_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_val_3621_);
lean_dec(v_a_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3659_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3625_ = lean_box(0);
v___x_3626_ = l_Lean_LocalDecl_userName(v_val_3621_);
v___x_3627_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3595_, v___x_3626_, v_danglingDot_3596_);
if (v___x_3627_ == 0)
{
lean_dec(v___x_3626_);
lean_del_object(v___x_3623_);
lean_dec(v_val_3621_);
v_a_3613_ = v___x_3625_;
goto v___jp_3612_;
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = l_Lean_LocalDecl_fvarId(v_val_3621_);
lean_dec(v_val_3621_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3628_);
v___x_3630_ = v___x_3623_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = 5;
v___x_3632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0));
v___x_3633_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3626_, v___x_3630_, v___x_3631_, v___x_3632_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3649_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3649_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3649_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
if (lean_obj_tag(v_a_3634_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3609_);
v_a_3638_ = lean_ctor_get(v_a_3634_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_a_3634_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3640_ = v_a_3634_;
v_isShared_3641_ = v_isSharedCheck_3648_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v_a_3634_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3648_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3645_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3643_);
v___x_3645_ = v___x_3636_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_dec_ref(v_a_3634_);
lean_del_object(v___x_3636_);
v_a_3613_ = v___x_3625_;
goto v___jp_3612_;
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_del_object(v___x_3609_);
v_a_3650_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3633_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3633_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
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
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
}
}
v___jp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v_a_3613_);
lean_ctor_set(v___x_3609_, 0, v___x_3611_);
v___x_3615_ = v___x_3609_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_a_3613_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
size_t v___x_3616_; size_t v___x_3617_; 
v___x_3616_ = ((size_t)1ULL);
v___x_3617_ = lean_usize_add(v_i_3599_, v___x_3616_);
v_i_3599_ = v___x_3617_;
v_b_3600_ = v___x_3615_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg___boxed(lean_object* v_id_3662_, lean_object* v_danglingDot_3663_, lean_object* v_as_3664_, lean_object* v_sz_3665_, lean_object* v_i_3666_, lean_object* v_b_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v_danglingDot_boxed_3671_; size_t v_sz_boxed_3672_; size_t v_i_boxed_3673_; lean_object* v_res_3674_; 
v_danglingDot_boxed_3671_ = lean_unbox(v_danglingDot_3663_);
v_sz_boxed_3672_ = lean_unbox_usize(v_sz_3665_);
lean_dec(v_sz_3665_);
v_i_boxed_3673_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg(v_id_3662_, v_danglingDot_boxed_3671_, v_as_3664_, v_sz_boxed_3672_, v_i_boxed_3673_, v_b_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v_as_3664_);
lean_dec(v_id_3662_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12(lean_object* v_id_3675_, uint8_t v_danglingDot_3676_, lean_object* v_as_3677_, size_t v_sz_3678_, size_t v_i_3679_, lean_object* v_b_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_usize_dec_lt(v_i_3679_, v_sz_3678_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v_b_3680_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
else
{
lean_object* v_snd_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3745_; 
v_snd_3692_ = lean_ctor_get(v_b_3680_, 1);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_b_3680_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; 
v_unused_3746_ = lean_ctor_get(v_b_3680_, 0);
lean_dec(v_unused_3746_);
v___x_3694_ = v_b_3680_;
v_isShared_3695_ = v_isSharedCheck_3745_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_snd_3692_);
lean_dec(v_b_3680_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3745_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v_a_3698_; lean_object* v_a_3705_; 
v___x_3696_ = lean_box(0);
v_a_3705_ = lean_array_uget(v_as_3677_, v_i_3679_);
if (lean_obj_tag(v_a_3705_) == 0)
{
v_a_3698_ = v_snd_3692_;
goto v___jp_3697_;
}
else
{
lean_object* v_val_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_snd_3692_);
v_val_3706_ = lean_ctor_get(v_a_3705_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_a_3705_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3708_ = v_a_3705_;
v_isShared_3709_ = v_isSharedCheck_3744_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_val_3706_);
lean_dec(v_a_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3744_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3710_ = lean_box(0);
v___x_3711_ = l_Lean_LocalDecl_userName(v_val_3706_);
v___x_3712_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3675_, v___x_3711_, v_danglingDot_3676_);
if (v___x_3712_ == 0)
{
lean_dec(v___x_3711_);
lean_del_object(v___x_3708_);
lean_dec(v_val_3706_);
v_a_3698_ = v___x_3710_;
goto v___jp_3697_;
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3713_ = l_Lean_LocalDecl_fvarId(v_val_3706_);
lean_dec(v_val_3706_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3713_);
v___x_3715_ = v___x_3708_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
uint8_t v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3716_ = 5;
v___x_3717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg___closed__0));
v___x_3718_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3711_, v___x_3715_, v___x_3716_, v___x_3717_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3734_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3734_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3734_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
if (lean_obj_tag(v_a_3719_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3733_; 
lean_del_object(v___x_3694_);
v_a_3723_ = lean_ctor_get(v_a_3719_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_a_3719_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3725_ = v_a_3719_;
v_isShared_3726_ = v_isSharedCheck_3733_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v_a_3719_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3733_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3730_; 
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3728_);
v___x_3730_ = v___x_3721_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_dec_ref(v_a_3719_);
lean_del_object(v___x_3721_);
v_a_3698_ = v___x_3710_;
goto v___jp_3697_;
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_del_object(v___x_3694_);
v_a_3735_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3718_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3718_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
}
}
v___jp_3697_:
{
lean_object* v___x_3700_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v_a_3698_);
lean_ctor_set(v___x_3694_, 0, v___x_3696_);
v___x_3700_ = v___x_3694_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_a_3698_);
v___x_3700_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
size_t v___x_3701_; size_t v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = ((size_t)1ULL);
v___x_3702_ = lean_usize_add(v_i_3679_, v___x_3701_);
v___x_3703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg(v_id_3675_, v_danglingDot_3676_, v_as_3677_, v_sz_3678_, v___x_3702_, v___x_3700_, v___y_3681_, v___y_3682_);
return v___x_3703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12___boxed(lean_object* v_id_3747_, lean_object* v_danglingDot_3748_, lean_object* v_as_3749_, lean_object* v_sz_3750_, lean_object* v_i_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
uint8_t v_danglingDot_boxed_3761_; size_t v_sz_boxed_3762_; size_t v_i_boxed_3763_; lean_object* v_res_3764_; 
v_danglingDot_boxed_3761_ = lean_unbox(v_danglingDot_3748_);
v_sz_boxed_3762_ = lean_unbox_usize(v_sz_3750_);
lean_dec(v_sz_3750_);
v_i_boxed_3763_ = lean_unbox_usize(v_i_3751_);
lean_dec(v_i_3751_);
v_res_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12(v_id_3747_, v_danglingDot_boxed_3761_, v_as_3749_, v_sz_boxed_3762_, v_i_boxed_3763_, v_b_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_as_3749_);
lean_dec(v_id_3747_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7(lean_object* v_id_3765_, uint8_t v_danglingDot_3766_, lean_object* v_inh_3767_, lean_object* v_n_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
if (lean_obj_tag(v_n_3768_) == 0)
{
lean_object* v_cs_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3834_; 
v_cs_3778_ = lean_ctor_get(v_n_3768_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_n_3768_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3780_ = v_n_3768_;
v_isShared_3781_ = v_isSharedCheck_3834_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_cs_3778_);
lean_dec(v_n_3768_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3834_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; size_t v_sz_3784_; size_t v___x_3785_; lean_object* v___x_3786_; 
v___x_3782_ = lean_box(0);
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set(v___x_3783_, 1, v_b_3769_);
v_sz_3784_ = lean_array_size(v_cs_3778_);
v___x_3785_ = ((size_t)0ULL);
v___x_3786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__11(v_id_3765_, v_danglingDot_3766_, v_inh_3767_, v_cs_3778_, v_sz_3784_, v___x_3785_, v___x_3783_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec_ref(v_cs_3778_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3825_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3825_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3825_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
if (lean_obj_tag(v_a_3787_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3780_);
v_a_3791_ = lean_ctor_get(v_a_3787_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_a_3787_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3793_ = v_a_3787_;
v_isShared_3794_ = v_isSharedCheck_3801_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v_a_3787_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3801_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3798_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3796_);
v___x_3798_ = v___x_3789_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3824_; 
v_a_3802_ = lean_ctor_get(v_a_3787_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3787_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3804_ = v_a_3787_;
v_isShared_3805_ = v_isSharedCheck_3824_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v_a_3787_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3824_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v_fst_3806_; 
v_fst_3806_ = lean_ctor_get(v_a_3802_, 0);
if (lean_obj_tag(v_fst_3806_) == 0)
{
lean_object* v_snd_3807_; lean_object* v___x_3809_; 
v_snd_3807_ = lean_ctor_get(v_a_3802_, 1);
lean_inc(v_snd_3807_);
lean_dec(v_a_3802_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set_tag(v___x_3780_, 1);
lean_ctor_set(v___x_3780_, 0, v_snd_3807_);
v___x_3809_ = v___x_3780_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_snd_3807_);
v___x_3809_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3809_);
v___x_3811_ = v___x_3804_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3813_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3811_);
v___x_3813_ = v___x_3789_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_val_3817_; lean_object* v___x_3819_; 
lean_inc_ref(v_fst_3806_);
lean_dec(v_a_3802_);
lean_del_object(v___x_3780_);
v_val_3817_ = lean_ctor_get(v_fst_3806_, 0);
lean_inc(v_val_3817_);
lean_dec_ref(v_fst_3806_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v_val_3817_);
v___x_3819_ = v___x_3804_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_val_3817_);
v___x_3819_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3821_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3819_);
v___x_3821_ = v___x_3789_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_del_object(v___x_3780_);
v_a_3826_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3786_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3786_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
else
{
lean_object* v_vs_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3891_; 
v_vs_3835_ = lean_ctor_get(v_n_3768_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_n_3768_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3837_ = v_n_3768_;
v_isShared_3838_ = v_isSharedCheck_3891_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_vs_3835_);
lean_dec(v_n_3768_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3891_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; size_t v_sz_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
lean_ctor_set(v___x_3840_, 1, v_b_3769_);
v_sz_3841_ = lean_array_size(v_vs_3835_);
v___x_3842_ = ((size_t)0ULL);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12(v_id_3765_, v_danglingDot_3766_, v_vs_3835_, v_sz_3841_, v___x_3842_, v___x_3840_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec_ref(v_vs_3835_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3882_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3846_ = v___x_3843_;
v_isShared_3847_ = v_isSharedCheck_3882_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3882_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
if (lean_obj_tag(v_a_3844_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3858_; 
lean_del_object(v___x_3837_);
v_a_3848_ = lean_ctor_get(v_a_3844_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_a_3844_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3850_ = v_a_3844_;
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v_a_3844_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3853_);
v___x_3855_ = v___x_3846_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3881_; 
v_a_3859_ = lean_ctor_get(v_a_3844_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_a_3844_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3861_ = v_a_3844_;
v_isShared_3862_ = v_isSharedCheck_3881_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v_a_3844_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3881_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_fst_3863_; 
v_fst_3863_ = lean_ctor_get(v_a_3859_, 0);
if (lean_obj_tag(v_fst_3863_) == 0)
{
lean_object* v_snd_3864_; lean_object* v___x_3866_; 
v_snd_3864_ = lean_ctor_get(v_a_3859_, 1);
lean_inc(v_snd_3864_);
lean_dec(v_a_3859_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_snd_3864_);
v___x_3866_ = v___x_3837_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_snd_3864_);
v___x_3866_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3868_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3866_);
v___x_3868_ = v___x_3861_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3870_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3868_);
v___x_3870_ = v___x_3846_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_object* v_val_3874_; lean_object* v___x_3876_; 
lean_inc_ref(v_fst_3863_);
lean_dec(v_a_3859_);
lean_del_object(v___x_3837_);
v_val_3874_ = lean_ctor_get(v_fst_3863_, 0);
lean_inc(v_val_3874_);
lean_dec_ref(v_fst_3863_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v_val_3874_);
v___x_3876_ = v___x_3861_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_val_3874_);
v___x_3876_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3878_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3876_);
v___x_3878_ = v___x_3846_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_del_object(v___x_3837_);
v_a_3883_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3843_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3843_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__11(lean_object* v_id_3892_, uint8_t v_danglingDot_3893_, lean_object* v_inh_3894_, lean_object* v_as_3895_, size_t v_sz_3896_, size_t v_i_3897_, lean_object* v_b_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v___x_3907_; 
v___x_3907_ = lean_usize_dec_lt(v_i_3897_, v_sz_3896_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v_b_3898_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
else
{
lean_object* v_snd_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3963_; 
v_snd_3910_ = lean_ctor_get(v_b_3898_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_b_3898_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v_b_3898_, 0);
lean_dec(v_unused_3964_);
v___x_3912_ = v_b_3898_;
v_isShared_3913_ = v_isSharedCheck_3963_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_snd_3910_);
lean_dec(v_b_3898_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3963_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_array_uget_borrowed(v_as_3895_, v_i_3897_);
lean_inc(v_snd_3910_);
lean_inc(v_a_3914_);
v___x_3915_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7(v_id_3892_, v_danglingDot_3893_, v_inh_3894_, v_a_3914_, v_snd_3910_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3954_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3954_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3954_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
if (lean_obj_tag(v_a_3916_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3912_);
lean_dec(v_snd_3910_);
v_a_3920_ = lean_ctor_get(v_a_3916_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_a_3916_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3922_ = v_a_3916_;
v_isShared_3923_ = v_isSharedCheck_3930_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v_a_3916_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3930_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3927_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3925_);
v___x_3927_ = v___x_3918_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3953_; 
v_a_3931_ = lean_ctor_get(v_a_3916_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v_a_3916_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3933_ = v_a_3916_;
v_isShared_3934_ = v_isSharedCheck_3953_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v_a_3916_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3953_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
if (lean_obj_tag(v_a_3931_) == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v_a_3931_);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3935_);
v___x_3937_ = v___x_3912_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_snd_3910_);
v___x_3937_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3939_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3937_);
v___x_3939_ = v___x_3933_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3941_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3939_);
v___x_3941_ = v___x_3918_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
lean_del_object(v___x_3933_);
lean_del_object(v___x_3918_);
lean_dec(v_snd_3910_);
v_a_3945_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_a_3945_);
lean_dec_ref(v_a_3931_);
v___x_3946_ = lean_box(0);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 1, v_a_3945_);
lean_ctor_set(v___x_3912_, 0, v___x_3946_);
v___x_3948_ = v___x_3912_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_a_3945_);
v___x_3948_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
size_t v___x_3949_; size_t v___x_3950_; 
v___x_3949_ = ((size_t)1ULL);
v___x_3950_ = lean_usize_add(v_i_3897_, v___x_3949_);
v_i_3897_ = v___x_3950_;
v_b_3898_ = v___x_3948_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_del_object(v___x_3912_);
lean_dec(v_snd_3910_);
v_a_3955_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3915_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3915_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__11___boxed(lean_object* v_id_3965_, lean_object* v_danglingDot_3966_, lean_object* v_inh_3967_, lean_object* v_as_3968_, lean_object* v_sz_3969_, lean_object* v_i_3970_, lean_object* v_b_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
uint8_t v_danglingDot_boxed_3980_; size_t v_sz_boxed_3981_; size_t v_i_boxed_3982_; lean_object* v_res_3983_; 
v_danglingDot_boxed_3980_ = lean_unbox(v_danglingDot_3966_);
v_sz_boxed_3981_ = lean_unbox_usize(v_sz_3969_);
lean_dec(v_sz_3969_);
v_i_boxed_3982_ = lean_unbox_usize(v_i_3970_);
lean_dec(v_i_3970_);
v_res_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__11(v_id_3965_, v_danglingDot_boxed_3980_, v_inh_3967_, v_as_3968_, v_sz_boxed_3981_, v_i_boxed_3982_, v_b_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec_ref(v_as_3968_);
lean_dec(v_id_3965_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7___boxed(lean_object* v_id_3984_, lean_object* v_danglingDot_3985_, lean_object* v_inh_3986_, lean_object* v_n_3987_, lean_object* v_b_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
uint8_t v_danglingDot_boxed_3997_; lean_object* v_res_3998_; 
v_danglingDot_boxed_3997_ = lean_unbox(v_danglingDot_3985_);
v_res_3998_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7(v_id_3984_, v_danglingDot_boxed_3997_, v_inh_3986_, v_n_3987_, v_b_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v_id_3984_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_id_3999_, uint8_t v_danglingDot_4000_, lean_object* v_t_4001_, lean_object* v_init_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_b_4012_; lean_object* v_root_4015_; lean_object* v_tail_4016_; lean_object* v___x_4017_; 
v_root_4015_ = lean_ctor_get(v_t_4001_, 0);
lean_inc_ref(v_root_4015_);
v_tail_4016_ = lean_ctor_get(v_t_4001_, 1);
lean_inc_ref(v_tail_4016_);
lean_dec_ref(v_t_4001_);
v___x_4017_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7(v_id_3999_, v_danglingDot_4000_, v_init_4002_, v_root_4015_, v_init_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4079_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4079_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4079_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
if (lean_obj_tag(v_a_4018_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v_tail_4016_);
v_a_4022_ = lean_ctor_get(v_a_4018_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v_a_4018_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4024_ = v_a_4018_;
v_isShared_4025_ = v_isSharedCheck_4032_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v_a_4018_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4032_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4029_; 
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4027_);
v___x_4029_ = v___x_4020_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
lean_object* v_a_4033_; 
lean_del_object(v___x_4020_);
v_a_4033_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_a_4033_);
lean_dec_ref(v_a_4018_);
if (lean_obj_tag(v_a_4033_) == 0)
{
lean_object* v_a_4034_; 
lean_dec_ref(v_tail_4016_);
v_a_4034_ = lean_ctor_get(v_a_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref(v_a_4033_);
v_b_4012_ = v_a_4034_;
goto v___jp_4011_;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; size_t v_sz_4038_; size_t v___x_4039_; lean_object* v___x_4040_; 
v_a_4035_ = lean_ctor_get(v_a_4033_, 0);
lean_inc(v_a_4035_);
lean_dec_ref(v_a_4033_);
v___x_4036_ = lean_box(0);
v___x_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
lean_ctor_set(v___x_4037_, 1, v_a_4035_);
v_sz_4038_ = lean_array_size(v_tail_4016_);
v___x_4039_ = ((size_t)0ULL);
v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8(v_id_3999_, v_danglingDot_4000_, v_tail_4016_, v_sz_4038_, v___x_4039_, v___x_4037_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec_ref(v_tail_4016_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4070_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4070_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4070_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
if (lean_obj_tag(v_a_4041_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4055_; 
v_a_4045_ = lean_ctor_get(v_a_4041_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_a_4041_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4047_ = v_a_4041_;
v_isShared_4048_ = v_isSharedCheck_4055_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v_a_4041_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4055_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4050_);
v___x_4052_ = v___x_4043_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4069_; 
v_a_4056_ = lean_ctor_get(v_a_4041_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_a_4041_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4058_ = v_a_4041_;
v_isShared_4059_ = v_isSharedCheck_4069_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v_a_4041_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4069_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v_fst_4060_; 
v_fst_4060_ = lean_ctor_get(v_a_4056_, 0);
if (lean_obj_tag(v_fst_4060_) == 0)
{
lean_object* v_snd_4061_; lean_object* v___x_4063_; 
v_snd_4061_ = lean_ctor_get(v_a_4056_, 1);
lean_inc(v_snd_4061_);
lean_dec(v_a_4056_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v_snd_4061_);
v___x_4063_ = v___x_4058_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_snd_4061_);
v___x_4063_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4065_; 
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4063_);
v___x_4065_ = v___x_4043_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
else
{
lean_object* v_val_4068_; 
lean_inc_ref(v_fst_4060_);
lean_del_object(v___x_4058_);
lean_dec(v_a_4056_);
lean_del_object(v___x_4043_);
v_val_4068_ = lean_ctor_get(v_fst_4060_, 0);
lean_inc(v_val_4068_);
lean_dec_ref(v_fst_4060_);
v_b_4012_ = v_val_4068_;
goto v___jp_4011_;
}
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
v_a_4071_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4040_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4040_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
lean_dec_ref(v_tail_4016_);
v_a_4080_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4017_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4017_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
v___jp_4011_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4013_, 0, v_b_4012_);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_id_4088_, lean_object* v_danglingDot_4089_, lean_object* v_t_4090_, lean_object* v_init_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
uint8_t v_danglingDot_boxed_4100_; lean_object* v_res_4101_; 
v_danglingDot_boxed_4100_ = lean_unbox(v_danglingDot_4089_);
v_res_4101_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_id_4088_, v_danglingDot_boxed_4100_, v_t_4090_, v_init_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v_id_4088_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0(lean_object* v___x_4102_, lean_object* v_a_4103_, lean_object* v___x_4104_, lean_object* v_ns_4105_, lean_object* v_id_4106_, uint8_t v_danglingDot_4107_, lean_object* v_alias_4108_, lean_object* v_declNames_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v___y_4119_; uint8_t v___x_4123_; 
v___x_4123_ = l_Lean_Name_isPrefixOf(v_ns_4105_, v_alias_4108_);
if (v___x_4123_ == 0)
{
v___y_4119_ = v___x_4123_;
goto v___jp_4118_;
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4124_ = lean_box(0);
lean_inc(v_alias_4108_);
v___x_4125_ = l_Lean_Name_replacePrefix(v_alias_4108_, v_ns_4105_, v___x_4124_);
v___x_4126_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4106_, v___x_4125_, v_danglingDot_4107_);
lean_dec(v___x_4125_);
v___y_4119_ = v___x_4126_;
goto v___jp_4118_;
}
v___jp_4118_:
{
if (v___y_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v_declNames_4109_);
lean_dec(v_alias_4108_);
lean_dec_ref(v___x_4104_);
v___x_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4102_);
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
return v___x_4121_;
}
else
{
lean_object* v___x_4122_; 
v___x_4122_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4103_, v___x_4104_, v_alias_4108_, v_declNames_4109_, v___y_4110_, v___y_4111_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v_alias_4108_);
return v___x_4122_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0___boxed(lean_object* v___x_4127_, lean_object* v_a_4128_, lean_object* v___x_4129_, lean_object* v_ns_4130_, lean_object* v_id_4131_, lean_object* v_danglingDot_4132_, lean_object* v_alias_4133_, lean_object* v_declNames_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
uint8_t v_danglingDot_boxed_4143_; lean_object* v_res_4144_; 
v_danglingDot_boxed_4143_ = lean_unbox(v_danglingDot_4132_);
v_res_4144_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0(v___x_4127_, v_a_4128_, v___x_4129_, v_ns_4130_, v_id_4131_, v_danglingDot_boxed_4143_, v_alias_4133_, v_declNames_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v_id_4131_);
lean_dec(v_ns_4130_);
lean_dec_ref(v_a_4128_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object* v_a_4145_, lean_object* v___x_4146_, lean_object* v_id_4147_, uint8_t v_danglingDot_4148_, lean_object* v_as_x27_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_a_4160_; 
if (lean_obj_tag(v_as_x27_4149_) == 0)
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v_id_4147_);
lean_dec_ref(v___x_4146_);
lean_dec_ref(v_a_4145_);
v___x_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_b_4150_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
else
{
lean_object* v_head_4165_; lean_object* v_tail_4166_; lean_object* v___x_4167_; 
v_head_4165_ = lean_ctor_get(v_as_x27_4149_, 0);
lean_inc(v_head_4165_);
v_tail_4166_ = lean_ctor_get(v_as_x27_4149_, 1);
lean_inc(v_tail_4166_);
lean_dec_ref(v_as_x27_4149_);
v___x_4167_ = lean_box(0);
if (lean_obj_tag(v_head_4165_) == 0)
{
lean_object* v_ns_4168_; lean_object* v___x_4169_; lean_object* v___f_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_ns_4168_ = lean_ctor_get(v_head_4165_, 0);
lean_inc(v_ns_4168_);
lean_dec_ref(v_head_4165_);
v___x_4169_ = lean_box(v_danglingDot_4148_);
lean_inc(v_id_4147_);
lean_inc_ref(v___x_4146_);
lean_inc_ref(v_a_4145_);
v___f_4170_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4170_, 0, v___x_4167_);
lean_closure_set(v___f_4170_, 1, v_a_4145_);
lean_closure_set(v___f_4170_, 2, v___x_4146_);
lean_closure_set(v___f_4170_, 3, v_ns_4168_);
lean_closure_set(v___f_4170_, 4, v_id_4147_);
lean_closure_set(v___f_4170_, 5, v___x_4169_);
lean_inc_ref(v___x_4146_);
v___x_4171_ = l_Lean_getAliasState(v___x_4146_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
lean_inc(v___y_4155_);
lean_inc_ref(v___y_4154_);
lean_inc_ref(v___y_4153_);
lean_inc(v___y_4152_);
lean_inc_ref(v___y_4151_);
v___x_4172_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v___x_4171_, v___f_4170_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref(v___x_4172_);
if (lean_obj_tag(v_a_4173_) == 0)
{
lean_object* v_a_4174_; 
lean_dec(v_tail_4166_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v_id_4147_);
lean_dec_ref(v___x_4146_);
lean_dec_ref(v_a_4145_);
v_a_4174_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v_a_4173_);
v_a_4160_ = v_a_4174_;
goto v___jp_4159_;
}
else
{
lean_dec_ref(v_a_4173_);
v_as_x27_4149_ = v_tail_4166_;
v_b_4150_ = v___x_4167_;
goto _start;
}
}
else
{
lean_dec(v_tail_4166_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v_id_4147_);
lean_dec_ref(v___x_4146_);
lean_dec_ref(v_a_4145_);
return v___x_4172_;
}
}
else
{
lean_object* v_id_4176_; lean_object* v_declName_4177_; uint8_t v___x_4178_; 
v_id_4176_ = lean_ctor_get(v_head_4165_, 0);
lean_inc(v_id_4176_);
v_declName_4177_ = lean_ctor_get(v_head_4165_, 1);
lean_inc(v_declName_4177_);
lean_dec_ref(v_head_4165_);
lean_inc(v_declName_4177_);
lean_inc_ref(v___x_4146_);
v___x_4178_ = l_Lean_Server_Completion_allowCompletion(v_a_4145_, v___x_4146_, v_declName_4177_);
if (v___x_4178_ == 0)
{
lean_dec(v_declName_4177_);
lean_dec(v_id_4176_);
v_as_x27_4149_ = v_tail_4166_;
v_b_4150_ = v___x_4167_;
goto _start;
}
else
{
uint8_t v___x_4180_; 
v___x_4180_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4147_, v_id_4176_, v_danglingDot_4148_);
if (v___x_4180_ == 0)
{
lean_dec(v_declName_4177_);
lean_dec(v_id_4176_);
v_as_x27_4149_ = v_tail_4166_;
v_b_4150_ = v___x_4167_;
goto _start;
}
else
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4182_ = l_Lean_Name_getString_x21(v_id_4176_);
lean_dec(v_id_4176_);
v___x_4183_ = lean_box(0);
v___x_4184_ = l_Lean_Name_str___override(v___x_4183_, v___x_4182_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
lean_inc(v___y_4155_);
lean_inc_ref(v___y_4154_);
v___x_4185_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4184_, v_declName_4177_, v___y_4151_, v___y_4152_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_dec_ref(v___x_4185_);
v_as_x27_4149_ = v_tail_4166_;
v_b_4150_ = v___x_4167_;
goto _start;
}
else
{
lean_dec(v_tail_4166_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v_id_4147_);
lean_dec_ref(v___x_4146_);
lean_dec_ref(v_a_4145_);
return v___x_4185_;
}
}
}
}
}
v___jp_4159_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_a_4160_);
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
return v___x_4162_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object* v_a_4187_, lean_object* v___x_4188_, lean_object* v_id_4189_, lean_object* v_danglingDot_4190_, lean_object* v_as_x27_4191_, lean_object* v_b_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
uint8_t v_danglingDot_boxed_4201_; lean_object* v_res_4202_; 
v_danglingDot_boxed_4201_ = lean_unbox(v_danglingDot_4190_);
v_res_4202_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_a_4187_, v___x_4188_, v_id_4189_, v_danglingDot_boxed_4201_, v_as_x27_4191_, v_b_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object* v_id_4203_, uint8_t v_danglingDot_4204_, lean_object* v_a_4205_, lean_object* v___x_4206_, lean_object* v_as_4207_, lean_object* v_as_x27_4208_, lean_object* v_b_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_a_4219_; 
if (lean_obj_tag(v_as_x27_4208_) == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec_ref(v___x_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_id_4203_);
v___x_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4222_, 0, v_b_4209_);
v___x_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
return v___x_4223_;
}
else
{
lean_object* v_head_4224_; lean_object* v_tail_4225_; lean_object* v___x_4226_; 
v_head_4224_ = lean_ctor_get(v_as_x27_4208_, 0);
lean_inc(v_head_4224_);
v_tail_4225_ = lean_ctor_get(v_as_x27_4208_, 1);
lean_inc(v_tail_4225_);
lean_dec_ref(v_as_x27_4208_);
v___x_4226_ = lean_box(0);
if (lean_obj_tag(v_head_4224_) == 0)
{
lean_object* v_ns_4227_; lean_object* v___x_4228_; lean_object* v___f_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v_ns_4227_ = lean_ctor_get(v_head_4224_, 0);
lean_inc(v_ns_4227_);
lean_dec_ref(v_head_4224_);
v___x_4228_ = lean_box(v_danglingDot_4204_);
lean_inc(v_id_4203_);
lean_inc_ref(v___x_4206_);
lean_inc_ref(v_a_4205_);
v___f_4229_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4229_, 0, v___x_4226_);
lean_closure_set(v___f_4229_, 1, v_a_4205_);
lean_closure_set(v___f_4229_, 2, v___x_4206_);
lean_closure_set(v___f_4229_, 3, v_ns_4227_);
lean_closure_set(v___f_4229_, 4, v_id_4203_);
lean_closure_set(v___f_4229_, 5, v___x_4228_);
lean_inc_ref(v___x_4206_);
v___x_4230_ = l_Lean_getAliasState(v___x_4206_);
lean_inc(v___y_4216_);
lean_inc_ref(v___y_4215_);
lean_inc(v___y_4214_);
lean_inc_ref(v___y_4213_);
lean_inc_ref(v___y_4212_);
lean_inc(v___y_4211_);
lean_inc_ref(v___y_4210_);
v___x_4231_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v___x_4230_, v___f_4229_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref(v___x_4231_);
if (lean_obj_tag(v_a_4232_) == 0)
{
lean_object* v_a_4233_; 
lean_dec(v_tail_4225_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec_ref(v___x_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_id_4203_);
v_a_4233_ = lean_ctor_get(v_a_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v_a_4232_);
v_a_4219_ = v_a_4233_;
goto v___jp_4218_;
}
else
{
lean_object* v___x_4234_; 
lean_dec_ref(v_a_4232_);
v___x_4234_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_a_4205_, v___x_4206_, v_id_4203_, v_danglingDot_4204_, v_tail_4225_, v___x_4226_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4234_;
}
}
else
{
lean_dec(v_tail_4225_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec_ref(v___x_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_id_4203_);
return v___x_4231_;
}
}
else
{
lean_object* v_id_4235_; lean_object* v_declName_4236_; uint8_t v___x_4237_; 
v_id_4235_ = lean_ctor_get(v_head_4224_, 0);
lean_inc(v_id_4235_);
v_declName_4236_ = lean_ctor_get(v_head_4224_, 1);
lean_inc(v_declName_4236_);
lean_dec_ref(v_head_4224_);
lean_inc(v_declName_4236_);
lean_inc_ref(v___x_4206_);
v___x_4237_ = l_Lean_Server_Completion_allowCompletion(v_a_4205_, v___x_4206_, v_declName_4236_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; 
lean_dec(v_declName_4236_);
lean_dec(v_id_4235_);
v___x_4238_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_a_4205_, v___x_4206_, v_id_4203_, v_danglingDot_4204_, v_tail_4225_, v___x_4226_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4238_;
}
else
{
uint8_t v___x_4239_; 
v___x_4239_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4203_, v_id_4235_, v_danglingDot_4204_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; 
lean_dec(v_declName_4236_);
lean_dec(v_id_4235_);
v___x_4240_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_a_4205_, v___x_4206_, v_id_4203_, v_danglingDot_4204_, v_tail_4225_, v___x_4226_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4240_;
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4241_ = l_Lean_Name_getString_x21(v_id_4235_);
lean_dec(v_id_4235_);
v___x_4242_ = lean_box(0);
v___x_4243_ = l_Lean_Name_str___override(v___x_4242_, v___x_4241_);
lean_inc(v___y_4216_);
lean_inc_ref(v___y_4215_);
lean_inc(v___y_4214_);
lean_inc_ref(v___y_4213_);
v___x_4244_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4243_, v_declName_4236_, v___y_4210_, v___y_4211_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v___x_4245_; 
lean_dec_ref(v___x_4244_);
v___x_4245_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_a_4205_, v___x_4206_, v_id_4203_, v_danglingDot_4204_, v_tail_4225_, v___x_4226_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4245_;
}
else
{
lean_dec(v_tail_4225_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec_ref(v___x_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_id_4203_);
return v___x_4244_;
}
}
}
}
}
v___jp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v_a_4219_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
return v___x_4221_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object* v_id_4246_, lean_object* v_danglingDot_4247_, lean_object* v_a_4248_, lean_object* v___x_4249_, lean_object* v_as_4250_, lean_object* v_as_x27_4251_, lean_object* v_b_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
uint8_t v_danglingDot_boxed_4261_; lean_object* v_res_4262_; 
v_danglingDot_boxed_4261_ = lean_unbox(v_danglingDot_4247_);
v_res_4262_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_id_4246_, v_danglingDot_boxed_4261_, v_a_4248_, v___x_4249_, v_as_4250_, v_as_x27_4251_, v_b_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v_as_4250_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_as_4263_, size_t v_sz_4264_, size_t v_i_4265_, lean_object* v_b_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
uint8_t v___x_4270_; 
v___x_4270_ = lean_usize_dec_lt(v_i_4265_, v_sz_4264_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_b_4266_);
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4271_);
return v___x_4272_;
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4274_; 
v_a_4273_ = lean_array_uget_borrowed(v_as_4263_, v_i_4265_);
lean_inc(v_a_4273_);
v___x_4274_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_4273_, v___y_4267_, v___y_4268_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
if (lean_obj_tag(v_a_4275_) == 0)
{
lean_dec_ref(v_a_4275_);
return v___x_4274_;
}
else
{
lean_object* v___x_4276_; size_t v___x_4277_; size_t v___x_4278_; 
lean_dec_ref(v_a_4275_);
lean_dec_ref(v___x_4274_);
v___x_4276_ = lean_box(0);
v___x_4277_ = ((size_t)1ULL);
v___x_4278_ = lean_usize_add(v_i_4265_, v___x_4277_);
v_i_4265_ = v___x_4278_;
v_b_4266_ = v___x_4276_;
goto _start;
}
}
else
{
return v___x_4274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_as_4280_, lean_object* v_sz_4281_, lean_object* v_i_4282_, lean_object* v_b_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
size_t v_sz_boxed_4287_; size_t v_i_boxed_4288_; lean_object* v_res_4289_; 
v_sz_boxed_4287_ = lean_unbox_usize(v_sz_4281_);
lean_dec(v_sz_4281_);
v_i_boxed_4288_ = lean_unbox_usize(v_i_4282_);
lean_dec(v_i_4282_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_as_4280_, v_sz_boxed_4287_, v_i_boxed_4288_, v_b_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v_as_4280_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4290_, lean_object* v_stx_4291_, lean_object* v_id_4292_, lean_object* v_hoverInfo_4293_, uint8_t v_danglingDot_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; uint8_t v___y_4313_; lean_object* v___y_4314_; lean_object* v_id_4355_; uint8_t v_danglingDot_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v_id_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; uint8_t v___x_4386_; 
v___x_4386_ = l_Lean_Name_hasMacroScopes(v_id_4292_);
if (v___x_4386_ == 0)
{
v_id_4375_ = v_id_4292_;
v___y_4376_ = v_a_4295_;
v___y_4377_ = v_a_4296_;
v___y_4378_ = v_a_4297_;
v___y_4379_ = v_a_4298_;
v___y_4380_ = v_a_4299_;
v___y_4381_ = v_a_4300_;
v___y_4382_ = v_a_4301_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Lean_Syntax_getHeadInfo(v_stx_4291_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_id_4388_; 
lean_dec_ref(v___x_4387_);
v_id_4388_ = lean_erase_macro_scopes(v_id_4292_);
v_id_4375_ = v_id_4388_;
v___y_4376_ = v_a_4295_;
v___y_4377_ = v_a_4296_;
v___y_4378_ = v_a_4297_;
v___y_4379_ = v_a_4298_;
v___y_4380_ = v_a_4299_;
v___y_4381_ = v_a_4300_;
v___y_4382_ = v_a_4301_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
lean_dec(v___x_4387_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_hoverInfo_4293_);
lean_dec(v_id_4292_);
lean_dec_ref(v_ctx_4290_);
v___x_4389_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
return v___x_4390_;
}
}
v___jp_4303_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4315_ = lean_st_ref_get(v___y_4311_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4312_);
lean_inc_ref(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4307_);
lean_inc_ref(v___y_4308_);
v___x_4316_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4314_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
if (lean_obj_tag(v_a_4317_) == 0)
{
lean_dec_ref(v_a_4317_);
lean_dec(v___x_4315_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4316_;
}
else
{
lean_object* v___x_4318_; lean_object* v_a_4319_; 
lean_dec_ref(v_a_4317_);
lean_dec_ref(v___x_4316_);
v___x_4318_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4305_);
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
if (lean_obj_tag(v_a_4319_) == 0)
{
lean_dec_ref(v_a_4319_);
lean_dec(v___x_4315_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4318_;
}
else
{
lean_object* v_env_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v_a_4319_);
lean_dec_ref(v___x_4318_);
v_env_4320_ = lean_ctor_get(v___x_4315_, 0);
lean_inc_ref(v_env_4320_);
lean_dec(v___x_4315_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4312_);
lean_inc_ref(v___y_4306_);
lean_inc_ref(v_env_4320_);
v___x_4321_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4320_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_toCommandContextInfo_4322_; lean_object* v_a_4323_; lean_object* v_currNamespace_4324_; lean_object* v_openDecls_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v_toCommandContextInfo_4322_ = lean_ctor_get(v_ctx_4290_, 0);
v_a_4323_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4321_);
v_currNamespace_4324_ = lean_ctor_get(v_toCommandContextInfo_4322_, 5);
v_openDecls_4325_ = lean_ctor_get(v_toCommandContextInfo_4322_, 6);
v___x_4326_ = lean_box(0);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4312_);
lean_inc_ref(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4307_);
lean_inc_ref(v___y_4308_);
lean_inc(v_openDecls_4325_);
lean_inc_ref(v_env_4320_);
lean_inc(v_a_4323_);
lean_inc(v___y_4304_);
v___x_4327_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___y_4304_, v___y_4313_, v_a_4323_, v_env_4320_, v_openDecls_4325_, v_openDecls_4325_, v___x_4326_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
if (lean_obj_tag(v_a_4328_) == 0)
{
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4323_);
lean_dec_ref(v_env_4320_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4327_;
}
else
{
lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
lean_dec_ref(v_a_4328_);
lean_dec_ref(v___x_4327_);
lean_inc_ref(v_env_4320_);
v___f_4329_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4329_, 0, v_a_4323_);
lean_closure_set(v___f_4329_, 1, v_env_4320_);
lean_inc(v_currNamespace_4324_);
v___f_4330_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4330_, 0, v___y_4309_);
lean_closure_set(v___f_4330_, 1, v___f_4329_);
lean_closure_set(v___f_4330_, 2, v_currNamespace_4324_);
lean_inc_ref(v_env_4320_);
v___x_4331_ = l_Lean_getAliasState(v_env_4320_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4312_);
lean_inc_ref(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4307_);
lean_inc_ref(v___y_4308_);
v___x_4332_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v___x_4331_, v___f_4330_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
if (lean_obj_tag(v_a_4333_) == 0)
{
lean_dec_ref(v_a_4333_);
lean_dec_ref(v_env_4320_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4332_;
}
else
{
lean_dec_ref(v_a_4333_);
lean_dec_ref(v___x_4332_);
if (v___y_4313_ == 0)
{
if (lean_obj_tag(v___y_4304_) == 1)
{
lean_object* v_pre_4334_; 
v_pre_4334_ = lean_ctor_get(v___y_4304_, 0);
if (lean_obj_tag(v_pre_4334_) == 0)
{
lean_object* v_str_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; size_t v_sz_4338_; size_t v___x_4339_; lean_object* v___x_4340_; 
v_str_4335_ = lean_ctor_get(v___y_4304_, 1);
v___x_4336_ = l_Lean_Parser_getTokenTable(v_env_4320_);
v___x_4337_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4336_, v_str_4335_);
v_sz_4338_ = lean_array_size(v___x_4337_);
v___x_4339_ = ((size_t)0ULL);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___x_4337_, v_sz_4338_, v___x_4339_, v___x_4326_, v___y_4308_, v___y_4307_);
lean_dec_ref(v___x_4337_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4341_);
if (lean_obj_tag(v_a_4341_) == 0)
{
lean_dec_ref(v_a_4341_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v_ctx_4290_);
return v___x_4340_;
}
else
{
lean_object* v___x_4342_; 
lean_dec_ref(v_a_4341_);
lean_dec_ref(v___x_4340_);
v___x_4342_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4290_, v___y_4304_, v___y_4313_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
return v___x_4342_;
}
}
else
{
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v_ctx_4290_);
return v___x_4340_;
}
}
else
{
lean_object* v___x_4343_; 
lean_dec_ref(v_env_4320_);
v___x_4343_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4290_, v___y_4304_, v___y_4313_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
return v___x_4343_;
}
}
else
{
lean_object* v___x_4344_; 
lean_dec_ref(v_env_4320_);
v___x_4344_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4290_, v___y_4304_, v___y_4313_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
return v___x_4344_;
}
}
else
{
lean_object* v___x_4345_; 
lean_dec_ref(v_env_4320_);
v___x_4345_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4290_, v___y_4304_, v___y_4313_, v___y_4308_, v___y_4307_, v___y_4305_, v___y_4306_, v___y_4312_, v___y_4310_, v___y_4311_);
return v___x_4345_;
}
}
}
else
{
lean_dec_ref(v_env_4320_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4332_;
}
}
}
else
{
lean_dec(v_a_4323_);
lean_dec_ref(v_env_4320_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4327_;
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec_ref(v_env_4320_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
v_a_4346_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4321_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4321_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4315_);
lean_dec(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v_ctx_4290_);
return v___x_4316_;
}
}
v___jp_4354_:
{
lean_object* v___x_4364_; lean_object* v___f_4365_; lean_object* v___x_4366_; lean_object* v___f_4367_; uint8_t v___x_4368_; 
v___x_4364_ = lean_box(v_danglingDot_4356_);
lean_inc(v_id_4355_);
lean_inc_ref(v_ctx_4290_);
v___f_4365_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4365_, 0, v_ctx_4290_);
lean_closure_set(v___f_4365_, 1, v_id_4355_);
lean_closure_set(v___f_4365_, 2, v___x_4364_);
v___x_4366_ = lean_box(v_danglingDot_4356_);
lean_inc(v_id_4355_);
v___f_4367_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4367_, 0, v_id_4355_);
lean_closure_set(v___f_4367_, 1, v___x_4366_);
v___x_4368_ = l_Lean_Name_isAtomic(v_id_4355_);
if (v___x_4368_ == 0)
{
v___y_4304_ = v_id_4355_;
v___y_4305_ = v___y_4359_;
v___y_4306_ = v___y_4360_;
v___y_4307_ = v___y_4358_;
v___y_4308_ = v___y_4357_;
v___y_4309_ = v___f_4367_;
v___y_4310_ = v___y_4362_;
v___y_4311_ = v___y_4363_;
v___y_4312_ = v___y_4361_;
v___y_4313_ = v_danglingDot_4356_;
v___y_4314_ = v___f_4365_;
goto v___jp_4303_;
}
else
{
lean_object* v_lctx_4369_; lean_object* v_decls_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v_lctx_4369_ = lean_ctor_get(v___y_4360_, 2);
v_decls_4370_ = lean_ctor_get(v_lctx_4369_, 1);
v___x_4371_ = lean_box(0);
lean_inc_ref(v_decls_4370_);
v___x_4372_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_id_4355_, v_danglingDot_4356_, v_decls_4370_, v___x_4371_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
if (lean_obj_tag(v_a_4373_) == 0)
{
lean_dec_ref(v_a_4373_);
lean_dec_ref(v___f_4367_);
lean_dec_ref(v___f_4365_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v_id_4355_);
lean_dec_ref(v_ctx_4290_);
return v___x_4372_;
}
else
{
lean_dec_ref(v_a_4373_);
lean_dec_ref(v___x_4372_);
v___y_4304_ = v_id_4355_;
v___y_4305_ = v___y_4359_;
v___y_4306_ = v___y_4360_;
v___y_4307_ = v___y_4358_;
v___y_4308_ = v___y_4357_;
v___y_4309_ = v___f_4367_;
v___y_4310_ = v___y_4362_;
v___y_4311_ = v___y_4363_;
v___y_4312_ = v___y_4361_;
v___y_4313_ = v_danglingDot_4356_;
v___y_4314_ = v___f_4365_;
goto v___jp_4303_;
}
}
else
{
lean_dec_ref(v___f_4367_);
lean_dec_ref(v___f_4365_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v_id_4355_);
lean_dec_ref(v_ctx_4290_);
return v___x_4372_;
}
}
}
v___jp_4374_:
{
if (lean_obj_tag(v_hoverInfo_4293_) == 1)
{
lean_object* v_delta_4383_; lean_object* v_id_4384_; uint8_t v_danglingDot_4385_; 
v_delta_4383_ = lean_ctor_get(v_hoverInfo_4293_, 0);
lean_inc(v_delta_4383_);
lean_dec_ref(v_hoverInfo_4293_);
v_id_4384_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4375_, v_delta_4383_);
v_danglingDot_4385_ = 0;
v_id_4355_ = v_id_4384_;
v_danglingDot_4356_ = v_danglingDot_4385_;
v___y_4357_ = v___y_4376_;
v___y_4358_ = v___y_4377_;
v___y_4359_ = v___y_4378_;
v___y_4360_ = v___y_4379_;
v___y_4361_ = v___y_4380_;
v___y_4362_ = v___y_4381_;
v___y_4363_ = v___y_4382_;
goto v___jp_4354_;
}
else
{
lean_dec(v_hoverInfo_4293_);
v_id_4355_ = v_id_4375_;
v_danglingDot_4356_ = v_danglingDot_4294_;
v___y_4357_ = v___y_4376_;
v___y_4358_ = v___y_4377_;
v___y_4359_ = v___y_4378_;
v___y_4360_ = v___y_4379_;
v___y_4361_ = v___y_4380_;
v___y_4362_ = v___y_4381_;
v___y_4363_ = v___y_4382_;
goto v___jp_4354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4391_, lean_object* v_stx_4392_, lean_object* v_id_4393_, lean_object* v_hoverInfo_4394_, lean_object* v_danglingDot_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
uint8_t v_danglingDot_boxed_4404_; lean_object* v_res_4405_; 
v_danglingDot_boxed_4404_ = lean_unbox(v_danglingDot_4395_);
v_res_4405_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4391_, v_stx_4392_, v_id_4393_, v_hoverInfo_4394_, v_danglingDot_boxed_4404_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_);
lean_dec(v_stx_4392_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4406_, lean_object* v___x_4407_, lean_object* v_alias_4408_, lean_object* v_as_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4406_, v___x_4407_, v_alias_4408_, v_as_4409_, v___y_4410_, v___y_4411_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4419_, lean_object* v___x_4420_, lean_object* v_alias_4421_, lean_object* v_as_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4419_, v___x_4420_, v_alias_4421_, v_as_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v_alias_4421_);
lean_dec_ref(v_a_4419_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_id_4432_, uint8_t v_danglingDot_4433_, lean_object* v_a_4434_, lean_object* v___x_4435_, lean_object* v_as_4436_, lean_object* v_as_x27_4437_, lean_object* v_b_4438_, lean_object* v_a_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_id_4432_, v_danglingDot_4433_, v_a_4434_, v___x_4435_, v_as_4436_, v_as_x27_4437_, v_b_4438_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_id_4449_, lean_object* v_danglingDot_4450_, lean_object* v_a_4451_, lean_object* v___x_4452_, lean_object* v_as_4453_, lean_object* v_as_x27_4454_, lean_object* v_b_4455_, lean_object* v_a_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
uint8_t v_danglingDot_boxed_4465_; lean_object* v_res_4466_; 
v_danglingDot_boxed_4465_ = lean_unbox(v_danglingDot_4450_);
v_res_4466_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_id_4449_, v_danglingDot_boxed_4465_, v_a_4451_, v___x_4452_, v_as_4453_, v_as_x27_4454_, v_b_4455_, v_a_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v_as_4453_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_as_4467_, size_t v_sz_4468_, size_t v_i_4469_, lean_object* v_b_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_as_4467_, v_sz_4468_, v_i_4469_, v_b_4470_, v___y_4471_, v___y_4472_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_as_4480_, lean_object* v_sz_4481_, lean_object* v_i_4482_, lean_object* v_b_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
size_t v_sz_boxed_4492_; size_t v_i_boxed_4493_; lean_object* v_res_4494_; 
v_sz_boxed_4492_ = lean_unbox_usize(v_sz_4481_);
lean_dec(v_sz_4481_);
v_i_boxed_4493_ = lean_unbox_usize(v_i_4482_);
lean_dec(v_i_4482_);
v_res_4494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_as_4480_, v_sz_boxed_4492_, v_i_boxed_4493_, v_b_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec_ref(v_as_4480_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_a_4495_, lean_object* v___x_4496_, lean_object* v_id_4497_, uint8_t v_danglingDot_4498_, lean_object* v_as_4499_, lean_object* v_as_x27_4500_, lean_object* v_b_4501_, lean_object* v_a_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_a_4495_, v___x_4496_, v_id_4497_, v_danglingDot_4498_, v_as_x27_4500_, v_b_4501_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_a_4512_, lean_object* v___x_4513_, lean_object* v_id_4514_, lean_object* v_danglingDot_4515_, lean_object* v_as_4516_, lean_object* v_as_x27_4517_, lean_object* v_b_4518_, lean_object* v_a_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
uint8_t v_danglingDot_boxed_4528_; lean_object* v_res_4529_; 
v_danglingDot_boxed_4528_ = lean_unbox(v_danglingDot_4515_);
v_res_4529_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_a_4512_, v___x_4513_, v_id_4514_, v_danglingDot_boxed_4528_, v_as_4516_, v_as_x27_4517_, v_b_4518_, v_a_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v_as_4516_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4530_, lean_object* v_map_4531_, lean_object* v_f_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4531_, v_f_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4543_, lean_object* v_map_4544_, lean_object* v_f_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4543_, v_map_4544_, v_f_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14(lean_object* v_id_4556_, uint8_t v_danglingDot_4557_, lean_object* v_as_4558_, size_t v_sz_4559_, size_t v_i_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___redArg(v_id_4556_, v_danglingDot_4557_, v_as_4558_, v_sz_4559_, v_i_4560_, v_b_4561_, v___y_4562_, v___y_4563_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14___boxed(lean_object* v_id_4571_, lean_object* v_danglingDot_4572_, lean_object* v_as_4573_, lean_object* v_sz_4574_, lean_object* v_i_4575_, lean_object* v_b_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
uint8_t v_danglingDot_boxed_4585_; size_t v_sz_boxed_4586_; size_t v_i_boxed_4587_; lean_object* v_res_4588_; 
v_danglingDot_boxed_4585_ = lean_unbox(v_danglingDot_4572_);
v_sz_boxed_4586_ = lean_unbox_usize(v_sz_4574_);
lean_dec(v_sz_4574_);
v_i_boxed_4587_ = lean_unbox_usize(v_i_4575_);
lean_dec(v_i_4575_);
v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__8_spec__14(v_id_4571_, v_danglingDot_boxed_4585_, v_as_4573_, v_sz_boxed_4586_, v_i_boxed_4587_, v_b_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_as_4573_);
lean_dec(v_id_4571_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_map_4589_, lean_object* v_f_4590_, lean_object* v_init_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(v_f_4590_, v_map_4589_, v_init_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_map_4602_, lean_object* v_f_4603_, lean_object* v_init_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___redArg(v_map_4602_, v_f_4603_, v_init_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03c3_4615_, lean_object* v_00_u03b2_4616_, lean_object* v_map_4617_, lean_object* v_f_4618_, lean_object* v_init_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(v_f_4618_, v_map_4617_, v_init_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03c3_4630_, lean_object* v_00_u03b2_4631_, lean_object* v_map_4632_, lean_object* v_f_4633_, lean_object* v_init_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8(v_00_u03c3_4630_, v_00_u03b2_4631_, v_map_4632_, v_f_4633_, v_init_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14(lean_object* v_id_4645_, uint8_t v_danglingDot_4646_, lean_object* v_as_4647_, size_t v_sz_4648_, size_t v_i_4649_, lean_object* v_b_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___redArg(v_id_4645_, v_danglingDot_4646_, v_as_4647_, v_sz_4648_, v_i_4649_, v_b_4650_, v___y_4651_, v___y_4652_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14___boxed(lean_object* v_id_4660_, lean_object* v_danglingDot_4661_, lean_object* v_as_4662_, lean_object* v_sz_4663_, lean_object* v_i_4664_, lean_object* v_b_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
uint8_t v_danglingDot_boxed_4674_; size_t v_sz_boxed_4675_; size_t v_i_boxed_4676_; lean_object* v_res_4677_; 
v_danglingDot_boxed_4674_ = lean_unbox(v_danglingDot_4661_);
v_sz_boxed_4675_ = lean_unbox_usize(v_sz_4663_);
lean_dec(v_sz_4663_);
v_i_boxed_4676_ = lean_unbox_usize(v_i_4664_);
lean_dec(v_i_4664_);
v_res_4677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5_spec__7_spec__12_spec__14(v_id_4660_, v_danglingDot_boxed_4674_, v_as_4662_, v_sz_boxed_4675_, v_i_boxed_4676_, v_b_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec_ref(v_as_4662_);
lean_dec(v_id_4660_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12(lean_object* v_00_u03c3_4678_, lean_object* v_00_u03b1_4679_, lean_object* v_00_u03b2_4680_, lean_object* v_f_4681_, lean_object* v_x_4682_, lean_object* v_x_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v___x_4693_; 
v___x_4693_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___redArg(v_f_4681_, v_x_4682_, v_x_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03c3_4694_, lean_object* v_00_u03b1_4695_, lean_object* v_00_u03b2_4696_, lean_object* v_f_4697_, lean_object* v_x_4698_, lean_object* v_x_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12(v_00_u03c3_4694_, v_00_u03b1_4695_, v_00_u03b2_4696_, v_f_4697_, v_x_4698_, v_x_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17(lean_object* v_00_u03b1_4710_, lean_object* v_00_u03b2_4711_, lean_object* v_00_u03c3_4712_, lean_object* v_f_4713_, lean_object* v_as_4714_, size_t v_i_4715_, size_t v_stop_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___redArg(v_f_4713_, v_as_4714_, v_i_4715_, v_stop_4716_, v_b_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17___boxed(lean_object** _args){
lean_object* v_00_u03b1_4728_ = _args[0];
lean_object* v_00_u03b2_4729_ = _args[1];
lean_object* v_00_u03c3_4730_ = _args[2];
lean_object* v_f_4731_ = _args[3];
lean_object* v_as_4732_ = _args[4];
lean_object* v_i_4733_ = _args[5];
lean_object* v_stop_4734_ = _args[6];
lean_object* v_b_4735_ = _args[7];
lean_object* v___y_4736_ = _args[8];
lean_object* v___y_4737_ = _args[9];
lean_object* v___y_4738_ = _args[10];
lean_object* v___y_4739_ = _args[11];
lean_object* v___y_4740_ = _args[12];
lean_object* v___y_4741_ = _args[13];
lean_object* v___y_4742_ = _args[14];
lean_object* v___y_4743_ = _args[15];
lean_object* v___y_4744_ = _args[16];
_start:
{
size_t v_i_boxed_4745_; size_t v_stop_boxed_4746_; lean_object* v_res_4747_; 
v_i_boxed_4745_ = lean_unbox_usize(v_i_4733_);
lean_dec(v_i_4733_);
v_stop_boxed_4746_ = lean_unbox_usize(v_stop_4734_);
lean_dec(v_stop_4734_);
v_res_4747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__17(v_00_u03b1_4728_, v_00_u03b2_4729_, v_00_u03c3_4730_, v_f_4731_, v_as_4732_, v_i_boxed_4745_, v_stop_boxed_4746_, v_b_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
lean_dec_ref(v_as_4732_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18(lean_object* v_00_u03c3_4748_, lean_object* v_00_u03b1_4749_, lean_object* v_00_u03b2_4750_, lean_object* v_f_4751_, lean_object* v_keys_4752_, lean_object* v_vals_4753_, lean_object* v_heq_4754_, lean_object* v_i_4755_, lean_object* v_acc_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___redArg(v_f_4751_, v_keys_4752_, v_vals_4753_, v_i_4755_, v_acc_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18___boxed(lean_object** _args){
lean_object* v_00_u03c3_4767_ = _args[0];
lean_object* v_00_u03b1_4768_ = _args[1];
lean_object* v_00_u03b2_4769_ = _args[2];
lean_object* v_f_4770_ = _args[3];
lean_object* v_keys_4771_ = _args[4];
lean_object* v_vals_4772_ = _args[5];
lean_object* v_heq_4773_ = _args[6];
lean_object* v_i_4774_ = _args[7];
lean_object* v_acc_4775_ = _args[8];
lean_object* v___y_4776_ = _args[9];
lean_object* v___y_4777_ = _args[10];
lean_object* v___y_4778_ = _args[11];
lean_object* v___y_4779_ = _args[12];
lean_object* v___y_4780_ = _args[13];
lean_object* v___y_4781_ = _args[14];
lean_object* v___y_4782_ = _args[15];
lean_object* v___y_4783_ = _args[16];
lean_object* v___y_4784_ = _args[17];
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__8_spec__12_spec__18(v_00_u03c3_4767_, v_00_u03b1_4768_, v_00_u03b2_4769_, v_f_4770_, v_keys_4771_, v_vals_4772_, v_heq_4773_, v_i_4774_, v_acc_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
lean_dec_ref(v_vals_4772_);
lean_dec_ref(v_keys_4771_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4786_, lean_object* v_pos_4787_, lean_object* v_completionInfoPos_4788_, lean_object* v_ctx_4789_, lean_object* v_lctx_4790_, lean_object* v_stx_4791_, lean_object* v_id_4792_, lean_object* v_hoverInfo_4793_, uint8_t v_danglingDot_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4797_ = lean_box(v_danglingDot_4794_);
lean_inc_ref(v_ctx_4789_);
v___x_4798_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_4798_, 0, v_ctx_4789_);
lean_closure_set(v___x_4798_, 1, v_stx_4791_);
lean_closure_set(v___x_4798_, 2, v_id_4792_);
lean_closure_set(v___x_4798_, 3, v_hoverInfo_4793_);
lean_closure_set(v___x_4798_, 4, v___x_4797_);
v___x_4799_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4786_, v_pos_4787_, v_completionInfoPos_4788_, v_ctx_4789_, v_lctx_4790_, v___x_4798_, v_a_4795_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_4800_, lean_object* v_pos_4801_, lean_object* v_completionInfoPos_4802_, lean_object* v_ctx_4803_, lean_object* v_lctx_4804_, lean_object* v_stx_4805_, lean_object* v_id_4806_, lean_object* v_hoverInfo_4807_, lean_object* v_danglingDot_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
uint8_t v_danglingDot_boxed_4811_; lean_object* v_res_4812_; 
v_danglingDot_boxed_4811_ = lean_unbox(v_danglingDot_4808_);
v_res_4812_ = l_Lean_Server_Completion_idCompletion(v_uri_4800_, v_pos_4801_, v_completionInfoPos_4802_, v_ctx_4803_, v_lctx_4804_, v_stx_4805_, v_id_4806_, v_hoverInfo_4807_, v_danglingDot_boxed_4811_, v_a_4809_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_4813_, lean_object* v___y_4814_){
_start:
{
uint8_t v___x_4816_; 
v___x_4816_ = l_Lean_Expr_hasMVar(v_e_4813_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4817_, 0, v_e_4813_);
v___x_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4817_);
return v___x_4818_;
}
else
{
lean_object* v___x_4819_; lean_object* v_mctx_4820_; lean_object* v___x_4821_; lean_object* v_fst_4822_; lean_object* v_snd_4823_; lean_object* v___x_4824_; lean_object* v_cache_4825_; lean_object* v_zetaDeltaFVarIds_4826_; lean_object* v_postponed_4827_; lean_object* v_diag_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4838_; 
v___x_4819_ = lean_st_ref_get(v___y_4814_);
v_mctx_4820_ = lean_ctor_get(v___x_4819_, 0);
lean_inc_ref(v_mctx_4820_);
lean_dec(v___x_4819_);
v___x_4821_ = l_Lean_instantiateMVarsCore(v_mctx_4820_, v_e_4813_);
v_fst_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_fst_4822_);
v_snd_4823_ = lean_ctor_get(v___x_4821_, 1);
lean_inc(v_snd_4823_);
lean_dec_ref(v___x_4821_);
v___x_4824_ = lean_st_ref_take(v___y_4814_);
v_cache_4825_ = lean_ctor_get(v___x_4824_, 1);
v_zetaDeltaFVarIds_4826_ = lean_ctor_get(v___x_4824_, 2);
v_postponed_4827_ = lean_ctor_get(v___x_4824_, 3);
v_diag_4828_ = lean_ctor_get(v___x_4824_, 4);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v___x_4824_, 0);
lean_dec(v_unused_4839_);
v___x_4830_ = v___x_4824_;
v_isShared_4831_ = v_isSharedCheck_4838_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_diag_4828_);
lean_inc(v_postponed_4827_);
lean_inc(v_zetaDeltaFVarIds_4826_);
lean_inc(v_cache_4825_);
lean_dec(v___x_4824_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4838_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v_snd_4823_);
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_snd_4823_);
lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_cache_4825_);
lean_ctor_set(v_reuseFailAlloc_4837_, 2, v_zetaDeltaFVarIds_4826_);
lean_ctor_set(v_reuseFailAlloc_4837_, 3, v_postponed_4827_);
lean_ctor_set(v_reuseFailAlloc_4837_, 4, v_diag_4828_);
v___x_4833_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4834_ = lean_st_ref_set(v___y_4814_, v___x_4833_);
v___x_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4835_, 0, v_fst_4822_);
v___x_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
return v___x_4836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4840_, v___y_4841_);
lean_dec(v___y_4841_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4844_, v___y_4849_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_4864_, lean_object* v_declName_4865_, lean_object* v_decl_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_unnormedTypeName_4875_; uint8_t v___x_4876_; 
v_unnormedTypeName_4875_ = l_Lean_Name_getPrefix(v_declName_4865_);
v___x_4876_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_4875_, v_a_4864_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec_ref(v_decl_4866_);
lean_dec(v_declName_4865_);
v___x_4877_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
else
{
lean_object* v___x_4879_; lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4945_; 
v___x_4879_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_4865_, v___y_4873_);
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4945_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4945_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
if (lean_obj_tag(v_a_4880_) == 1)
{
lean_object* v_val_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4940_; 
lean_del_object(v___x_4882_);
v_val_4884_ = lean_ctor_get(v_a_4880_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v_a_4880_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4886_ = v_a_4880_;
v_isShared_4887_ = v_isSharedCheck_4940_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_val_4884_);
lean_dec(v_a_4880_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4940_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v_info_4888_; lean_object* v_kind_4889_; lean_object* v_tags_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v_info_4888_ = lean_ctor_get(v_decl_4866_, 0);
lean_inc_ref(v_info_4888_);
v_kind_4889_ = lean_ctor_get(v_decl_4866_, 1);
lean_inc_ref(v_kind_4889_);
v_tags_4890_ = lean_ctor_get(v_decl_4866_, 2);
lean_inc_ref(v_tags_4890_);
lean_dec_ref(v_decl_4866_);
v___x_4891_ = l_Lean_Name_getPrefix(v_val_4884_);
lean_dec(v_val_4884_);
lean_inc(v___y_4873_);
lean_inc_ref(v___y_4872_);
lean_inc(v___y_4871_);
lean_inc_ref(v___y_4870_);
v___x_4892_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_4891_, v_info_4888_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4931_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4895_ = v___x_4892_;
v_isShared_4896_ = v_isSharedCheck_4931_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4892_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4931_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
uint8_t v___x_4897_; 
v___x_4897_ = lean_unbox(v_a_4893_);
lean_dec(v_a_4893_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; lean_object* v___x_4900_; 
lean_dec_ref(v_tags_4890_);
lean_dec_ref(v_kind_4889_);
lean_dec_ref(v_info_4888_);
lean_del_object(v___x_4886_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
v___x_4898_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 0, v___x_4898_);
v___x_4900_ = v___x_4895_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4898_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
else
{
lean_object* v___x_4902_; 
lean_del_object(v___x_4895_);
lean_inc(v___y_4873_);
lean_inc_ref(v___y_4872_);
lean_inc(v___y_4871_);
lean_inc_ref(v___y_4870_);
v___x_4902_ = lean_apply_5(v_kind_4889_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, lean_box(0));
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4904_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
lean_inc(v_a_4903_);
lean_dec_ref(v___x_4902_);
v___x_4904_ = lean_apply_5(v_tags_4890_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, lean_box(0));
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4911_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
lean_inc(v_a_4905_);
lean_dec_ref(v___x_4904_);
v___x_4906_ = l_Lean_ConstantInfo_name(v_info_4888_);
lean_dec_ref(v_info_4888_);
v___x_4907_ = l_Lean_Name_getString_x21(v___x_4906_);
v___x_4908_ = lean_box(0);
v___x_4909_ = l_Lean_Name_str___override(v___x_4908_, v___x_4907_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set_tag(v___x_4886_, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4906_);
v___x_4911_ = v___x_4886_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4906_);
v___x_4911_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
uint8_t v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_unbox(v_a_4903_);
lean_dec(v_a_4903_);
v___x_4913_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_4909_, v___x_4911_, v___x_4912_, v_a_4905_, v___y_4867_, v___y_4868_);
return v___x_4913_;
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_dec(v_a_4903_);
lean_dec_ref(v_info_4888_);
lean_del_object(v___x_4886_);
v_a_4915_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4904_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4904_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_dec_ref(v_tags_4890_);
lean_dec_ref(v_info_4888_);
lean_del_object(v___x_4886_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
v_a_4923_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4902_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4902_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
}
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_dec_ref(v_tags_4890_);
lean_dec_ref(v_kind_4889_);
lean_dec_ref(v_info_4888_);
lean_del_object(v___x_4886_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
v_a_4932_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4892_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4892_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
}
else
{
lean_object* v___x_4941_; lean_object* v___x_4943_; 
lean_dec(v_a_4880_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec_ref(v_decl_4866_);
v___x_4941_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4941_);
v___x_4943_ = v___x_4882_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4941_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_4946_, lean_object* v_declName_4947_, lean_object* v_decl_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_4946_, v_declName_4947_, v_decl_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_a_4971_; lean_object* v___y_4975_; uint8_t v___y_4976_; lean_object* v___y_4986_; lean_object* v_a_4987_; lean_object* v___x_4990_; 
lean_inc(v___y_4965_);
lean_inc_ref(v___y_4964_);
lean_inc(v___y_4963_);
lean_inc_ref(v___y_4962_);
v___x_4990_ = lean_infer_type(v_expr_4958_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4992_; lean_object* v_a_4993_; lean_object* v_a_4994_; lean_object* v___x_4995_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref(v___x_4990_);
v___x_4992_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_4991_, v___y_4963_);
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref(v___x_4992_);
v_a_4994_ = lean_ctor_get(v_a_4993_, 0);
lean_inc(v_a_4994_);
lean_dec(v_a_4993_);
lean_inc(v___y_4965_);
lean_inc_ref(v___y_4964_);
lean_inc(v___y_4963_);
lean_inc_ref(v___y_4962_);
v___x_4995_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_4994_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref(v___x_4995_);
v_a_4971_ = v_a_4996_;
goto v___jp_4970_;
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
v_a_4997_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4995_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4995_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
lean_inc(v_a_4997_);
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
v___y_4986_ = v___x_5002_;
v_a_4987_ = v_a_4997_;
goto v___jp_4985_;
}
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
v_a_5005_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4990_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4990_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
lean_inc(v_a_5005_);
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
v___y_4986_ = v___x_5010_;
v_a_4987_ = v_a_5005_;
goto v___jp_4985_;
}
}
}
v___jp_4967_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
v___jp_4970_:
{
if (lean_obj_tag(v_a_4971_) == 0)
{
lean_object* v___f_4972_; lean_object* v___x_4973_; 
v___f_4972_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_4972_, 0, v_a_4971_);
v___x_4973_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_4972_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
return v___x_4973_;
}
else
{
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
goto v___jp_4967_;
}
}
v___jp_4974_:
{
if (v___y_4976_ == 0)
{
lean_dec_ref(v___y_4975_);
goto v___jp_4967_;
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
v_a_4977_ = lean_ctor_get(v___y_4975_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___y_4975_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___y_4975_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___y_4975_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
v___jp_4985_:
{
uint8_t v___x_4988_; 
v___x_4988_ = l_Lean_Exception_isInterrupt(v_a_4987_);
if (v___x_4988_ == 0)
{
uint8_t v___x_4989_; 
v___x_4989_ = l_Lean_Exception_isRuntime(v_a_4987_);
v___y_4975_ = v___y_4986_;
v___y_4976_ = v___x_4989_;
goto v___jp_4974_;
}
else
{
lean_dec_ref(v_a_4987_);
v___y_4975_ = v___y_4986_;
v___y_4976_ = v___x_4988_;
goto v___jp_4974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5023_, lean_object* v_pos_5024_, lean_object* v_completionInfoPos_5025_, lean_object* v_ctx_5026_, lean_object* v_info_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v_lctx_5030_; lean_object* v_expr_5031_; lean_object* v___f_5032_; lean_object* v___x_5033_; 
v_lctx_5030_ = lean_ctor_get(v_info_5027_, 1);
lean_inc_ref(v_lctx_5030_);
v_expr_5031_ = lean_ctor_get(v_info_5027_, 3);
lean_inc_ref(v_expr_5031_);
lean_dec_ref(v_info_5027_);
v___f_5032_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5032_, 0, v_expr_5031_);
v___x_5033_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5023_, v_pos_5024_, v_completionInfoPos_5025_, v_ctx_5026_, v_lctx_5030_, v___f_5032_, v_a_5028_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5034_, lean_object* v_pos_5035_, lean_object* v_completionInfoPos_5036_, lean_object* v_ctx_5037_, lean_object* v_info_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l_Lean_Server_Completion_dotCompletion(v_uri_5034_, v_pos_5035_, v_completionInfoPos_5036_, v_ctx_5037_, v_info_5038_, v_a_5039_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5042_, uint8_t v___x_5043_, lean_object* v_id_5044_, lean_object* v_declName_5045_, lean_object* v_decl_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v___x_5058_; uint8_t v___x_5059_; 
v___x_5058_ = l_Lean_Name_getPrefix(v_declName_5045_);
lean_inc(v___x_5042_);
v___x_5059_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5058_, v___x_5042_);
if (v___x_5059_ == 0)
{
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_decl_5046_);
lean_dec(v_declName_5045_);
lean_dec(v___x_5042_);
goto v___jp_5055_;
}
else
{
if (v___x_5043_ == 0)
{
lean_object* v___x_5060_; lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5157_; 
v___x_5060_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5045_, v___y_5053_);
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5157_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5157_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
if (lean_obj_tag(v_a_5061_) == 1)
{
lean_object* v_val_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5152_; 
lean_del_object(v___x_5063_);
v_val_5065_ = lean_ctor_get(v_a_5061_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v_a_5061_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5067_ = v_a_5061_;
v_isShared_5068_ = v_isSharedCheck_5152_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_val_5065_);
lean_dec(v_a_5061_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5152_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v_info_5069_; lean_object* v_kind_5070_; lean_object* v_tags_5071_; lean_object* v___x_5072_; 
v_info_5069_ = lean_ctor_get(v_decl_5046_, 0);
lean_inc_ref(v_info_5069_);
v_kind_5070_ = lean_ctor_get(v_decl_5046_, 1);
lean_inc_ref(v_kind_5070_);
v_tags_5071_ = lean_ctor_get(v_decl_5046_, 2);
lean_inc_ref(v_tags_5071_);
lean_dec_ref(v_decl_5046_);
lean_inc(v___y_5053_);
lean_inc_ref(v___y_5052_);
lean_inc(v___y_5051_);
lean_inc_ref(v___y_5050_);
v___x_5072_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5042_, v_info_5069_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5143_; 
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5075_ = v___x_5072_;
v_isShared_5076_ = v_isSharedCheck_5143_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5072_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5143_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
uint8_t v___x_5077_; 
v___x_5077_ = lean_unbox(v_a_5073_);
lean_dec(v_a_5073_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; lean_object* v___x_5080_; 
lean_dec_ref(v_tags_5071_);
lean_dec_ref(v_kind_5070_);
lean_dec_ref(v_info_5069_);
lean_del_object(v___x_5067_);
lean_dec(v_val_5065_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
v___x_5078_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5076_ == 0)
{
lean_ctor_set(v___x_5075_, 0, v___x_5078_);
v___x_5080_ = v___x_5075_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
else
{
lean_object* v___x_5082_; 
lean_del_object(v___x_5075_);
lean_inc(v___y_5053_);
lean_inc_ref(v___y_5052_);
lean_inc(v___y_5051_);
lean_inc_ref(v___y_5050_);
v___x_5082_ = lean_apply_5(v_kind_5070_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, lean_box(0));
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5084_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref(v___x_5082_);
lean_inc(v___y_5053_);
v___x_5084_ = lean_apply_5(v_tags_5071_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, lean_box(0));
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; uint8_t v___x_5086_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref(v___x_5084_);
v___x_5086_ = l_Lean_Name_isAnonymous(v_id_5044_);
if (v___x_5086_ == 0)
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5108_; 
lean_del_object(v___x_5067_);
v___x_5087_ = l_Lean_Name_getPrefix(v_val_5065_);
v___x_5088_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5087_, v_id_5044_, v___x_5086_, v_val_5065_, v___y_5053_);
lean_dec(v___y_5053_);
lean_dec(v___x_5087_);
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5091_ = v___x_5088_;
v_isShared_5092_ = v_isSharedCheck_5108_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5088_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5108_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
if (lean_obj_tag(v_a_5089_) == 1)
{
lean_object* v_val_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5103_; 
lean_del_object(v___x_5091_);
v_val_5093_ = lean_ctor_get(v_a_5089_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_a_5089_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5095_ = v_a_5089_;
v_isShared_5096_ = v_isSharedCheck_5103_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_val_5093_);
lean_dec(v_a_5089_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5103_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5097_; lean_object* v___x_5099_; 
v___x_5097_ = l_Lean_ConstantInfo_name(v_info_5069_);
lean_dec_ref(v_info_5069_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set_tag(v___x_5095_, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5097_);
v___x_5099_ = v___x_5095_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5097_);
v___x_5099_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
uint8_t v___x_5100_; lean_object* v___x_5101_; 
v___x_5100_ = lean_unbox(v_a_5083_);
lean_dec(v_a_5083_);
v___x_5101_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5093_, v___x_5099_, v___x_5100_, v_a_5085_, v___y_5047_, v___y_5048_);
return v___x_5101_;
}
}
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5106_; 
lean_dec(v_a_5089_);
lean_dec(v_a_5085_);
lean_dec(v_a_5083_);
lean_dec_ref(v_info_5069_);
v___x_5104_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v___x_5104_);
v___x_5106_ = v___x_5091_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5104_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
else
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5114_; 
lean_dec(v_val_5065_);
lean_dec(v___y_5053_);
v___x_5109_ = l_Lean_ConstantInfo_name(v_info_5069_);
lean_dec_ref(v_info_5069_);
v___x_5110_ = l_Lean_Name_getString_x21(v___x_5109_);
v___x_5111_ = lean_box(0);
v___x_5112_ = l_Lean_Name_str___override(v___x_5111_, v___x_5110_);
if (v_isShared_5068_ == 0)
{
lean_ctor_set_tag(v___x_5067_, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5109_);
v___x_5114_ = v___x_5067_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v___x_5109_);
v___x_5114_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
uint8_t v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5124_; 
v___x_5115_ = lean_unbox(v_a_5083_);
lean_dec(v_a_5083_);
v___x_5116_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5112_, v___x_5114_, v___x_5115_, v_a_5085_, v___y_5047_, v___y_5048_);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5124_ == 0)
{
lean_object* v_unused_5125_; 
v_unused_5125_ = lean_ctor_get(v___x_5116_, 0);
lean_dec(v_unused_5125_);
v___x_5118_ = v___x_5116_;
v_isShared_5119_ = v_isSharedCheck_5124_;
goto v_resetjp_5117_;
}
else
{
lean_dec(v___x_5116_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5124_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5120_; lean_object* v___x_5122_; 
v___x_5120_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 0, v___x_5120_);
v___x_5122_ = v___x_5118_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5120_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec(v_a_5083_);
lean_dec_ref(v_info_5069_);
lean_del_object(v___x_5067_);
lean_dec(v_val_5065_);
lean_dec(v___y_5053_);
v_a_5127_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5084_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5084_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_dec_ref(v_tags_5071_);
lean_dec_ref(v_info_5069_);
lean_del_object(v___x_5067_);
lean_dec(v_val_5065_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
v_a_5135_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5082_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5082_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
}
}
else
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5151_; 
lean_dec_ref(v_tags_5071_);
lean_dec_ref(v_kind_5070_);
lean_dec_ref(v_info_5069_);
lean_del_object(v___x_5067_);
lean_dec(v_val_5065_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
v_a_5144_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5146_ = v___x_5072_;
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5072_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5149_; 
if (v_isShared_5147_ == 0)
{
v___x_5149_ = v___x_5146_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
}
}
}
}
}
else
{
lean_object* v___x_5153_; lean_object* v___x_5155_; 
lean_dec(v_a_5061_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_decl_5046_);
lean_dec(v___x_5042_);
v___x_5153_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 0, v___x_5153_);
v___x_5155_ = v___x_5063_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
else
{
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_decl_5046_);
lean_dec(v_declName_5045_);
lean_dec(v___x_5042_);
goto v___jp_5055_;
}
}
v___jp_5055_:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5056_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
return v___x_5057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5158_, lean_object* v___x_5159_, lean_object* v_id_5160_, lean_object* v_declName_5161_, lean_object* v_decl_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_){
_start:
{
uint8_t v___x_23150__boxed_5171_; lean_object* v_res_5172_; 
v___x_23150__boxed_5171_ = lean_unbox(v___x_5159_);
v_res_5172_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5158_, v___x_23150__boxed_5171_, v_id_5160_, v_declName_5161_, v_decl_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v_id_5160_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5173_, lean_object* v_id_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5173_) == 1)
{
lean_object* v_val_5183_; lean_object* v___x_5184_; 
v_val_5183_ = lean_ctor_get(v_expectedType_x3f_5173_, 0);
lean_inc(v_val_5183_);
lean_dec_ref(v_expectedType_x3f_5173_);
lean_inc(v___y_5181_);
lean_inc_ref(v___y_5180_);
lean_inc(v___y_5179_);
lean_inc_ref(v___y_5178_);
v___x_5184_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5183_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5200_; 
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5187_ = v___x_5184_;
v_isShared_5188_ = v_isSharedCheck_5200_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5184_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5200_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5189_ = lean_array_get_size(v_a_5185_);
v___x_5190_ = lean_unsigned_to_nat(0u);
v___x_5191_ = lean_nat_dec_eq(v___x_5189_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___f_5194_; lean_object* v___x_5195_; 
lean_del_object(v___x_5187_);
v___x_5192_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5185_);
lean_dec(v_a_5185_);
v___x_5193_ = lean_box(v___x_5191_);
v___f_5194_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 13, 3);
lean_closure_set(v___f_5194_, 0, v___x_5192_);
lean_closure_set(v___f_5194_, 1, v___x_5193_);
lean_closure_set(v___f_5194_, 2, v_id_5174_);
v___x_5195_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5194_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
return v___x_5195_;
}
else
{
lean_object* v___x_5196_; lean_object* v___x_5198_; 
lean_dec(v_a_5185_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v_id_5174_);
v___x_5196_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5188_ == 0)
{
lean_ctor_set(v___x_5187_, 0, v___x_5196_);
v___x_5198_ = v___x_5187_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v___x_5196_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5208_; 
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v_id_5174_);
v_a_5201_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5203_ = v___x_5184_;
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5184_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5206_; 
if (v_isShared_5204_ == 0)
{
v___x_5206_ = v___x_5203_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5201_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
else
{
lean_object* v___x_5209_; lean_object* v___x_5210_; 
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v_id_5174_);
lean_dec(v_expectedType_x3f_5173_);
v___x_5209_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5209_);
return v___x_5210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5211_, lean_object* v_id_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5211_, v_id_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5222_, lean_object* v_pos_5223_, lean_object* v_completionInfoPos_5224_, lean_object* v_ctx_5225_, lean_object* v_lctx_5226_, lean_object* v_id_5227_, lean_object* v_expectedType_x3f_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v___y_5231_; lean_object* v___x_5232_; 
v___y_5231_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5231_, 0, v_expectedType_x3f_5228_);
lean_closure_set(v___y_5231_, 1, v_id_5227_);
v___x_5232_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5222_, v_pos_5223_, v_completionInfoPos_5224_, v_ctx_5225_, v_lctx_5226_, v___y_5231_, v_a_5229_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5233_, lean_object* v_pos_5234_, lean_object* v_completionInfoPos_5235_, lean_object* v_ctx_5236_, lean_object* v_lctx_5237_, lean_object* v_id_5238_, lean_object* v_expectedType_x3f_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5233_, v_pos_5234_, v_completionInfoPos_5235_, v_ctx_5236_, v_lctx_5237_, v_id_5238_, v_expectedType_x3f_5239_, v_a_5240_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5249_, lean_object* v_as_5250_, size_t v_sz_5251_, size_t v_i_5252_, lean_object* v_b_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_a_5258_; uint8_t v___x_5262_; 
v___x_5262_ = lean_usize_dec_lt(v_i_5252_, v_sz_5251_);
if (v___x_5262_ == 0)
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5263_, 0, v_b_5253_);
v___x_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5263_);
return v___x_5264_;
}
else
{
lean_object* v___x_5265_; lean_object* v_a_5266_; 
v___x_5265_ = lean_box(0);
v_a_5266_ = lean_array_uget_borrowed(v_as_5250_, v_i_5252_);
if (lean_obj_tag(v_a_5266_) == 1)
{
lean_object* v_str_5267_; uint8_t v___x_5268_; 
v_str_5267_ = lean_ctor_get(v_a_5266_, 1);
v___x_5268_ = l_String_charactersIn(v___y_5249_, v_str_5267_);
if (v___x_5268_ == 0)
{
v_a_5258_ = v___x_5265_;
goto v___jp_5257_;
}
else
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5270_ = lean_box(0);
v___x_5271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5267_);
v___x_5272_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5272_, 0, v_str_5267_);
lean_ctor_set(v___x_5272_, 1, v___x_5269_);
lean_ctor_set(v___x_5272_, 2, v___x_5270_);
lean_ctor_set(v___x_5272_, 3, v___x_5271_);
lean_ctor_set(v___x_5272_, 4, v___x_5270_);
lean_ctor_set(v___x_5272_, 5, v___x_5270_);
lean_ctor_set(v___x_5272_, 6, v___x_5270_);
lean_ctor_set(v___x_5272_, 7, v___x_5270_);
v___x_5273_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5272_, v___x_5270_, v___y_5254_, v___y_5255_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_a_5274_);
if (lean_obj_tag(v_a_5274_) == 0)
{
lean_dec_ref(v_a_5274_);
return v___x_5273_;
}
else
{
lean_dec_ref(v_a_5274_);
lean_dec_ref(v___x_5273_);
v_a_5258_ = v___x_5265_;
goto v___jp_5257_;
}
}
else
{
return v___x_5273_;
}
}
}
else
{
v_a_5258_ = v___x_5265_;
goto v___jp_5257_;
}
}
v___jp_5257_:
{
size_t v___x_5259_; size_t v___x_5260_; 
v___x_5259_ = ((size_t)1ULL);
v___x_5260_ = lean_usize_add(v_i_5252_, v___x_5259_);
v_i_5252_ = v___x_5260_;
v_b_5253_ = v_a_5258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5275_, lean_object* v_as_5276_, lean_object* v_sz_5277_, lean_object* v_i_5278_, lean_object* v_b_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
size_t v_sz_boxed_5283_; size_t v_i_boxed_5284_; lean_object* v_res_5285_; 
v_sz_boxed_5283_ = lean_unbox_usize(v_sz_5277_);
lean_dec(v_sz_5277_);
v_i_boxed_5284_ = lean_unbox_usize(v_i_5278_);
lean_dec(v_i_5278_);
v_res_5285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5275_, v_as_5276_, v_sz_boxed_5283_, v_i_boxed_5284_, v_b_5279_, v___y_5280_, v___y_5281_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec_ref(v_as_5276_);
lean_dec_ref(v___y_5275_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v___x_5296_; lean_object* v_env_5297_; uint8_t v___x_5298_; lean_object* v_fieldNames_5299_; lean_object* v___x_5300_; size_t v_sz_5301_; size_t v___x_5302_; lean_object* v___x_5303_; 
v___x_5296_ = lean_st_ref_get(v___y_5294_);
v_env_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc_ref(v_env_5297_);
lean_dec(v___x_5296_);
v___x_5298_ = 0;
v_fieldNames_5299_ = l_Lean_getStructureFieldsFlattened(v_env_5297_, v_structName_5286_, v___x_5298_);
v___x_5300_ = lean_box(0);
v_sz_5301_ = lean_array_size(v_fieldNames_5299_);
v___x_5302_ = ((size_t)0ULL);
v___x_5303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5287_, v_fieldNames_5299_, v_sz_5301_, v___x_5302_, v___x_5300_, v___y_5288_, v___y_5289_);
lean_dec_ref(v_fieldNames_5299_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
if (lean_obj_tag(v_a_5304_) == 0)
{
lean_dec_ref(v_a_5304_);
return v___x_5303_;
}
else
{
lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5312_; 
lean_dec_ref(v_a_5304_);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5312_ == 0)
{
lean_object* v_unused_5313_; 
v_unused_5313_ = lean_ctor_get(v___x_5303_, 0);
lean_dec(v_unused_5313_);
v___x_5306_ = v___x_5303_;
v_isShared_5307_ = v_isSharedCheck_5312_;
goto v_resetjp_5305_;
}
else
{
lean_dec(v___x_5303_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5312_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5308_; lean_object* v___x_5310_; 
v___x_5308_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 0, v___x_5308_);
v___x_5310_ = v___x_5306_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v___x_5308_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
else
{
return v___x_5303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec_ref(v___y_5315_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5326_, lean_object* v_pos_5327_, lean_object* v_completionInfoPos_5328_, lean_object* v_ctx_5329_, lean_object* v_lctx_5330_, lean_object* v_id_5331_, lean_object* v_structName_5332_, lean_object* v_a_5333_){
_start:
{
lean_object* v___y_5336_; 
if (lean_obj_tag(v_id_5331_) == 0)
{
lean_object* v___x_5339_; 
v___x_5339_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5336_ = v___x_5339_;
goto v___jp_5335_;
}
else
{
lean_object* v_val_5340_; uint8_t v___x_5341_; lean_object* v___x_5342_; 
v_val_5340_ = lean_ctor_get(v_id_5331_, 0);
lean_inc(v_val_5340_);
lean_dec_ref(v_id_5331_);
v___x_5341_ = 1;
v___x_5342_ = l_Lean_Name_toString(v_val_5340_, v___x_5341_);
v___y_5336_ = v___x_5342_;
goto v___jp_5335_;
}
v___jp_5335_:
{
lean_object* v___f_5337_; lean_object* v___x_5338_; 
v___f_5337_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5337_, 0, v_structName_5332_);
lean_closure_set(v___f_5337_, 1, v___y_5336_);
v___x_5338_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5326_, v_pos_5327_, v_completionInfoPos_5328_, v_ctx_5329_, v_lctx_5330_, v___f_5337_, v_a_5333_);
return v___x_5338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5343_, lean_object* v_pos_5344_, lean_object* v_completionInfoPos_5345_, lean_object* v_ctx_5346_, lean_object* v_lctx_5347_, lean_object* v_id_5348_, lean_object* v_structName_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5343_, v_pos_5344_, v_completionInfoPos_5345_, v_ctx_5346_, v_lctx_5347_, v_id_5348_, v_structName_5349_, v_a_5350_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5353_, lean_object* v_as_5354_, size_t v_sz_5355_, size_t v_i_5356_, lean_object* v_b_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v___x_5366_; 
v___x_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5353_, v_as_5354_, v_sz_5355_, v_i_5356_, v_b_5357_, v___y_5358_, v___y_5359_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5367_, lean_object* v_as_5368_, lean_object* v_sz_5369_, lean_object* v_i_5370_, lean_object* v_b_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
size_t v_sz_boxed_5380_; size_t v_i_boxed_5381_; lean_object* v_res_5382_; 
v_sz_boxed_5380_ = lean_unbox_usize(v_sz_5369_);
lean_dec(v_sz_5369_);
v_i_boxed_5381_ = lean_unbox_usize(v_i_5370_);
lean_dec(v_i_5370_);
v_res_5382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5367_, v_as_5368_, v_sz_boxed_5380_, v_i_boxed_5381_, v_b_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec_ref(v_as_5368_);
lean_dec_ref(v___y_5367_);
return v_res_5382_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0(void){
_start:
{
uint32_t v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = 32;
v___x_5384_ = l_Char_utf8Size(v___x_5383_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5385_, lean_object* v_caps_5386_, lean_object* v_mkItem_5387_, lean_object* v_ctx_5388_, lean_object* v_stx_5389_, uint8_t v_snd_5390_, lean_object* v_x_5391_, lean_object* v_____s_5392_){
_start:
{
lean_object* v_fst_5393_; lean_object* v_snd_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5447_; 
v_fst_5393_ = lean_ctor_get(v_x_5391_, 0);
v_snd_5394_ = lean_ctor_get(v_x_5391_, 1);
v_isSharedCheck_5447_ = !lean_is_exclusive(v_x_5391_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5396_ = v_x_5391_;
v_isShared_5397_ = v_isSharedCheck_5447_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_snd_5394_);
lean_inc(v_fst_5393_);
lean_dec(v_x_5391_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5447_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___y_5399_; uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___y_5406_; lean_object* v___y_5407_; uint8_t v___x_5436_; 
v___x_5403_ = 1;
lean_inc(v_fst_5393_);
v___x_5404_ = l_Lean_Name_toString(v_fst_5393_, v___x_5403_);
v___x_5436_ = l_String_charactersIn(v_fst_5385_, v___x_5404_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5439_; 
lean_dec_ref(v___x_5404_);
lean_del_object(v___x_5396_);
lean_dec(v_snd_5394_);
lean_dec(v_fst_5393_);
lean_dec_ref(v_ctx_5388_);
lean_dec_ref(v_mkItem_5387_);
v___x_5439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5439_, 0, v_____s_5392_);
return v___x_5439_;
}
else
{
lean_object* v_textDocument_x3f_5440_; 
v_textDocument_x3f_5440_ = lean_ctor_get(v_caps_5386_, 0);
if (lean_obj_tag(v_textDocument_x3f_5440_) == 0)
{
goto v___jp_5437_;
}
else
{
lean_object* v_val_5441_; lean_object* v_completion_x3f_5442_; 
v_val_5441_ = lean_ctor_get(v_textDocument_x3f_5440_, 0);
v_completion_x3f_5442_ = lean_ctor_get(v_val_5441_, 0);
if (lean_obj_tag(v_completion_x3f_5442_) == 0)
{
goto v___jp_5437_;
}
else
{
lean_object* v_val_5443_; 
v_val_5443_ = lean_ctor_get(v_completion_x3f_5442_, 0);
if (lean_obj_tag(v_val_5443_) == 0)
{
goto v___jp_5437_;
}
else
{
lean_object* v_val_5444_; 
v_val_5444_ = lean_ctor_get(v_val_5443_, 0);
if (lean_obj_tag(v_val_5444_) == 0)
{
goto v___jp_5437_;
}
else
{
lean_object* v_val_5445_; uint8_t v___x_5446_; 
v_val_5445_ = lean_ctor_get(v_val_5444_, 0);
v___x_5446_ = lean_unbox(v_val_5445_);
if (v___x_5446_ == 0)
{
goto v___jp_5437_;
}
else
{
goto v___jp_5425_;
}
}
}
}
}
}
v___jp_5398_:
{
lean_object* v___x_5400_; lean_object* v_items_5401_; lean_object* v___x_5402_; 
v___x_5400_ = lean_apply_3(v_mkItem_5387_, v_fst_5393_, v_snd_5394_, v___y_5399_);
v_items_5401_ = lean_array_push(v_____s_5392_, v___x_5400_);
v___x_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5402_, 0, v_items_5401_);
return v___x_5402_;
}
v___jp_5405_:
{
lean_object* v_toCommandContextInfo_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5422_; 
v_toCommandContextInfo_5408_ = lean_ctor_get(v_ctx_5388_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v_ctx_5388_);
if (v_isSharedCheck_5422_ == 0)
{
lean_object* v_unused_5423_; lean_object* v_unused_5424_; 
v_unused_5423_ = lean_ctor_get(v_ctx_5388_, 2);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_ctx_5388_, 1);
lean_dec(v_unused_5424_);
v___x_5410_ = v_ctx_5388_;
v_isShared_5411_ = v_isSharedCheck_5422_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_toCommandContextInfo_5408_);
lean_dec(v_ctx_5388_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5422_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v_fileMap_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v_range_5416_; 
v_fileMap_5412_ = lean_ctor_get(v_toCommandContextInfo_5408_, 2);
lean_inc_ref(v_fileMap_5412_);
lean_dec_ref(v_toCommandContextInfo_5408_);
lean_inc_ref(v_fileMap_5412_);
v___x_5413_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5412_, v___y_5406_);
lean_dec(v___y_5406_);
v___x_5414_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5412_, v___y_5407_);
lean_dec(v___y_5407_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5414_);
lean_ctor_set(v___x_5396_, 0, v___x_5413_);
v_range_5416_ = v___x_5396_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5413_);
lean_ctor_set(v_reuseFailAlloc_5421_, 1, v___x_5414_);
v_range_5416_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5418_; 
lean_inc_ref(v_range_5416_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 2, v_range_5416_);
lean_ctor_set(v___x_5410_, 1, v_range_5416_);
lean_ctor_set(v___x_5410_, 0, v___x_5404_);
v___x_5418_ = v___x_5410_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5404_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_range_5416_);
lean_ctor_set(v_reuseFailAlloc_5420_, 2, v_range_5416_);
v___x_5418_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
lean_object* v___x_5419_; 
v___x_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
v___y_5399_ = v___x_5419_;
goto v___jp_5398_;
}
}
}
}
v___jp_5425_:
{
uint8_t v___x_5426_; lean_object* v___x_5427_; 
v___x_5426_ = 0;
v___x_5427_ = l_Lean_Syntax_getRange_x3f(v_stx_5389_, v___x_5426_);
if (lean_obj_tag(v___x_5427_) == 1)
{
lean_object* v_val_5428_; 
v_val_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_val_5428_);
lean_dec_ref(v___x_5427_);
if (v_snd_5390_ == 0)
{
lean_object* v_start_5429_; lean_object* v_stop_5430_; 
v_start_5429_ = lean_ctor_get(v_val_5428_, 0);
lean_inc(v_start_5429_);
v_stop_5430_ = lean_ctor_get(v_val_5428_, 1);
lean_inc(v_stop_5430_);
lean_dec(v_val_5428_);
v___y_5406_ = v_start_5429_;
v___y_5407_ = v_stop_5430_;
goto v___jp_5405_;
}
else
{
lean_object* v_start_5431_; lean_object* v_stop_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v_start_5431_ = lean_ctor_get(v_val_5428_, 0);
lean_inc(v_start_5431_);
v_stop_5432_ = lean_ctor_get(v_val_5428_, 1);
lean_inc(v_stop_5432_);
lean_dec(v_val_5428_);
v___x_5433_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5434_ = lean_nat_add(v_stop_5432_, v___x_5433_);
lean_dec(v_stop_5432_);
v___y_5406_ = v_start_5431_;
v___y_5407_ = v___x_5434_;
goto v___jp_5405_;
}
}
else
{
lean_object* v___x_5435_; 
lean_dec(v___x_5427_);
lean_dec_ref(v___x_5404_);
lean_del_object(v___x_5396_);
lean_dec_ref(v_ctx_5388_);
v___x_5435_ = lean_box(0);
v___y_5399_ = v___x_5435_;
goto v___jp_5398_;
}
}
v___jp_5437_:
{
if (v___x_5436_ == 0)
{
goto v___jp_5425_;
}
else
{
lean_object* v___x_5438_; 
lean_dec_ref(v___x_5404_);
lean_del_object(v___x_5396_);
lean_dec_ref(v_ctx_5388_);
v___x_5438_ = lean_box(0);
v___y_5399_ = v___x_5438_;
goto v___jp_5398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5448_, lean_object* v_caps_5449_, lean_object* v_mkItem_5450_, lean_object* v_ctx_5451_, lean_object* v_stx_5452_, lean_object* v_snd_5453_, lean_object* v_x_5454_, lean_object* v_____s_5455_){
_start:
{
uint8_t v_snd_1079__boxed_5456_; lean_object* v_res_5457_; 
v_snd_1079__boxed_5456_ = lean_unbox(v_snd_5453_);
v_res_5457_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5448_, v_caps_5449_, v_mkItem_5450_, v_ctx_5451_, v_stx_5452_, v_snd_1079__boxed_5456_, v_x_5454_, v_____s_5455_);
lean_dec(v_stx_5452_);
lean_dec_ref(v_caps_5449_);
lean_dec_ref(v_fst_5448_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5459_, lean_object* v_entries_5460_, lean_object* v_stx_5461_, lean_object* v_caps_5462_, lean_object* v_ctx_5463_, lean_object* v_mkItem_5464_){
_start:
{
lean_object* v_fst_5466_; uint8_t v_snd_5467_; uint8_t v___x_5472_; lean_object* v___x_5473_; 
v___x_5472_ = 0;
v___x_5473_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5461_, v___x_5472_, v___x_5472_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v___x_5474_; 
v___x_5474_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5466_ = v___x_5474_;
v_snd_5467_ = v___x_5472_;
goto v___jp_5465_;
}
else
{
lean_object* v_val_5475_; lean_object* v_str_5476_; lean_object* v_startPos_5477_; lean_object* v_stopPos_5478_; uint8_t v___y_5480_; uint8_t v___x_5482_; 
v_val_5475_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_val_5475_);
lean_dec_ref(v___x_5473_);
v_str_5476_ = lean_ctor_get(v_val_5475_, 0);
lean_inc_ref(v_str_5476_);
v_startPos_5477_ = lean_ctor_get(v_val_5475_, 1);
lean_inc(v_startPos_5477_);
v_stopPos_5478_ = lean_ctor_get(v_val_5475_, 2);
lean_inc(v_stopPos_5478_);
lean_dec(v_val_5475_);
v___x_5482_ = lean_string_utf8_at_end(v_str_5476_, v_stopPos_5478_);
if (v___x_5482_ == 0)
{
uint32_t v___x_5483_; uint32_t v___x_5484_; uint8_t v___x_5485_; 
v___x_5483_ = lean_string_utf8_get(v_str_5476_, v_stopPos_5478_);
v___x_5484_ = 46;
v___x_5485_ = lean_uint32_dec_eq(v___x_5483_, v___x_5484_);
if (v___x_5485_ == 0)
{
v___y_5480_ = v___x_5485_;
goto v___jp_5479_;
}
else
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5486_ = lean_string_utf8_extract(v_str_5476_, v_startPos_5477_, v_stopPos_5478_);
lean_dec(v_stopPos_5478_);
lean_dec(v_startPos_5477_);
lean_dec_ref(v_str_5476_);
v___x_5487_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5488_ = lean_string_append(v___x_5486_, v___x_5487_);
v_fst_5466_ = v___x_5488_;
v_snd_5467_ = v___x_5485_;
goto v___jp_5465_;
}
}
else
{
v___y_5480_ = v___x_5472_;
goto v___jp_5479_;
}
v___jp_5479_:
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_string_utf8_extract(v_str_5476_, v_startPos_5477_, v_stopPos_5478_);
lean_dec(v_stopPos_5478_);
lean_dec(v_startPos_5477_);
lean_dec_ref(v_str_5476_);
v_fst_5466_ = v___x_5481_;
v_snd_5467_ = v___y_5480_;
goto v___jp_5465_;
}
}
v___jp_5465_:
{
lean_object* v___x_5468_; lean_object* v___f_5469_; lean_object* v_items_5470_; lean_object* v___x_5471_; 
v___x_5468_ = lean_box(v_snd_5467_);
v___f_5469_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5469_, 0, v_fst_5466_);
lean_closure_set(v___f_5469_, 1, v_caps_5462_);
lean_closure_set(v___f_5469_, 2, v_mkItem_5464_);
lean_closure_set(v___f_5469_, 3, v_ctx_5463_);
lean_closure_set(v___f_5469_, 4, v_stx_5461_);
lean_closure_set(v___f_5469_, 5, v___x_5468_);
v_items_5470_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5471_ = lean_apply_4(v_inst_5459_, lean_box(0), v_entries_5460_, v_items_5470_, v___f_5469_);
return v___x_5471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5489_, lean_object* v_00_u03b1_5490_, lean_object* v_inst_5491_, lean_object* v_entries_5492_, lean_object* v_stx_5493_, lean_object* v_caps_5494_, lean_object* v_ctx_5495_, lean_object* v_mkItem_5496_){
_start:
{
lean_object* v___x_5497_; 
v___x_5497_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5491_, v_entries_5492_, v_stx_5493_, v_caps_5494_, v_ctx_5495_, v_mkItem_5496_);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v_options_5503_, lean_object* v_completionInfoPos_5504_, lean_object* v_uri_5505_, lean_object* v_pos_5506_, lean_object* v_name_5507_, lean_object* v_decl_5508_, lean_object* v_textEdit_x3f_5509_){
_start:
{
lean_object* v_defValue_5510_; lean_object* v_descr_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5537_; 
v_defValue_5510_ = lean_ctor_get(v_decl_5508_, 2);
v_descr_5511_ = lean_ctor_get(v_decl_5508_, 3);
v_isSharedCheck_5537_ = !lean_is_exclusive(v_decl_5508_);
if (v_isSharedCheck_5537_ == 0)
{
lean_object* v_unused_5538_; lean_object* v_unused_5539_; 
v_unused_5538_ = lean_ctor_get(v_decl_5508_, 1);
lean_dec(v_unused_5538_);
v_unused_5539_ = lean_ctor_get(v_decl_5508_, 0);
lean_dec(v_unused_5539_);
v___x_5513_ = v_decl_5508_;
v_isShared_5514_ = v_isSharedCheck_5537_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_descr_5511_);
lean_inc(v_defValue_5510_);
lean_dec(v_decl_5508_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5537_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v_map_5515_; uint8_t v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___y_5520_; lean_object* v___x_5535_; 
v_map_5515_ = lean_ctor_get(v_options_5503_, 0);
v___x_5516_ = 1;
lean_inc(v_name_5507_);
v___x_5517_ = l_Lean_Name_toString(v_name_5507_, v___x_5516_);
v___x_5518_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5515_, v_name_5507_);
lean_dec(v_name_5507_);
if (lean_obj_tag(v___x_5535_) == 0)
{
v___y_5520_ = v_defValue_5510_;
goto v___jp_5519_;
}
else
{
if (lean_obj_tag(v___x_5535_) == 0)
{
v___y_5520_ = v_defValue_5510_;
goto v___jp_5519_;
}
else
{
lean_object* v_val_5536_; 
lean_dec_ref(v_defValue_5510_);
v_val_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_val_5536_);
lean_dec_ref(v___x_5535_);
v___y_5520_ = v_val_5536_;
goto v___jp_5519_;
}
}
v___jp_5519_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5531_; 
v___x_5521_ = lean_data_value_to_string(v___y_5520_);
v___x_5522_ = lean_string_append(v___x_5518_, v___x_5521_);
lean_dec_ref(v___x_5521_);
v___x_5523_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5524_ = lean_string_append(v___x_5522_, v___x_5523_);
v___x_5525_ = lean_string_append(v___x_5524_, v_descr_5511_);
lean_dec_ref(v_descr_5511_);
v___x_5526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5525_);
v___x_5527_ = lean_box(0);
v___x_5528_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5529_, 0, v_completionInfoPos_5504_);
if (v_isShared_5514_ == 0)
{
lean_ctor_set(v___x_5513_, 3, v___x_5527_);
lean_ctor_set(v___x_5513_, 2, v___x_5529_);
lean_ctor_set(v___x_5513_, 1, v_pos_5506_);
lean_ctor_set(v___x_5513_, 0, v_uri_5505_);
v___x_5531_ = v___x_5513_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_uri_5505_);
lean_ctor_set(v_reuseFailAlloc_5534_, 1, v_pos_5506_);
lean_ctor_set(v_reuseFailAlloc_5534_, 2, v___x_5529_);
lean_ctor_set(v_reuseFailAlloc_5534_, 3, v___x_5527_);
v___x_5531_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5531_);
v___x_5533_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5533_, 0, v___x_5517_);
lean_ctor_set(v___x_5533_, 1, v___x_5526_);
lean_ctor_set(v___x_5533_, 2, v___x_5527_);
lean_ctor_set(v___x_5533_, 3, v___x_5528_);
lean_ctor_set(v___x_5533_, 4, v_textEdit_x3f_5509_);
lean_ctor_set(v___x_5533_, 5, v___x_5527_);
lean_ctor_set(v___x_5533_, 6, v___x_5532_);
lean_ctor_set(v___x_5533_, 7, v___x_5527_);
return v___x_5533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v_options_5540_, lean_object* v_completionInfoPos_5541_, lean_object* v_uri_5542_, lean_object* v_pos_5543_, lean_object* v_name_5544_, lean_object* v_decl_5545_, lean_object* v_textEdit_x3f_5546_){
_start:
{
lean_object* v_res_5547_; 
v_res_5547_ = l_Lean_Server_Completion_optionCompletion___lam__0(v_options_5540_, v_completionInfoPos_5541_, v_uri_5542_, v_pos_5543_, v_name_5544_, v_decl_5545_, v_textEdit_x3f_5546_);
lean_dec_ref(v_options_5540_);
return v_res_5547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5548_, lean_object* v_stx_5549_, lean_object* v_ctx_5550_, uint8_t v_snd_5551_, lean_object* v_fst_5552_, lean_object* v_caps_5553_, lean_object* v_init_5554_, lean_object* v_x_5555_){
_start:
{
if (lean_obj_tag(v_x_5555_) == 0)
{
lean_object* v_k_5556_; lean_object* v_v_5557_; lean_object* v_l_5558_; lean_object* v_r_5559_; lean_object* v___x_5560_; lean_object* v_a_5561_; lean_object* v___y_5563_; uint8_t v___x_5567_; lean_object* v___x_5568_; lean_object* v___y_5570_; lean_object* v___y_5571_; uint8_t v___x_5590_; 
v_k_5556_ = lean_ctor_get(v_x_5555_, 1);
lean_inc(v_k_5556_);
v_v_5557_ = lean_ctor_get(v_x_5555_, 2);
lean_inc(v_v_5557_);
v_l_5558_ = lean_ctor_get(v_x_5555_, 3);
lean_inc(v_l_5558_);
v_r_5559_ = lean_ctor_get(v_x_5555_, 4);
lean_inc(v_r_5559_);
lean_dec_ref(v_x_5555_);
lean_inc_ref(v_ctx_5550_);
lean_inc_ref(v_mkItem_5548_);
v___x_5560_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5548_, v_stx_5549_, v_ctx_5550_, v_snd_5551_, v_fst_5552_, v_caps_5553_, v_init_5554_, v_l_5558_);
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
lean_inc(v_a_5561_);
v___x_5567_ = 1;
lean_inc(v_k_5556_);
v___x_5568_ = l_Lean_Name_toString(v_k_5556_, v___x_5567_);
v___x_5590_ = l_String_charactersIn(v_fst_5552_, v___x_5568_);
if (v___x_5590_ == 0)
{
lean_object* v_a_5593_; 
lean_dec_ref(v___x_5568_);
lean_dec(v_a_5561_);
lean_dec(v_v_5557_);
lean_dec(v_k_5556_);
v_a_5593_ = lean_ctor_get(v___x_5560_, 0);
lean_inc(v_a_5593_);
lean_dec_ref(v___x_5560_);
v_init_5554_ = v_a_5593_;
v_x_5555_ = v_r_5559_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5595_; 
lean_dec_ref(v___x_5560_);
v_textDocument_x3f_5595_ = lean_ctor_get(v_caps_5553_, 0);
if (lean_obj_tag(v_textDocument_x3f_5595_) == 0)
{
goto v___jp_5591_;
}
else
{
lean_object* v_val_5596_; lean_object* v_completion_x3f_5597_; 
v_val_5596_ = lean_ctor_get(v_textDocument_x3f_5595_, 0);
v_completion_x3f_5597_ = lean_ctor_get(v_val_5596_, 0);
if (lean_obj_tag(v_completion_x3f_5597_) == 0)
{
goto v___jp_5591_;
}
else
{
lean_object* v_val_5598_; 
v_val_5598_ = lean_ctor_get(v_completion_x3f_5597_, 0);
if (lean_obj_tag(v_val_5598_) == 0)
{
goto v___jp_5591_;
}
else
{
lean_object* v_val_5599_; 
v_val_5599_ = lean_ctor_get(v_val_5598_, 0);
if (lean_obj_tag(v_val_5599_) == 0)
{
goto v___jp_5591_;
}
else
{
lean_object* v_val_5600_; uint8_t v___x_5601_; 
v_val_5600_ = lean_ctor_get(v_val_5599_, 0);
v___x_5601_ = lean_unbox(v_val_5600_);
if (v___x_5601_ == 0)
{
goto v___jp_5591_;
}
else
{
goto v___jp_5579_;
}
}
}
}
}
}
v___jp_5562_:
{
lean_object* v___x_5564_; lean_object* v_items_5565_; 
lean_inc_ref(v_mkItem_5548_);
v___x_5564_ = lean_apply_3(v_mkItem_5548_, v_k_5556_, v_v_5557_, v___y_5563_);
v_items_5565_ = lean_array_push(v_a_5561_, v___x_5564_);
v_init_5554_ = v_items_5565_;
v_x_5555_ = v_r_5559_;
goto _start;
}
v___jp_5569_:
{
lean_object* v_toCommandContextInfo_5572_; lean_object* v_fileMap_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v_range_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
v_toCommandContextInfo_5572_ = lean_ctor_get(v_ctx_5550_, 0);
v_fileMap_5573_ = lean_ctor_get(v_toCommandContextInfo_5572_, 2);
lean_inc_ref(v_fileMap_5573_);
v___x_5574_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5573_, v___y_5570_);
lean_dec(v___y_5570_);
lean_inc_ref(v_fileMap_5573_);
v___x_5575_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5573_, v___y_5571_);
lean_dec(v___y_5571_);
v_range_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5576_, 0, v___x_5574_);
lean_ctor_set(v_range_5576_, 1, v___x_5575_);
lean_inc_ref(v_range_5576_);
v___x_5577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5577_, 0, v___x_5568_);
lean_ctor_set(v___x_5577_, 1, v_range_5576_);
lean_ctor_set(v___x_5577_, 2, v_range_5576_);
v___x_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5578_, 0, v___x_5577_);
v___y_5563_ = v___x_5578_;
goto v___jp_5562_;
}
v___jp_5579_:
{
uint8_t v___x_5580_; lean_object* v___x_5581_; 
v___x_5580_ = 0;
v___x_5581_ = l_Lean_Syntax_getRange_x3f(v_stx_5549_, v___x_5580_);
if (lean_obj_tag(v___x_5581_) == 1)
{
lean_object* v_val_5582_; 
v_val_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_val_5582_);
lean_dec_ref(v___x_5581_);
if (v_snd_5551_ == 0)
{
lean_object* v_start_5583_; lean_object* v_stop_5584_; 
v_start_5583_ = lean_ctor_get(v_val_5582_, 0);
lean_inc(v_start_5583_);
v_stop_5584_ = lean_ctor_get(v_val_5582_, 1);
lean_inc(v_stop_5584_);
lean_dec(v_val_5582_);
v___y_5570_ = v_start_5583_;
v___y_5571_ = v_stop_5584_;
goto v___jp_5569_;
}
else
{
lean_object* v_start_5585_; lean_object* v_stop_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; 
v_start_5585_ = lean_ctor_get(v_val_5582_, 0);
lean_inc(v_start_5585_);
v_stop_5586_ = lean_ctor_get(v_val_5582_, 1);
lean_inc(v_stop_5586_);
lean_dec(v_val_5582_);
v___x_5587_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5588_ = lean_nat_add(v_stop_5586_, v___x_5587_);
lean_dec(v_stop_5586_);
v___y_5570_ = v_start_5585_;
v___y_5571_ = v___x_5588_;
goto v___jp_5569_;
}
}
else
{
lean_object* v___x_5589_; 
lean_dec(v___x_5581_);
lean_dec_ref(v___x_5568_);
v___x_5589_ = lean_box(0);
v___y_5563_ = v___x_5589_;
goto v___jp_5562_;
}
}
v___jp_5591_:
{
if (v___x_5590_ == 0)
{
goto v___jp_5579_;
}
else
{
lean_object* v___x_5592_; 
lean_dec_ref(v___x_5568_);
v___x_5592_ = lean_box(0);
v___y_5563_ = v___x_5592_;
goto v___jp_5562_;
}
}
}
else
{
lean_object* v___x_5602_; 
lean_dec_ref(v_ctx_5550_);
lean_dec_ref(v_mkItem_5548_);
v___x_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5602_, 0, v_init_5554_);
return v___x_5602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5603_, lean_object* v_stx_5604_, lean_object* v_ctx_5605_, lean_object* v_snd_5606_, lean_object* v_fst_5607_, lean_object* v_caps_5608_, lean_object* v_init_5609_, lean_object* v_x_5610_){
_start:
{
uint8_t v_snd_1463__boxed_5611_; lean_object* v_res_5612_; 
v_snd_1463__boxed_5611_ = lean_unbox(v_snd_5606_);
v_res_5612_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5603_, v_stx_5604_, v_ctx_5605_, v_snd_1463__boxed_5611_, v_fst_5607_, v_caps_5608_, v_init_5609_, v_x_5610_);
lean_dec_ref(v_caps_5608_);
lean_dec_ref(v_fst_5607_);
lean_dec(v_stx_5604_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5613_, lean_object* v_stx_5614_, lean_object* v_caps_5615_, lean_object* v_ctx_5616_, lean_object* v_mkItem_5617_){
_start:
{
lean_object* v_fst_5619_; uint8_t v_snd_5620_; uint8_t v___x_5624_; lean_object* v___x_5625_; 
v___x_5624_ = 0;
v___x_5625_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5614_, v___x_5624_, v___x_5624_);
if (lean_obj_tag(v___x_5625_) == 0)
{
lean_object* v___x_5626_; 
v___x_5626_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5619_ = v___x_5626_;
v_snd_5620_ = v___x_5624_;
goto v___jp_5618_;
}
else
{
lean_object* v_val_5627_; lean_object* v_str_5628_; lean_object* v_startPos_5629_; lean_object* v_stopPos_5630_; uint8_t v___y_5632_; uint8_t v___x_5634_; 
v_val_5627_ = lean_ctor_get(v___x_5625_, 0);
lean_inc(v_val_5627_);
lean_dec_ref(v___x_5625_);
v_str_5628_ = lean_ctor_get(v_val_5627_, 0);
lean_inc_ref(v_str_5628_);
v_startPos_5629_ = lean_ctor_get(v_val_5627_, 1);
lean_inc(v_startPos_5629_);
v_stopPos_5630_ = lean_ctor_get(v_val_5627_, 2);
lean_inc(v_stopPos_5630_);
lean_dec(v_val_5627_);
v___x_5634_ = lean_string_utf8_at_end(v_str_5628_, v_stopPos_5630_);
if (v___x_5634_ == 0)
{
uint32_t v___x_5635_; uint32_t v___x_5636_; uint8_t v___x_5637_; 
v___x_5635_ = lean_string_utf8_get(v_str_5628_, v_stopPos_5630_);
v___x_5636_ = 46;
v___x_5637_ = lean_uint32_dec_eq(v___x_5635_, v___x_5636_);
if (v___x_5637_ == 0)
{
v___y_5632_ = v___x_5637_;
goto v___jp_5631_;
}
else
{
lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5638_ = lean_string_utf8_extract(v_str_5628_, v_startPos_5629_, v_stopPos_5630_);
lean_dec(v_stopPos_5630_);
lean_dec(v_startPos_5629_);
lean_dec_ref(v_str_5628_);
v___x_5639_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5640_ = lean_string_append(v___x_5638_, v___x_5639_);
v_fst_5619_ = v___x_5640_;
v_snd_5620_ = v___x_5637_;
goto v___jp_5618_;
}
}
else
{
v___y_5632_ = v___x_5624_;
goto v___jp_5631_;
}
v___jp_5631_:
{
lean_object* v___x_5633_; 
v___x_5633_ = lean_string_utf8_extract(v_str_5628_, v_startPos_5629_, v_stopPos_5630_);
lean_dec(v_stopPos_5630_);
lean_dec(v_startPos_5629_);
lean_dec_ref(v_str_5628_);
v_fst_5619_ = v___x_5633_;
v_snd_5620_ = v___y_5632_;
goto v___jp_5618_;
}
}
v___jp_5618_:
{
lean_object* v_items_5621_; lean_object* v___x_5622_; lean_object* v_a_5623_; 
v_items_5621_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5622_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5617_, v_stx_5614_, v_ctx_5616_, v_snd_5620_, v_fst_5619_, v_caps_5615_, v_items_5621_, v_entries_5613_);
lean_dec_ref(v_fst_5619_);
v_a_5623_ = lean_ctor_get(v___x_5622_, 0);
lean_inc(v_a_5623_);
lean_dec_ref(v___x_5622_);
return v_a_5623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object* v_entries_5641_, lean_object* v_stx_5642_, lean_object* v_caps_5643_, lean_object* v_ctx_5644_, lean_object* v_mkItem_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_entries_5641_, v_stx_5642_, v_caps_5643_, v_ctx_5644_, v_mkItem_5645_);
lean_dec_ref(v_caps_5643_);
lean_dec(v_stx_5642_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object* v_completionInfoPos_5647_, lean_object* v_uri_5648_, lean_object* v_pos_5649_, lean_object* v_stx_5650_, lean_object* v_caps_5651_, lean_object* v_ctx_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_){
_start:
{
lean_object* v___x_5658_; 
v___x_5658_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5671_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5661_ = v___x_5658_;
v_isShared_5662_ = v_isSharedCheck_5671_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5658_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5671_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v_options_5663_; lean_object* v___f_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5669_; 
v_options_5663_ = lean_ctor_get(v___y_5655_, 2);
lean_inc_ref(v_options_5663_);
lean_dec_ref(v___y_5655_);
v___f_5664_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5664_, 0, v_options_5663_);
lean_closure_set(v___f_5664_, 1, v_completionInfoPos_5647_);
lean_closure_set(v___f_5664_, 2, v_uri_5648_);
lean_closure_set(v___f_5664_, 3, v_pos_5649_);
v___x_5665_ = lean_unsigned_to_nat(1u);
v___x_5666_ = l_Lean_Syntax_getArg(v_stx_5650_, v___x_5665_);
v___x_5667_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_a_5659_, v___x_5666_, v_caps_5651_, v_ctx_5652_, v___f_5664_);
lean_dec(v___x_5666_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v___x_5667_);
v___x_5669_ = v___x_5661_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5667_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
else
{
lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5684_; 
lean_dec_ref(v_ctx_5652_);
lean_dec_ref(v_pos_5649_);
lean_dec_ref(v_uri_5648_);
lean_dec(v_completionInfoPos_5647_);
v_a_5672_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5674_ = v___x_5658_;
v_isShared_5675_ = v_isSharedCheck_5684_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_dec(v___x_5658_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5684_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v_ref_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5682_; 
v_ref_5676_ = lean_ctor_get(v___y_5655_, 5);
lean_inc(v_ref_5676_);
lean_dec_ref(v___y_5655_);
v___x_5677_ = lean_io_error_to_string(v_a_5672_);
v___x_5678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
v___x_5679_ = l_Lean_MessageData_ofFormat(v___x_5678_);
v___x_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5680_, 0, v_ref_5676_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 0, v___x_5680_);
v___x_5682_ = v___x_5674_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v___x_5680_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object* v_completionInfoPos_5685_, lean_object* v_uri_5686_, lean_object* v_pos_5687_, lean_object* v_stx_5688_, lean_object* v_caps_5689_, lean_object* v_ctx_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5685_, v_uri_5686_, v_pos_5687_, v_stx_5688_, v_caps_5689_, v_ctx_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
lean_dec(v___y_5694_);
lean_dec(v___y_5692_);
lean_dec_ref(v___y_5691_);
lean_dec_ref(v_caps_5689_);
lean_dec(v_stx_5688_);
return v_res_5696_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__0(void){
_start:
{
lean_object* v___x_5697_; 
v___x_5697_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5697_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1(void){
_start:
{
lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5698_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__0, &l_Lean_Server_Completion_optionCompletion___closed__0_once, _init_l_Lean_Server_Completion_optionCompletion___closed__0);
v___x_5699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
return v___x_5699_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2(void){
_start:
{
lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; 
v___x_5700_ = lean_unsigned_to_nat(32u);
v___x_5701_ = lean_mk_empty_array_with_capacity(v___x_5700_);
v___x_5702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5701_);
return v___x_5702_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3(void){
_start:
{
size_t v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___x_5703_ = ((size_t)5ULL);
v___x_5704_ = lean_unsigned_to_nat(0u);
v___x_5705_ = lean_unsigned_to_nat(32u);
v___x_5706_ = lean_mk_empty_array_with_capacity(v___x_5705_);
v___x_5707_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__2, &l_Lean_Server_Completion_optionCompletion___closed__2_once, _init_l_Lean_Server_Completion_optionCompletion___closed__2);
v___x_5708_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5708_, 0, v___x_5707_);
lean_ctor_set(v___x_5708_, 1, v___x_5706_);
lean_ctor_set(v___x_5708_, 2, v___x_5704_);
lean_ctor_set(v___x_5708_, 3, v___x_5704_);
lean_ctor_set_usize(v___x_5708_, 4, v___x_5703_);
return v___x_5708_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4(void){
_start:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; 
v___x_5709_ = lean_box(1);
v___x_5710_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__3, &l_Lean_Server_Completion_optionCompletion___closed__3_once, _init_l_Lean_Server_Completion_optionCompletion___closed__3);
v___x_5711_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__1, &l_Lean_Server_Completion_optionCompletion___closed__1_once, _init_l_Lean_Server_Completion_optionCompletion___closed__1);
v___x_5712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
lean_ctor_set(v___x_5712_, 1, v___x_5710_);
lean_ctor_set(v___x_5712_, 2, v___x_5709_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* v_uri_5713_, lean_object* v_pos_5714_, lean_object* v_completionInfoPos_5715_, lean_object* v_ctx_5716_, lean_object* v_stx_5717_, lean_object* v_caps_5718_){
_start:
{
lean_object* v___f_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; 
lean_inc_ref(v_ctx_5716_);
v___f_5720_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__1___boxed), 11, 6);
lean_closure_set(v___f_5720_, 0, v_completionInfoPos_5715_);
lean_closure_set(v___f_5720_, 1, v_uri_5713_);
lean_closure_set(v___f_5720_, 2, v_pos_5714_);
lean_closure_set(v___f_5720_, 3, v_stx_5717_);
lean_closure_set(v___f_5720_, 4, v_caps_5718_);
lean_closure_set(v___f_5720_, 5, v_ctx_5716_);
v___x_5721_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5722_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5716_, v___x_5721_, v___f_5720_);
return v___x_5722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* v_uri_5723_, lean_object* v_pos_5724_, lean_object* v_completionInfoPos_5725_, lean_object* v_ctx_5726_, lean_object* v_stx_5727_, lean_object* v_caps_5728_, lean_object* v_a_5729_){
_start:
{
lean_object* v_res_5730_; 
v_res_5730_ = l_Lean_Server_Completion_optionCompletion(v_uri_5723_, v_pos_5724_, v_completionInfoPos_5725_, v_ctx_5726_, v_stx_5727_, v_caps_5728_);
return v_res_5730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object* v_completionInfoPos_5740_, lean_object* v_uri_5741_, lean_object* v_pos_5742_, lean_object* v_name_5743_, lean_object* v_explan_5744_, lean_object* v_textEdit_x3f_5745_){
_start:
{
lean_object* v_metadata_5746_; lean_object* v_removedVersion_x3f_5747_; uint8_t v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; uint8_t v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; 
v_metadata_5746_ = lean_ctor_get(v_explan_5744_, 1);
v_removedVersion_x3f_5747_ = lean_ctor_get(v_metadata_5746_, 2);
v___x_5748_ = 1;
v___x_5749_ = l_Lean_Name_toString(v_name_5743_, v___x_5748_);
v___x_5750_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1));
v___x_5751_ = 1;
v___x_5752_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_5744_);
v___x_5753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
lean_ctor_set_uint8(v___x_5753_, sizeof(void*)*1, v___x_5751_);
v___x_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
v___x_5755_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5756_ = lean_box(0);
v___x_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5757_, 0, v_completionInfoPos_5740_);
v___x_5758_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5758_, 0, v_uri_5741_);
lean_ctor_set(v___x_5758_, 1, v_pos_5742_);
lean_ctor_set(v___x_5758_, 2, v___x_5757_);
lean_ctor_set(v___x_5758_, 3, v___x_5756_);
v___x_5759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5758_);
if (lean_obj_tag(v_removedVersion_x3f_5747_) == 0)
{
lean_object* v___x_5760_; 
v___x_5760_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5749_);
lean_ctor_set(v___x_5760_, 1, v___x_5750_);
lean_ctor_set(v___x_5760_, 2, v___x_5754_);
lean_ctor_set(v___x_5760_, 3, v___x_5755_);
lean_ctor_set(v___x_5760_, 4, v_textEdit_x3f_5745_);
lean_ctor_set(v___x_5760_, 5, v___x_5756_);
lean_ctor_set(v___x_5760_, 6, v___x_5759_);
lean_ctor_set(v___x_5760_, 7, v___x_5756_);
return v___x_5760_;
}
else
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3));
v___x_5762_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5749_);
lean_ctor_set(v___x_5762_, 1, v___x_5750_);
lean_ctor_set(v___x_5762_, 2, v___x_5754_);
lean_ctor_set(v___x_5762_, 3, v___x_5755_);
lean_ctor_set(v___x_5762_, 4, v_textEdit_x3f_5745_);
lean_ctor_set(v___x_5762_, 5, v___x_5756_);
lean_ctor_set(v___x_5762_, 6, v___x_5759_);
lean_ctor_set(v___x_5762_, 7, v___x_5761_);
return v___x_5762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object* v_completionInfoPos_5763_, lean_object* v_uri_5764_, lean_object* v_pos_5765_, lean_object* v_name_5766_, lean_object* v_explan_5767_, lean_object* v_textEdit_x3f_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Lean_Server_Completion_errorNameCompletion___lam__0(v_completionInfoPos_5763_, v_uri_5764_, v_pos_5765_, v_name_5766_, v_explan_5767_, v_textEdit_x3f_5768_);
lean_dec_ref(v_explan_5767_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object* v_init_5770_, lean_object* v_x_5771_){
_start:
{
if (lean_obj_tag(v_x_5771_) == 0)
{
lean_object* v_k_5772_; lean_object* v_v_5773_; lean_object* v_l_5774_; lean_object* v_r_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; 
v_k_5772_ = lean_ctor_get(v_x_5771_, 1);
v_v_5773_ = lean_ctor_get(v_x_5771_, 2);
v_l_5774_ = lean_ctor_get(v_x_5771_, 3);
v_r_5775_ = lean_ctor_get(v_x_5771_, 4);
v___x_5776_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5770_, v_l_5774_);
lean_inc(v_v_5773_);
lean_inc(v_k_5772_);
v___x_5777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5777_, 0, v_k_5772_);
lean_ctor_set(v___x_5777_, 1, v_v_5773_);
v___x_5778_ = lean_array_push(v___x_5776_, v___x_5777_);
v_init_5770_ = v___x_5778_;
v_x_5771_ = v_r_5775_;
goto _start;
}
else
{
return v_init_5770_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5780_, lean_object* v_x_5781_){
_start:
{
lean_object* v_res_5782_; 
v_res_5782_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5780_, v_x_5781_);
lean_dec(v_x_5781_);
return v_res_5782_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_5783_, lean_object* v_e_5784_, lean_object* v_e_x27_5785_){
_start:
{
lean_object* v_fst_5786_; lean_object* v_fst_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; uint8_t v___x_5790_; 
v_fst_5786_ = lean_ctor_get(v_e_5784_, 0);
lean_inc(v_fst_5786_);
lean_dec_ref(v_e_5784_);
v_fst_5787_ = lean_ctor_get(v_e_x27_5785_, 0);
lean_inc(v_fst_5787_);
lean_dec_ref(v_e_x27_5785_);
v___x_5788_ = l_Lean_Name_toString(v_fst_5786_, v___x_5783_);
v___x_5789_ = l_Lean_Name_toString(v_fst_5787_, v___x_5783_);
v___x_5790_ = lean_string_dec_lt(v___x_5788_, v___x_5789_);
lean_dec_ref(v___x_5789_);
lean_dec_ref(v___x_5788_);
return v___x_5790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_5791_, lean_object* v_e_5792_, lean_object* v_e_x27_5793_){
_start:
{
uint8_t v___x_1494__boxed_5794_; uint8_t v_res_5795_; lean_object* v_r_5796_; 
v___x_1494__boxed_5794_ = lean_unbox(v___x_5791_);
v_res_5795_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1494__boxed_5794_, v_e_5792_, v_e_x27_5793_);
v_r_5796_ = lean_box(v_res_5795_);
return v_r_5796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_as_5797_, lean_object* v_lo_5798_, lean_object* v_hi_5799_){
_start:
{
uint8_t v___x_5800_; 
v___x_5800_ = lean_nat_dec_lt(v_lo_5798_, v_hi_5799_);
if (v___x_5800_ == 0)
{
lean_dec(v_lo_5798_);
return v_as_5797_;
}
else
{
lean_object* v___x_5801_; lean_object* v___f_5802_; lean_object* v___x_5803_; lean_object* v_fst_5804_; lean_object* v_snd_5805_; uint8_t v___x_5806_; 
v___x_5801_ = lean_box(v___x_5800_);
v___f_5802_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5802_, 0, v___x_5801_);
lean_inc(v_lo_5798_);
v___x_5803_ = l_Array_qpartition___redArg(v_as_5797_, v___f_5802_, v_lo_5798_, v_hi_5799_);
v_fst_5804_ = lean_ctor_get(v___x_5803_, 0);
lean_inc(v_fst_5804_);
v_snd_5805_ = lean_ctor_get(v___x_5803_, 1);
lean_inc(v_snd_5805_);
lean_dec_ref(v___x_5803_);
v___x_5806_ = lean_nat_dec_le(v_hi_5799_, v_fst_5804_);
if (v___x_5806_ == 0)
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_snd_5805_, v_lo_5798_, v_fst_5804_);
v___x_5808_ = lean_unsigned_to_nat(1u);
v___x_5809_ = lean_nat_add(v_fst_5804_, v___x_5808_);
lean_dec(v_fst_5804_);
v_as_5797_ = v___x_5807_;
v_lo_5798_ = v___x_5809_;
goto _start;
}
else
{
lean_dec(v_fst_5804_);
lean_dec(v_lo_5798_);
return v_snd_5805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_as_5811_, lean_object* v_lo_5812_, lean_object* v_hi_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_as_5811_, v_lo_5812_, v_hi_5813_);
lean_dec(v_hi_5813_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_5817_){
_start:
{
lean_object* v___x_5819_; lean_object* v_env_5820_; lean_object* v___x_5821_; lean_object* v_toEnvExtension_5822_; lean_object* v_asyncMode_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___x_5835_; uint8_t v___x_5836_; 
v___x_5819_ = lean_st_ref_get(v___y_5817_);
v_env_5820_ = lean_ctor_get(v___x_5819_, 0);
lean_inc_ref(v_env_5820_);
lean_dec(v___x_5819_);
v___x_5821_ = l_Lean_errorExplanationExt;
v_toEnvExtension_5822_ = lean_ctor_get(v___x_5821_, 0);
lean_inc_ref(v_toEnvExtension_5822_);
v_asyncMode_5823_ = lean_ctor_get(v_toEnvExtension_5822_, 2);
lean_inc(v_asyncMode_5823_);
lean_dec_ref(v_toEnvExtension_5822_);
v___x_5824_ = lean_box(1);
v___x_5825_ = lean_box(0);
v___x_5826_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5824_, v___x_5821_, v_env_5820_, v_asyncMode_5823_, v___x_5825_);
lean_dec(v_asyncMode_5823_);
v___x_5827_ = lean_unsigned_to_nat(0u);
v___x_5828_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_5829_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_5828_, v___x_5826_);
lean_dec(v___x_5826_);
v___x_5835_ = lean_array_get_size(v___x_5829_);
v___x_5836_ = lean_nat_dec_eq(v___x_5835_, v___x_5827_);
if (v___x_5836_ == 0)
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___y_5840_; uint8_t v___x_5842_; 
v___x_5837_ = lean_unsigned_to_nat(1u);
v___x_5838_ = lean_nat_sub(v___x_5835_, v___x_5837_);
v___x_5842_ = lean_nat_dec_le(v___x_5827_, v___x_5838_);
if (v___x_5842_ == 0)
{
lean_inc(v___x_5838_);
v___y_5840_ = v___x_5838_;
goto v___jp_5839_;
}
else
{
v___y_5840_ = v___x_5827_;
goto v___jp_5839_;
}
v___jp_5839_:
{
uint8_t v___x_5841_; 
v___x_5841_ = lean_nat_dec_le(v___y_5840_, v___x_5838_);
if (v___x_5841_ == 0)
{
lean_dec(v___x_5838_);
lean_inc(v___y_5840_);
v___y_5831_ = v___y_5840_;
v___y_5832_ = v___y_5840_;
goto v___jp_5830_;
}
else
{
v___y_5831_ = v___y_5840_;
v___y_5832_ = v___x_5838_;
goto v___jp_5830_;
}
}
}
else
{
lean_object* v___x_5843_; 
v___x_5843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5829_);
return v___x_5843_;
}
v___jp_5830_:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_5829_, v___y_5831_, v___y_5832_);
lean_dec(v___y_5832_);
v___x_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5833_);
return v___x_5834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_5844_, lean_object* v___y_5845_){
_start:
{
lean_object* v_res_5846_; 
v_res_5846_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_5844_);
lean_dec(v___y_5844_);
return v_res_5846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_5847_, lean_object* v_stx_5848_, lean_object* v_ctx_5849_, uint8_t v_snd_5850_, lean_object* v_fst_5851_, lean_object* v_caps_5852_, lean_object* v_as_5853_, size_t v_sz_5854_, size_t v_i_5855_, lean_object* v_b_5856_){
_start:
{
lean_object* v_a_5858_; uint8_t v___x_5862_; 
v___x_5862_ = lean_usize_dec_lt(v_i_5855_, v_sz_5854_);
if (v___x_5862_ == 0)
{
lean_dec_ref(v_ctx_5849_);
lean_dec_ref(v_mkItem_5847_);
return v_b_5856_;
}
else
{
lean_object* v_a_5863_; lean_object* v_fst_5864_; lean_object* v_snd_5865_; lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5907_; 
v_a_5863_ = lean_array_uget(v_as_5853_, v_i_5855_);
v_fst_5864_ = lean_ctor_get(v_a_5863_, 0);
v_snd_5865_ = lean_ctor_get(v_a_5863_, 1);
v_isSharedCheck_5907_ = !lean_is_exclusive(v_a_5863_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5867_ = v_a_5863_;
v_isShared_5868_ = v_isSharedCheck_5907_;
goto v_resetjp_5866_;
}
else
{
lean_inc(v_snd_5865_);
lean_inc(v_fst_5864_);
lean_dec(v_a_5863_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5907_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___y_5870_; lean_object* v___x_5873_; lean_object* v___y_5875_; lean_object* v___y_5876_; uint8_t v___x_5897_; 
lean_inc(v_fst_5864_);
v___x_5873_ = l_Lean_Name_toString(v_fst_5864_, v___x_5862_);
v___x_5897_ = l_String_charactersIn(v_fst_5851_, v___x_5873_);
if (v___x_5897_ == 0)
{
lean_dec_ref(v___x_5873_);
lean_del_object(v___x_5867_);
lean_dec(v_snd_5865_);
lean_dec(v_fst_5864_);
v_a_5858_ = v_b_5856_;
goto v___jp_5857_;
}
else
{
lean_object* v_textDocument_x3f_5900_; 
v_textDocument_x3f_5900_ = lean_ctor_get(v_caps_5852_, 0);
if (lean_obj_tag(v_textDocument_x3f_5900_) == 0)
{
goto v___jp_5898_;
}
else
{
lean_object* v_val_5901_; lean_object* v_completion_x3f_5902_; 
v_val_5901_ = lean_ctor_get(v_textDocument_x3f_5900_, 0);
v_completion_x3f_5902_ = lean_ctor_get(v_val_5901_, 0);
if (lean_obj_tag(v_completion_x3f_5902_) == 0)
{
goto v___jp_5898_;
}
else
{
lean_object* v_val_5903_; 
v_val_5903_ = lean_ctor_get(v_completion_x3f_5902_, 0);
if (lean_obj_tag(v_val_5903_) == 0)
{
goto v___jp_5898_;
}
else
{
lean_object* v_val_5904_; 
v_val_5904_ = lean_ctor_get(v_val_5903_, 0);
if (lean_obj_tag(v_val_5904_) == 0)
{
goto v___jp_5898_;
}
else
{
lean_object* v_val_5905_; uint8_t v___x_5906_; 
v_val_5905_ = lean_ctor_get(v_val_5904_, 0);
v___x_5906_ = lean_unbox(v_val_5905_);
if (v___x_5906_ == 0)
{
goto v___jp_5898_;
}
else
{
goto v___jp_5886_;
}
}
}
}
}
}
v___jp_5869_:
{
lean_object* v___x_5871_; lean_object* v_items_5872_; 
lean_inc_ref(v_mkItem_5847_);
v___x_5871_ = lean_apply_3(v_mkItem_5847_, v_fst_5864_, v_snd_5865_, v___y_5870_);
v_items_5872_ = lean_array_push(v_b_5856_, v___x_5871_);
v_a_5858_ = v_items_5872_;
goto v___jp_5857_;
}
v___jp_5874_:
{
lean_object* v_toCommandContextInfo_5877_; lean_object* v_fileMap_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v_range_5882_; 
v_toCommandContextInfo_5877_ = lean_ctor_get(v_ctx_5849_, 0);
v_fileMap_5878_ = lean_ctor_get(v_toCommandContextInfo_5877_, 2);
lean_inc_ref(v_fileMap_5878_);
v___x_5879_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5878_, v___y_5875_);
lean_dec(v___y_5875_);
lean_inc_ref(v_fileMap_5878_);
v___x_5880_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5878_, v___y_5876_);
lean_dec(v___y_5876_);
if (v_isShared_5868_ == 0)
{
lean_ctor_set(v___x_5867_, 1, v___x_5880_);
lean_ctor_set(v___x_5867_, 0, v___x_5879_);
v_range_5882_ = v___x_5867_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5879_);
lean_ctor_set(v_reuseFailAlloc_5885_, 1, v___x_5880_);
v_range_5882_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
lean_object* v___x_5883_; lean_object* v___x_5884_; 
lean_inc_ref(v_range_5882_);
v___x_5883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5873_);
lean_ctor_set(v___x_5883_, 1, v_range_5882_);
lean_ctor_set(v___x_5883_, 2, v_range_5882_);
v___x_5884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5884_, 0, v___x_5883_);
v___y_5870_ = v___x_5884_;
goto v___jp_5869_;
}
}
v___jp_5886_:
{
uint8_t v___x_5887_; lean_object* v___x_5888_; 
v___x_5887_ = 0;
v___x_5888_ = l_Lean_Syntax_getRange_x3f(v_stx_5848_, v___x_5887_);
if (lean_obj_tag(v___x_5888_) == 1)
{
lean_object* v_val_5889_; 
v_val_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc(v_val_5889_);
lean_dec_ref(v___x_5888_);
if (v_snd_5850_ == 0)
{
lean_object* v_start_5890_; lean_object* v_stop_5891_; 
v_start_5890_ = lean_ctor_get(v_val_5889_, 0);
lean_inc(v_start_5890_);
v_stop_5891_ = lean_ctor_get(v_val_5889_, 1);
lean_inc(v_stop_5891_);
lean_dec(v_val_5889_);
v___y_5875_ = v_start_5890_;
v___y_5876_ = v_stop_5891_;
goto v___jp_5874_;
}
else
{
lean_object* v_start_5892_; lean_object* v_stop_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v_start_5892_ = lean_ctor_get(v_val_5889_, 0);
lean_inc(v_start_5892_);
v_stop_5893_ = lean_ctor_get(v_val_5889_, 1);
lean_inc(v_stop_5893_);
lean_dec(v_val_5889_);
v___x_5894_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5895_ = lean_nat_add(v_stop_5893_, v___x_5894_);
lean_dec(v_stop_5893_);
v___y_5875_ = v_start_5892_;
v___y_5876_ = v___x_5895_;
goto v___jp_5874_;
}
}
else
{
lean_object* v___x_5896_; 
lean_dec(v___x_5888_);
lean_dec_ref(v___x_5873_);
lean_del_object(v___x_5867_);
v___x_5896_ = lean_box(0);
v___y_5870_ = v___x_5896_;
goto v___jp_5869_;
}
}
v___jp_5898_:
{
if (v___x_5897_ == 0)
{
goto v___jp_5886_;
}
else
{
lean_object* v___x_5899_; 
lean_dec_ref(v___x_5873_);
lean_del_object(v___x_5867_);
v___x_5899_ = lean_box(0);
v___y_5870_ = v___x_5899_;
goto v___jp_5869_;
}
}
}
}
v___jp_5857_:
{
size_t v___x_5859_; size_t v___x_5860_; 
v___x_5859_ = ((size_t)1ULL);
v___x_5860_ = lean_usize_add(v_i_5855_, v___x_5859_);
v_i_5855_ = v___x_5860_;
v_b_5856_ = v_a_5858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_5908_, lean_object* v_stx_5909_, lean_object* v_ctx_5910_, lean_object* v_snd_5911_, lean_object* v_fst_5912_, lean_object* v_caps_5913_, lean_object* v_as_5914_, lean_object* v_sz_5915_, lean_object* v_i_5916_, lean_object* v_b_5917_){
_start:
{
uint8_t v_snd_1583__boxed_5918_; size_t v_sz_boxed_5919_; size_t v_i_boxed_5920_; lean_object* v_res_5921_; 
v_snd_1583__boxed_5918_ = lean_unbox(v_snd_5911_);
v_sz_boxed_5919_ = lean_unbox_usize(v_sz_5915_);
lean_dec(v_sz_5915_);
v_i_boxed_5920_ = lean_unbox_usize(v_i_5916_);
lean_dec(v_i_5916_);
v_res_5921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_5908_, v_stx_5909_, v_ctx_5910_, v_snd_1583__boxed_5918_, v_fst_5912_, v_caps_5913_, v_as_5914_, v_sz_boxed_5919_, v_i_boxed_5920_, v_b_5917_);
lean_dec_ref(v_as_5914_);
lean_dec_ref(v_caps_5913_);
lean_dec_ref(v_fst_5912_);
lean_dec(v_stx_5909_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_5922_, lean_object* v_stx_5923_, lean_object* v_caps_5924_, lean_object* v_ctx_5925_, lean_object* v_mkItem_5926_){
_start:
{
lean_object* v_fst_5928_; uint8_t v_snd_5929_; uint8_t v___x_5934_; lean_object* v___x_5935_; 
v___x_5934_ = 0;
v___x_5935_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5923_, v___x_5934_, v___x_5934_);
if (lean_obj_tag(v___x_5935_) == 0)
{
lean_object* v___x_5936_; 
v___x_5936_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5928_ = v___x_5936_;
v_snd_5929_ = v___x_5934_;
goto v___jp_5927_;
}
else
{
lean_object* v_val_5937_; lean_object* v_str_5938_; lean_object* v_startPos_5939_; lean_object* v_stopPos_5940_; uint8_t v___y_5942_; uint8_t v___x_5944_; 
v_val_5937_ = lean_ctor_get(v___x_5935_, 0);
lean_inc(v_val_5937_);
lean_dec_ref(v___x_5935_);
v_str_5938_ = lean_ctor_get(v_val_5937_, 0);
lean_inc_ref(v_str_5938_);
v_startPos_5939_ = lean_ctor_get(v_val_5937_, 1);
lean_inc(v_startPos_5939_);
v_stopPos_5940_ = lean_ctor_get(v_val_5937_, 2);
lean_inc(v_stopPos_5940_);
lean_dec(v_val_5937_);
v___x_5944_ = lean_string_utf8_at_end(v_str_5938_, v_stopPos_5940_);
if (v___x_5944_ == 0)
{
uint32_t v___x_5945_; uint32_t v___x_5946_; uint8_t v___x_5947_; 
v___x_5945_ = lean_string_utf8_get(v_str_5938_, v_stopPos_5940_);
v___x_5946_ = 46;
v___x_5947_ = lean_uint32_dec_eq(v___x_5945_, v___x_5946_);
if (v___x_5947_ == 0)
{
v___y_5942_ = v___x_5947_;
goto v___jp_5941_;
}
else
{
lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; 
v___x_5948_ = lean_string_utf8_extract(v_str_5938_, v_startPos_5939_, v_stopPos_5940_);
lean_dec(v_stopPos_5940_);
lean_dec(v_startPos_5939_);
lean_dec_ref(v_str_5938_);
v___x_5949_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5950_ = lean_string_append(v___x_5948_, v___x_5949_);
v_fst_5928_ = v___x_5950_;
v_snd_5929_ = v___x_5947_;
goto v___jp_5927_;
}
}
else
{
v___y_5942_ = v___x_5934_;
goto v___jp_5941_;
}
v___jp_5941_:
{
lean_object* v___x_5943_; 
v___x_5943_ = lean_string_utf8_extract(v_str_5938_, v_startPos_5939_, v_stopPos_5940_);
lean_dec(v_stopPos_5940_);
lean_dec(v_startPos_5939_);
lean_dec_ref(v_str_5938_);
v_fst_5928_ = v___x_5943_;
v_snd_5929_ = v___y_5942_;
goto v___jp_5927_;
}
}
v___jp_5927_:
{
lean_object* v_items_5930_; size_t v_sz_5931_; size_t v___x_5932_; lean_object* v___x_5933_; 
v_items_5930_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_5931_ = lean_array_size(v_entries_5922_);
v___x_5932_ = ((size_t)0ULL);
v___x_5933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_5926_, v_stx_5923_, v_ctx_5925_, v_snd_5929_, v_fst_5928_, v_caps_5924_, v_entries_5922_, v_sz_5931_, v___x_5932_, v_items_5930_);
lean_dec_ref(v_fst_5928_);
return v___x_5933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_5951_, lean_object* v_stx_5952_, lean_object* v_caps_5953_, lean_object* v_ctx_5954_, lean_object* v_mkItem_5955_){
_start:
{
lean_object* v_res_5956_; 
v_res_5956_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_5951_, v_stx_5952_, v_caps_5953_, v_ctx_5954_, v_mkItem_5955_);
lean_dec_ref(v_caps_5953_);
lean_dec(v_stx_5952_);
lean_dec_ref(v_entries_5951_);
return v_res_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_5957_, lean_object* v_caps_5958_, lean_object* v_ctx_5959_, lean_object* v___f_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_){
_start:
{
lean_object* v___x_5966_; lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5975_; 
v___x_5966_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_5964_);
v_a_5967_ = lean_ctor_get(v___x_5966_, 0);
v_isSharedCheck_5975_ = !lean_is_exclusive(v___x_5966_);
if (v_isSharedCheck_5975_ == 0)
{
v___x_5969_ = v___x_5966_;
v_isShared_5970_ = v_isSharedCheck_5975_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v___x_5966_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5975_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5971_; lean_object* v___x_5973_; 
v___x_5971_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_5967_, v_partialId_5957_, v_caps_5958_, v_ctx_5959_, v___f_5960_);
lean_dec(v_a_5967_);
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 0, v___x_5971_);
v___x_5973_ = v___x_5969_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5974_; 
v_reuseFailAlloc_5974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5974_, 0, v___x_5971_);
v___x_5973_ = v_reuseFailAlloc_5974_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
return v___x_5973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_5976_, lean_object* v_caps_5977_, lean_object* v_ctx_5978_, lean_object* v___f_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_5976_, v_caps_5977_, v_ctx_5978_, v___f_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
lean_dec(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec_ref(v_caps_5977_);
lean_dec(v_partialId_5976_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_5986_, lean_object* v_pos_5987_, lean_object* v_completionInfoPos_5988_, lean_object* v_ctx_5989_, lean_object* v_partialId_5990_, lean_object* v_caps_5991_){
_start:
{
lean_object* v___f_5993_; lean_object* v___f_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; 
v___f_5993_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5993_, 0, v_completionInfoPos_5988_);
lean_closure_set(v___f_5993_, 1, v_uri_5986_);
lean_closure_set(v___f_5993_, 2, v_pos_5987_);
lean_inc_ref(v_ctx_5989_);
v___f_5994_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_5994_, 0, v_partialId_5990_);
lean_closure_set(v___f_5994_, 1, v_caps_5991_);
lean_closure_set(v___f_5994_, 2, v_ctx_5989_);
lean_closure_set(v___f_5994_, 3, v___f_5993_);
v___x_5995_ = lean_unsigned_to_nat(32u);
v___x_5996_ = lean_mk_empty_array_with_capacity(v___x_5995_);
lean_dec_ref(v___x_5996_);
v___x_5997_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5998_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5989_, v___x_5997_, v___f_5994_);
return v___x_5998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_5999_, lean_object* v_pos_6000_, lean_object* v_completionInfoPos_6001_, lean_object* v_ctx_6002_, lean_object* v_partialId_6003_, lean_object* v_caps_6004_, lean_object* v_a_6005_){
_start:
{
lean_object* v_res_6006_; 
v_res_6006_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_5999_, v_pos_6000_, v_completionInfoPos_6001_, v_ctx_6002_, v_partialId_6003_, v_caps_6004_);
return v_res_6006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
lean_object* v___x_6012_; 
v___x_6012_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6010_);
return v___x_6012_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_){
_start:
{
lean_object* v_res_6018_; 
v_res_6018_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_);
lean_dec(v___y_6016_);
lean_dec_ref(v___y_6015_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
return v_res_6018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6019_, lean_object* v_t_6020_){
_start:
{
lean_object* v___x_6021_; 
v___x_6021_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6019_, v_t_6020_);
return v___x_6021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6022_, lean_object* v_t_6023_){
_start:
{
lean_object* v_res_6024_; 
v_res_6024_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6022_, v_t_6023_);
lean_dec(v_t_6023_);
return v_res_6024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6025_, lean_object* v_as_6026_, lean_object* v_lo_6027_, lean_object* v_hi_6028_, lean_object* v_w_6029_, lean_object* v_hlo_6030_, lean_object* v_hhi_6031_){
_start:
{
lean_object* v___x_6032_; 
v___x_6032_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_as_6026_, v_lo_6027_, v_hi_6028_);
return v___x_6032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6033_, lean_object* v_as_6034_, lean_object* v_lo_6035_, lean_object* v_hi_6036_, lean_object* v_w_6037_, lean_object* v_hlo_6038_, lean_object* v_hhi_6039_){
_start:
{
lean_object* v_res_6040_; 
v_res_6040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6033_, v_as_6034_, v_lo_6035_, v_hi_6036_, v_w_6037_, v_hlo_6038_, v_hhi_6039_);
lean_dec(v_hi_6036_);
lean_dec(v_n_6033_);
return v_res_6040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6041_, lean_object* v_uri_6042_, lean_object* v_pos_6043_, size_t v_sz_6044_, size_t v_i_6045_, lean_object* v_bs_6046_){
_start:
{
uint8_t v___x_6047_; 
v___x_6047_ = lean_usize_dec_lt(v_i_6045_, v_sz_6044_);
if (v___x_6047_ == 0)
{
lean_dec_ref(v_pos_6043_);
lean_dec_ref(v_uri_6042_);
lean_dec(v_completionInfoPos_6041_);
return v_bs_6046_;
}
else
{
lean_object* v_v_6048_; lean_object* v_userName_6049_; lean_object* v_docString_6050_; lean_object* v___x_6051_; lean_object* v_bs_x27_6052_; lean_object* v___x_6053_; lean_object* v___y_6055_; 
v_v_6048_ = lean_array_uget_borrowed(v_bs_6046_, v_i_6045_);
v_userName_6049_ = lean_ctor_get(v_v_6048_, 1);
lean_inc_ref(v_userName_6049_);
v_docString_6050_ = lean_ctor_get(v_v_6048_, 3);
lean_inc(v_docString_6050_);
v___x_6051_ = lean_unsigned_to_nat(0u);
v_bs_x27_6052_ = lean_array_uset(v_bs_6046_, v_i_6045_, v___x_6051_);
v___x_6053_ = lean_box(0);
if (lean_obj_tag(v_docString_6050_) == 0)
{
v___y_6055_ = v___x_6053_;
goto v___jp_6054_;
}
else
{
lean_object* v_val_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6074_; 
v_val_6065_ = lean_ctor_get(v_docString_6050_, 0);
v_isSharedCheck_6074_ = !lean_is_exclusive(v_docString_6050_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6067_ = v_docString_6050_;
v_isShared_6068_ = v_isSharedCheck_6074_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_val_6065_);
lean_dec(v_docString_6050_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6074_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
uint8_t v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6072_; 
v___x_6069_ = 1;
v___x_6070_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6070_, 0, v_val_6065_);
lean_ctor_set_uint8(v___x_6070_, sizeof(void*)*1, v___x_6069_);
if (v_isShared_6068_ == 0)
{
lean_ctor_set(v___x_6067_, 0, v___x_6070_);
v___x_6072_ = v___x_6067_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v___x_6070_);
v___x_6072_ = v_reuseFailAlloc_6073_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
v___y_6055_ = v___x_6072_;
goto v___jp_6054_;
}
}
}
v___jp_6054_:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; size_t v___x_6061_; size_t v___x_6062_; lean_object* v___x_6063_; 
v___x_6056_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6041_);
v___x_6057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6057_, 0, v_completionInfoPos_6041_);
lean_inc_ref(v_pos_6043_);
lean_inc_ref(v_uri_6042_);
v___x_6058_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6058_, 0, v_uri_6042_);
lean_ctor_set(v___x_6058_, 1, v_pos_6043_);
lean_ctor_set(v___x_6058_, 2, v___x_6057_);
lean_ctor_set(v___x_6058_, 3, v___x_6053_);
v___x_6059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
v___x_6060_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6060_, 0, v_userName_6049_);
lean_ctor_set(v___x_6060_, 1, v___x_6053_);
lean_ctor_set(v___x_6060_, 2, v___y_6055_);
lean_ctor_set(v___x_6060_, 3, v___x_6056_);
lean_ctor_set(v___x_6060_, 4, v___x_6053_);
lean_ctor_set(v___x_6060_, 5, v___x_6053_);
lean_ctor_set(v___x_6060_, 6, v___x_6059_);
lean_ctor_set(v___x_6060_, 7, v___x_6053_);
v___x_6061_ = ((size_t)1ULL);
v___x_6062_ = lean_usize_add(v_i_6045_, v___x_6061_);
v___x_6063_ = lean_array_uset(v_bs_x27_6052_, v_i_6045_, v___x_6060_);
v_i_6045_ = v___x_6062_;
v_bs_6046_ = v___x_6063_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6075_, lean_object* v_uri_6076_, lean_object* v_pos_6077_, lean_object* v_sz_6078_, lean_object* v_i_6079_, lean_object* v_bs_6080_){
_start:
{
size_t v_sz_boxed_6081_; size_t v_i_boxed_6082_; lean_object* v_res_6083_; 
v_sz_boxed_6081_ = lean_unbox_usize(v_sz_6078_);
lean_dec(v_sz_6078_);
v_i_boxed_6082_ = lean_unbox_usize(v_i_6079_);
lean_dec(v_i_6079_);
v_res_6083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6075_, v_uri_6076_, v_pos_6077_, v_sz_boxed_6081_, v_i_boxed_6082_, v_bs_6080_);
return v_res_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6084_, lean_object* v_completionInfoPos_6085_, lean_object* v_uri_6086_, lean_object* v_pos_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_){
_start:
{
lean_object* v___x_6093_; 
v___x_6093_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6084_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_);
if (lean_obj_tag(v___x_6093_) == 0)
{
lean_object* v_a_6094_; lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6104_; 
v_a_6094_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6104_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6104_ == 0)
{
v___x_6096_ = v___x_6093_;
v_isShared_6097_ = v_isSharedCheck_6104_;
goto v_resetjp_6095_;
}
else
{
lean_inc(v_a_6094_);
lean_dec(v___x_6093_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6104_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
size_t v_sz_6098_; size_t v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6102_; 
v_sz_6098_ = lean_array_size(v_a_6094_);
v___x_6099_ = ((size_t)0ULL);
v___x_6100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6085_, v_uri_6086_, v_pos_6087_, v_sz_6098_, v___x_6099_, v_a_6094_);
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 0, v___x_6100_);
v___x_6102_ = v___x_6096_;
goto v_reusejp_6101_;
}
else
{
lean_object* v_reuseFailAlloc_6103_; 
v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6103_, 0, v___x_6100_);
v___x_6102_ = v_reuseFailAlloc_6103_;
goto v_reusejp_6101_;
}
v_reusejp_6101_:
{
return v___x_6102_;
}
}
}
else
{
lean_object* v_a_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6112_; 
lean_dec_ref(v_pos_6087_);
lean_dec_ref(v_uri_6086_);
lean_dec(v_completionInfoPos_6085_);
v_a_6105_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6112_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6112_ == 0)
{
v___x_6107_ = v___x_6093_;
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_a_6105_);
lean_dec(v___x_6093_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v___x_6110_; 
if (v_isShared_6108_ == 0)
{
v___x_6110_ = v___x_6107_;
goto v_reusejp_6109_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_a_6105_);
v___x_6110_ = v_reuseFailAlloc_6111_;
goto v_reusejp_6109_;
}
v_reusejp_6109_:
{
return v___x_6110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6113_, lean_object* v_completionInfoPos_6114_, lean_object* v_uri_6115_, lean_object* v_pos_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
uint8_t v___x_526__boxed_6122_; lean_object* v_res_6123_; 
v___x_526__boxed_6122_ = lean_unbox(v___x_6113_);
v_res_6123_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_526__boxed_6122_, v_completionInfoPos_6114_, v_uri_6115_, v_pos_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6124_, lean_object* v_pos_6125_, lean_object* v_completionInfoPos_6126_, lean_object* v_ctx_6127_){
_start:
{
lean_object* v___x_6129_; uint8_t v___x_6130_; lean_object* v___x_6131_; lean_object* v___f_6132_; lean_object* v___x_6133_; 
v___x_6129_ = l_Lean_LocalContext_empty;
v___x_6130_ = 0;
v___x_6131_ = lean_box(v___x_6130_);
v___f_6132_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6132_, 0, v___x_6131_);
lean_closure_set(v___f_6132_, 1, v_completionInfoPos_6126_);
lean_closure_set(v___f_6132_, 2, v_uri_6124_);
lean_closure_set(v___f_6132_, 3, v_pos_6125_);
v___x_6133_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6127_, v___x_6129_, v___f_6132_);
return v___x_6133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6134_, lean_object* v_pos_6135_, lean_object* v_completionInfoPos_6136_, lean_object* v_ctx_6137_, lean_object* v_a_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6134_, v_pos_6135_, v_completionInfoPos_6136_, v_ctx_6137_);
return v_res_6139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6140_, lean_object* v_b_6141_){
_start:
{
lean_object* v_array_6142_; lean_object* v_start_6143_; lean_object* v_stop_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6157_; 
v_array_6142_ = lean_ctor_get(v_a_6140_, 0);
v_start_6143_ = lean_ctor_get(v_a_6140_, 1);
v_stop_6144_ = lean_ctor_get(v_a_6140_, 2);
v_isSharedCheck_6157_ = !lean_is_exclusive(v_a_6140_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6146_ = v_a_6140_;
v_isShared_6147_ = v_isSharedCheck_6157_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_stop_6144_);
lean_inc(v_start_6143_);
lean_inc(v_array_6142_);
lean_dec(v_a_6140_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6157_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
uint8_t v___x_6148_; 
v___x_6148_ = lean_nat_dec_lt(v_start_6143_, v_stop_6144_);
if (v___x_6148_ == 0)
{
lean_del_object(v___x_6146_);
lean_dec(v_stop_6144_);
lean_dec(v_start_6143_);
lean_dec_ref(v_array_6142_);
return v_b_6141_;
}
else
{
lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6152_; 
v___x_6149_ = lean_unsigned_to_nat(1u);
v___x_6150_ = lean_nat_add(v_start_6143_, v___x_6149_);
lean_inc_ref(v_array_6142_);
if (v_isShared_6147_ == 0)
{
lean_ctor_set(v___x_6146_, 1, v___x_6150_);
v___x_6152_ = v___x_6146_;
goto v_reusejp_6151_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_array_6142_);
lean_ctor_set(v_reuseFailAlloc_6156_, 1, v___x_6150_);
lean_ctor_set(v_reuseFailAlloc_6156_, 2, v_stop_6144_);
v___x_6152_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6151_;
}
v_reusejp_6151_:
{
lean_object* v___x_6153_; lean_object* v___x_6154_; 
v___x_6153_ = lean_array_fget(v_array_6142_, v_start_6143_);
lean_dec(v_start_6143_);
lean_dec_ref(v_array_6142_);
v___x_6154_ = lean_array_push(v_b_6141_, v___x_6153_);
v_a_6140_ = v___x_6152_;
v_b_6141_ = v___x_6154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6160_, lean_object* v_idx_6161_){
_start:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; 
v___x_6162_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6163_ = lean_array_get_size(v_scopeNames_6160_);
v___x_6164_ = l_Array_toSubarray___redArg(v_scopeNames_6160_, v_idx_6161_, v___x_6163_);
v___x_6165_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6166_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6164_, v___x_6165_);
v___x_6167_ = lean_array_to_list(v___x_6166_);
v___x_6168_ = l_String_intercalate(v___x_6162_, v___x_6167_);
return v___x_6168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6169_, lean_object* v_R_6170_, lean_object* v_a_6171_, lean_object* v_b_6172_){
_start:
{
lean_object* v___x_6173_; 
v___x_6173_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6171_, v_b_6172_);
return v___x_6173_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6174_, lean_object* v_next_6175_, lean_object* v_scopeNames_6176_, lean_object* v_idComponents_6177_, lean_object* v_a_6178_, uint8_t v_b_6179_){
_start:
{
uint8_t v___x_6180_; 
v___x_6180_ = lean_nat_dec_lt(v_a_6178_, v_upperBound_6174_);
if (v___x_6180_ == 0)
{
lean_dec(v_a_6178_);
return v_b_6179_;
}
else
{
uint8_t v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; uint8_t v___x_6184_; 
v___x_6181_ = 0;
v___x_6182_ = lean_nat_add(v_next_6175_, v_a_6178_);
v___x_6183_ = lean_array_get_size(v_scopeNames_6176_);
v___x_6184_ = lean_nat_dec_lt(v___x_6182_, v___x_6183_);
if (v___x_6184_ == 0)
{
lean_dec(v___x_6182_);
lean_dec(v_a_6178_);
return v___x_6181_;
}
else
{
lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; uint8_t v___x_6188_; 
v___x_6185_ = lean_array_fget_borrowed(v_scopeNames_6176_, v___x_6182_);
lean_dec(v___x_6182_);
v___x_6186_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6187_ = lean_array_get_borrowed(v___x_6186_, v_idComponents_6177_, v_a_6178_);
v___x_6188_ = lean_string_dec_eq(v___x_6187_, v___x_6185_);
if (v___x_6188_ == 0)
{
lean_dec(v_a_6178_);
return v___x_6181_;
}
else
{
lean_object* v___x_6189_; lean_object* v___x_6190_; 
v___x_6189_ = lean_unsigned_to_nat(1u);
v___x_6190_ = lean_nat_add(v_a_6178_, v___x_6189_);
lean_dec(v_a_6178_);
v_a_6178_ = v___x_6190_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6192_, lean_object* v_next_6193_, lean_object* v_scopeNames_6194_, lean_object* v_idComponents_6195_, lean_object* v_a_6196_, lean_object* v_b_6197_){
_start:
{
uint8_t v_b_boxed_6198_; uint8_t v_res_6199_; lean_object* v_r_6200_; 
v_b_boxed_6198_ = lean_unbox(v_b_6197_);
v_res_6199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6192_, v_next_6193_, v_scopeNames_6194_, v_idComponents_6195_, v_a_6196_, v_b_boxed_6198_);
lean_dec_ref(v_idComponents_6195_);
lean_dec_ref(v_scopeNames_6194_);
lean_dec(v_next_6193_);
lean_dec(v_upperBound_6192_);
v_r_6200_ = lean_box(v_res_6199_);
return v_r_6200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6201_, lean_object* v_idComponents_6202_, lean_object* v_scopeNames_6203_, lean_object* v_a_6204_, lean_object* v_b_6205_){
_start:
{
lean_object* v_a_6207_; uint8_t v___x_6211_; 
v___x_6211_ = lean_nat_dec_lt(v_a_6204_, v_upperBound_6201_);
if (v___x_6211_ == 0)
{
lean_dec(v_a_6204_);
lean_dec_ref(v_scopeNames_6203_);
return v_b_6205_;
}
else
{
lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; uint8_t v___x_6215_; 
v___x_6212_ = lean_array_get_size(v_idComponents_6202_);
v___x_6213_ = lean_unsigned_to_nat(1u);
v___x_6214_ = lean_nat_sub(v___x_6212_, v___x_6213_);
v___x_6215_ = lean_nat_dec_lt(v___x_6214_, v___x_6212_);
if (v___x_6215_ == 0)
{
lean_object* v___x_6216_; lean_object* v___x_6217_; 
lean_dec(v___x_6214_);
lean_inc(v_a_6204_);
lean_inc_ref(v_scopeNames_6203_);
v___x_6216_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6203_, v_a_6204_);
v___x_6217_ = lean_array_push(v_b_6205_, v___x_6216_);
v_a_6207_ = v___x_6217_;
goto v___jp_6206_;
}
else
{
lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; uint8_t v___x_6221_; 
v___x_6218_ = lean_nat_add(v_a_6204_, v___x_6212_);
v___x_6219_ = lean_nat_sub(v___x_6218_, v___x_6213_);
lean_dec(v___x_6218_);
v___x_6220_ = lean_array_get_size(v_scopeNames_6203_);
v___x_6221_ = lean_nat_dec_lt(v___x_6219_, v___x_6220_);
if (v___x_6221_ == 0)
{
lean_dec(v___x_6219_);
lean_dec(v___x_6214_);
v_a_6207_ = v_b_6205_;
goto v___jp_6206_;
}
else
{
lean_object* v___x_6222_; lean_object* v___x_6223_; uint8_t v___x_6224_; 
v___x_6222_ = lean_array_fget_borrowed(v_idComponents_6202_, v___x_6214_);
v___x_6223_ = lean_array_fget_borrowed(v_scopeNames_6203_, v___x_6219_);
v___x_6224_ = l_String_charactersIn(v___x_6222_, v___x_6223_);
if (v___x_6224_ == 0)
{
lean_dec(v___x_6219_);
lean_dec(v___x_6214_);
v_a_6207_ = v_b_6205_;
goto v___jp_6206_;
}
else
{
lean_object* v___x_6225_; uint8_t v___x_6226_; 
v___x_6225_ = lean_unsigned_to_nat(0u);
v___x_6226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6214_, v_a_6204_, v_scopeNames_6203_, v_idComponents_6202_, v___x_6225_, v___x_6224_);
lean_dec(v___x_6214_);
if (v___x_6226_ == 0)
{
lean_dec(v___x_6219_);
v_a_6207_ = v_b_6205_;
goto v___jp_6206_;
}
else
{
lean_object* v___x_6227_; lean_object* v___x_6228_; 
lean_inc_ref(v_scopeNames_6203_);
v___x_6227_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6203_, v___x_6219_);
v___x_6228_ = lean_array_push(v_b_6205_, v___x_6227_);
v_a_6207_ = v___x_6228_;
goto v___jp_6206_;
}
}
}
}
}
v___jp_6206_:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6208_ = lean_unsigned_to_nat(1u);
v___x_6209_ = lean_nat_add(v_a_6204_, v___x_6208_);
lean_dec(v_a_6204_);
v_a_6204_ = v___x_6209_;
v_b_6205_ = v_a_6207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6229_, lean_object* v_idComponents_6230_, lean_object* v_scopeNames_6231_, lean_object* v_a_6232_, lean_object* v_b_6233_){
_start:
{
lean_object* v_res_6234_; 
v_res_6234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6229_, v_idComponents_6230_, v_scopeNames_6231_, v_a_6232_, v_b_6233_);
lean_dec_ref(v_idComponents_6230_);
lean_dec(v_upperBound_6229_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6235_, lean_object* v_scopeNames_6236_){
_start:
{
lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v_r_6239_; lean_object* v___x_6240_; 
v___x_6237_ = lean_unsigned_to_nat(0u);
v___x_6238_ = lean_array_get_size(v_scopeNames_6236_);
v_r_6239_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6238_, v_idComponents_6235_, v_scopeNames_6236_, v___x_6237_, v_r_6239_);
return v___x_6240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6241_, lean_object* v_scopeNames_6242_){
_start:
{
lean_object* v_res_6243_; 
v_res_6243_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6241_, v_scopeNames_6242_);
lean_dec_ref(v_idComponents_6241_);
return v_res_6243_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6244_, lean_object* v_next_6245_, lean_object* v_scopeNames_6246_, lean_object* v_idComponents_6247_, lean_object* v_inst_6248_, lean_object* v_R_6249_, lean_object* v_a_6250_, uint8_t v_b_6251_, lean_object* v_c_6252_){
_start:
{
uint8_t v___x_6253_; 
v___x_6253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6244_, v_next_6245_, v_scopeNames_6246_, v_idComponents_6247_, v_a_6250_, v_b_6251_);
return v___x_6253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6254_, lean_object* v_next_6255_, lean_object* v_scopeNames_6256_, lean_object* v_idComponents_6257_, lean_object* v_inst_6258_, lean_object* v_R_6259_, lean_object* v_a_6260_, lean_object* v_b_6261_, lean_object* v_c_6262_){
_start:
{
uint8_t v_b_boxed_6263_; uint8_t v_res_6264_; lean_object* v_r_6265_; 
v_b_boxed_6263_ = lean_unbox(v_b_6261_);
v_res_6264_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6254_, v_next_6255_, v_scopeNames_6256_, v_idComponents_6257_, v_inst_6258_, v_R_6259_, v_a_6260_, v_b_boxed_6263_, v_c_6262_);
lean_dec_ref(v_idComponents_6257_);
lean_dec_ref(v_scopeNames_6256_);
lean_dec(v_next_6255_);
lean_dec(v_upperBound_6254_);
v_r_6265_ = lean_box(v_res_6264_);
return v_r_6265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6266_, lean_object* v_idComponents_6267_, lean_object* v_scopeNames_6268_, lean_object* v_inst_6269_, lean_object* v_R_6270_, lean_object* v_a_6271_, lean_object* v_b_6272_, lean_object* v_c_6273_){
_start:
{
lean_object* v___x_6274_; 
v___x_6274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6266_, v_idComponents_6267_, v_scopeNames_6268_, v_a_6271_, v_b_6272_);
return v___x_6274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6275_, lean_object* v_idComponents_6276_, lean_object* v_scopeNames_6277_, lean_object* v_inst_6278_, lean_object* v_R_6279_, lean_object* v_a_6280_, lean_object* v_b_6281_, lean_object* v_c_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6275_, v_idComponents_6276_, v_scopeNames_6277_, v_inst_6278_, v_R_6279_, v_a_6280_, v_b_6281_, v_c_6282_);
lean_dec_ref(v_idComponents_6276_);
lean_dec(v_upperBound_6275_);
return v_res_6283_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6284_){
_start:
{
lean_object* v___x_6285_; lean_object* v___x_6286_; uint8_t v___x_6287_; 
v___x_6285_ = lean_string_utf8_byte_size(v_x_6284_);
v___x_6286_ = lean_unsigned_to_nat(0u);
v___x_6287_ = lean_nat_dec_eq(v___x_6285_, v___x_6286_);
if (v___x_6287_ == 0)
{
uint8_t v___x_6288_; 
v___x_6288_ = 1;
return v___x_6288_;
}
else
{
uint8_t v___x_6289_; 
v___x_6289_ = 0;
return v___x_6289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6290_){
_start:
{
uint8_t v_res_6291_; lean_object* v_r_6292_; 
v_res_6291_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6290_);
lean_dec_ref(v_x_6290_);
v_r_6292_ = lean_box(v_res_6291_);
return v_r_6292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6293_, size_t v_i_6294_, lean_object* v_bs_6295_){
_start:
{
uint8_t v___x_6296_; 
v___x_6296_ = lean_usize_dec_lt(v_i_6294_, v_sz_6293_);
if (v___x_6296_ == 0)
{
return v_bs_6295_;
}
else
{
lean_object* v_v_6297_; lean_object* v___x_6298_; lean_object* v_bs_x27_6299_; lean_object* v___x_6300_; size_t v___x_6301_; size_t v___x_6302_; lean_object* v___x_6303_; 
v_v_6297_ = lean_array_uget(v_bs_6295_, v_i_6294_);
v___x_6298_ = lean_unsigned_to_nat(0u);
v_bs_x27_6299_ = lean_array_uset(v_bs_6295_, v_i_6294_, v___x_6298_);
v___x_6300_ = l_Lean_Name_toString(v_v_6297_, v___x_6296_);
v___x_6301_ = ((size_t)1ULL);
v___x_6302_ = lean_usize_add(v_i_6294_, v___x_6301_);
v___x_6303_ = lean_array_uset(v_bs_x27_6299_, v_i_6294_, v___x_6300_);
v_i_6294_ = v___x_6302_;
v_bs_6295_ = v___x_6303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6305_, lean_object* v_i_6306_, lean_object* v_bs_6307_){
_start:
{
size_t v_sz_boxed_6308_; size_t v_i_boxed_6309_; lean_object* v_res_6310_; 
v_sz_boxed_6308_ = lean_unbox_usize(v_sz_6305_);
lean_dec(v_sz_6305_);
v_i_boxed_6309_ = lean_unbox_usize(v_i_6306_);
lean_dec(v_i_6306_);
v_res_6310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6308_, v_i_boxed_6309_, v_bs_6307_);
return v_res_6310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6311_, lean_object* v_uri_6312_, lean_object* v_pos_6313_, size_t v_sz_6314_, size_t v_i_6315_, lean_object* v_bs_6316_){
_start:
{
uint8_t v___x_6317_; 
v___x_6317_ = lean_usize_dec_lt(v_i_6315_, v_sz_6314_);
if (v___x_6317_ == 0)
{
lean_dec_ref(v_pos_6313_);
lean_dec_ref(v_uri_6312_);
lean_dec(v_completionInfoPos_6311_);
return v_bs_6316_;
}
else
{
lean_object* v_v_6318_; lean_object* v___x_6319_; lean_object* v_bs_x27_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; size_t v___x_6327_; size_t v___x_6328_; lean_object* v___x_6329_; 
v_v_6318_ = lean_array_uget(v_bs_6316_, v_i_6315_);
v___x_6319_ = lean_unsigned_to_nat(0u);
v_bs_x27_6320_ = lean_array_uset(v_bs_6316_, v_i_6315_, v___x_6319_);
v___x_6321_ = lean_box(0);
v___x_6322_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6311_);
v___x_6323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6323_, 0, v_completionInfoPos_6311_);
lean_inc_ref(v_pos_6313_);
lean_inc_ref(v_uri_6312_);
v___x_6324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6324_, 0, v_uri_6312_);
lean_ctor_set(v___x_6324_, 1, v_pos_6313_);
lean_ctor_set(v___x_6324_, 2, v___x_6323_);
lean_ctor_set(v___x_6324_, 3, v___x_6321_);
v___x_6325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6325_, 0, v___x_6324_);
v___x_6326_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6326_, 0, v_v_6318_);
lean_ctor_set(v___x_6326_, 1, v___x_6321_);
lean_ctor_set(v___x_6326_, 2, v___x_6321_);
lean_ctor_set(v___x_6326_, 3, v___x_6322_);
lean_ctor_set(v___x_6326_, 4, v___x_6321_);
lean_ctor_set(v___x_6326_, 5, v___x_6321_);
lean_ctor_set(v___x_6326_, 6, v___x_6325_);
lean_ctor_set(v___x_6326_, 7, v___x_6321_);
v___x_6327_ = ((size_t)1ULL);
v___x_6328_ = lean_usize_add(v_i_6315_, v___x_6327_);
v___x_6329_ = lean_array_uset(v_bs_x27_6320_, v_i_6315_, v___x_6326_);
v_i_6315_ = v___x_6328_;
v_bs_6316_ = v___x_6329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6331_, lean_object* v_uri_6332_, lean_object* v_pos_6333_, lean_object* v_sz_6334_, lean_object* v_i_6335_, lean_object* v_bs_6336_){
_start:
{
size_t v_sz_boxed_6337_; size_t v_i_boxed_6338_; lean_object* v_res_6339_; 
v_sz_boxed_6337_ = lean_unbox_usize(v_sz_6334_);
lean_dec(v_sz_6334_);
v_i_boxed_6338_ = lean_unbox_usize(v_i_6335_);
lean_dec(v_i_6335_);
v_res_6339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6331_, v_uri_6332_, v_pos_6333_, v_sz_boxed_6337_, v_i_boxed_6338_, v_bs_6336_);
return v_res_6339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6341_, lean_object* v_pos_6342_, lean_object* v_completionInfoPos_6343_, lean_object* v_id_x3f_6344_, uint8_t v_danglingDot_6345_, lean_object* v_scopeNames_6346_){
_start:
{
lean_object* v___f_6348_; lean_object* v_idComponents_6350_; lean_object* v___y_6361_; 
v___f_6348_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6344_) == 0)
{
lean_object* v___x_6364_; 
v___x_6364_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6361_ = v___x_6364_;
goto v___jp_6360_;
}
else
{
lean_object* v_val_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; size_t v_sz_6368_; size_t v___x_6369_; lean_object* v___x_6370_; 
v_val_6365_ = lean_ctor_get(v_id_x3f_6344_, 0);
lean_inc(v_val_6365_);
lean_dec_ref(v_id_x3f_6344_);
v___x_6366_ = l_Lean_Name_components(v_val_6365_);
v___x_6367_ = lean_array_mk(v___x_6366_);
v_sz_6368_ = lean_array_size(v___x_6367_);
v___x_6369_ = ((size_t)0ULL);
v___x_6370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6368_, v___x_6369_, v___x_6367_);
v___y_6361_ = v___x_6370_;
goto v___jp_6360_;
}
v___jp_6349_:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v_scopeNames_6354_; lean_object* v_candidates_6355_; size_t v_sz_6356_; size_t v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6351_ = lean_array_mk(v_scopeNames_6346_);
v___x_6352_ = lean_array_pop(v___x_6351_);
v___x_6353_ = l_Array_takeWhile___redArg(v___f_6348_, v___x_6352_);
lean_dec_ref(v___x_6352_);
v_scopeNames_6354_ = l_Array_reverse___redArg(v___x_6353_);
v_candidates_6355_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6350_, v_scopeNames_6354_);
lean_dec_ref(v_idComponents_6350_);
v_sz_6356_ = lean_array_size(v_candidates_6355_);
v___x_6357_ = ((size_t)0ULL);
v___x_6358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6343_, v_uri_6341_, v_pos_6342_, v_sz_6356_, v___x_6357_, v_candidates_6355_);
v___x_6359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6359_, 0, v___x_6358_);
return v___x_6359_;
}
v___jp_6360_:
{
if (v_danglingDot_6345_ == 0)
{
v_idComponents_6350_ = v___y_6361_;
goto v___jp_6349_;
}
else
{
lean_object* v___x_6362_; lean_object* v_idComponents_6363_; 
v___x_6362_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6363_ = lean_array_push(v___y_6361_, v___x_6362_);
v_idComponents_6350_ = v_idComponents_6363_;
goto v___jp_6349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6371_, lean_object* v_pos_6372_, lean_object* v_completionInfoPos_6373_, lean_object* v_id_x3f_6374_, lean_object* v_danglingDot_6375_, lean_object* v_scopeNames_6376_, lean_object* v_a_6377_){
_start:
{
uint8_t v_danglingDot_boxed_6378_; lean_object* v_res_6379_; 
v_danglingDot_boxed_6378_ = lean_unbox(v_danglingDot_6375_);
v_res_6379_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6371_, v_pos_6372_, v_completionInfoPos_6373_, v_id_x3f_6374_, v_danglingDot_boxed_6378_, v_scopeNames_6376_);
return v_res_6379_;
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
