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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_String_charactersIn(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_isPrivatePrefix(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_RequestCancellation_requestCancelled;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_Zipper_prependNode___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
lean_object* l_Lean_Server_Completion_getEligibleHeaderDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getCompletionTagsForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAliasState(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaces(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__15(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_28_ = lean_st_ref_put(v_a_6_, v___x_27_);
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
v___x_388_ = l_Lean_privateToUserName_x3f(v_declName_385_);
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
v___x_455_ = l_Lean_String_charactersIn(v_str_450_, v_str_452_);
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
v___x_466_ = l_Lean_String_charactersIn(v_str_450_, v_str_452_);
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
v___x_679_ = l_Lean_String_charactersIn(v_str_677_, v_str_678_);
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
lean_object* v_a_1126_; lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1162_; 
v_a_1126_ = lean_ctor_get(v_a_1074_, 0);
v_a_1127_ = lean_ctor_get(v_a_1074_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_a_1074_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1129_ = v_a_1074_;
v_isShared_1130_ = v_isSharedCheck_1162_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
lean_dec(v_a_1074_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1162_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_map_1131_; lean_object* v_pos_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1161_; 
v_map_1131_ = lean_ctor_get(v_a_1126_, 0);
v_pos_1132_ = lean_ctor_get(v_a_1126_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_a_1126_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1134_ = v_a_1126_;
v_isShared_1135_ = v_isSharedCheck_1161_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_pos_1132_);
lean_inc(v_map_1131_);
lean_dec(v_a_1126_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1161_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_keyArray_1146_; lean_object* v_valueArray_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_keyArray_1146_ = lean_ctor_get(v_map_1131_, 1);
v_valueArray_1147_ = lean_ctor_get(v_map_1131_, 2);
v___x_1148_ = lean_array_get_size(v_keyArray_1146_);
v___x_1149_ = lean_nat_dec_lt(v_pos_1132_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_del_object(v___x_1134_);
lean_dec(v_pos_1132_);
lean_dec_ref(v_map_1131_);
lean_del_object(v___x_1129_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_a_1127_);
v_a_1074_ = v___x_1150_;
goto _start;
}
else
{
lean_object* v___x_1152_; uint8_t v_isSome_1153_; 
v___x_1152_ = lean_array_fget_borrowed(v_keyArray_1146_, v_pos_1132_);
v_isSome_1153_ = lean_noption_is_some(v___x_1152_);
if (v_isSome_1153_ == 0)
{
goto v___jp_1136_;
}
else
{
lean_object* v___x_1154_; uint8_t v_isSome_1155_; 
v___x_1154_ = lean_array_fget_borrowed(v_valueArray_1147_, v_pos_1132_);
v_isSome_1155_ = lean_noption_is_some(v___x_1154_);
if (v_isSome_1155_ == 0)
{
goto v___jp_1136_;
}
else
{
lean_object* v_val_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_del_object(v___x_1134_);
lean_del_object(v___x_1129_);
lean_inc(v___x_1152_);
v_val_1156_ = lean_noption_get(v___x_1152_);
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_add(v_pos_1132_, v___x_1157_);
lean_dec(v_pos_1132_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_map_1131_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_a_1127_);
v_it_1117_ = v___x_1160_;
v_fst_1118_ = v_val_1156_;
goto v___jp_1116_;
}
}
}
v___jp_1136_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_pos_1132_, v___x_1137_);
lean_dec(v_pos_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1138_);
v___x_1140_ = v___x_1134_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_map_1131_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1140_);
v___x_1142_ = v___x_1129_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_a_1127_);
v___x_1142_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
v_a_1074_ = v___x_1142_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v_a_1074_, 1);
switch(lean_obj_tag(v_a_1163_))
{
case 0:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref(v___x_1073_);
lean_dec(v_id_1071_);
lean_dec_ref(v_ctx_1070_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1075_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
case 1:
{
lean_object* v_a_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1185_; 
v_a_1166_ = lean_ctor_get(v_a_1163_, 0);
v_a_1167_ = lean_ctor_get(v_a_1163_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_a_1163_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1169_ = v_a_1163_;
v_isShared_1170_ = v_isSharedCheck_1185_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_inc(v_a_1166_);
lean_dec(v_a_1163_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1185_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_start_1171_; lean_object* v_stop_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_start_1171_ = lean_ctor_get(v_a_1166_, 1);
v_stop_1172_ = lean_ctor_get(v_a_1166_, 2);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_nat_sub(v_stop_1172_, v_start_1171_);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
lean_dec(v___x_1174_);
if (v___x_1175_ == 0)
{
lean_del_object(v___x_1169_);
lean_dec_ref(v_a_1166_);
v_it_1085_ = v_a_1167_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_z_1179_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_1166_);
v___x_1177_ = l_Subarray_drop___redArg(v_a_1166_, v___x_1176_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1177_);
v_z_1179_ = v___x_1169_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_a_1167_);
v_z_1179_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Subarray_get___redArg(v_a_1166_, v___x_1173_);
lean_dec_ref(v_a_1166_);
switch(lean_obj_tag(v___x_1180_))
{
case 0:
{
lean_object* v_key_1181_; 
v_key_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_key_1181_);
lean_dec_ref_known(v___x_1180_, 2);
v_it_1123_ = v_z_1179_;
v_fst_1124_ = v_key_1181_;
goto v___jp_1122_;
}
case 1:
{
lean_object* v_node_1182_; lean_object* v___x_1183_; 
v_node_1182_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_node_1182_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1183_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1182_, v_z_1179_);
v_it_1085_ = v___x_1183_;
goto v___jp_1084_;
}
default: 
{
v_it_1085_ = v_z_1179_;
goto v___jp_1084_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_1186_; lean_object* v_keys_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1204_; 
v_vals_1186_ = lean_ctor_get(v_a_1163_, 1);
v_keys_1187_ = lean_ctor_get(v_a_1163_, 0);
v_a_1188_ = lean_ctor_get(v_a_1163_, 2);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_a_1163_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1190_ = v_a_1163_;
v_isShared_1191_ = v_isSharedCheck_1204_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_inc(v_vals_1186_);
lean_inc(v_keys_1187_);
lean_dec(v_a_1163_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1204_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_start_1192_; lean_object* v_stop_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v_start_1192_ = lean_ctor_get(v_vals_1186_, 1);
v_stop_1193_ = lean_ctor_get(v_vals_1186_, 2);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_nat_sub(v_stop_1193_, v_start_1192_);
v___x_1196_ = lean_nat_dec_lt(v___x_1194_, v___x_1195_);
lean_dec(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_del_object(v___x_1190_);
lean_dec_ref(v_keys_1187_);
lean_dec_ref(v_vals_1186_);
v_it_1085_ = v_a_1188_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_1187_);
v___x_1198_ = l_Subarray_drop___redArg(v_keys_1187_, v___x_1197_);
v___x_1199_ = l_Subarray_drop___redArg(v_vals_1186_, v___x_1197_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1199_);
lean_ctor_set(v___x_1190_, 0, v___x_1198_);
v___x_1201_ = v___x_1190_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_a_1188_);
v___x_1201_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Subarray_get___redArg(v_keys_1187_, v___x_1194_);
lean_dec_ref(v_keys_1187_);
v_it_1123_ = v___x_1201_;
v_fst_1124_ = v___x_1202_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object* v_ctx_1205_, lean_object* v_id_1206_, lean_object* v_danglingDot_1207_, lean_object* v___x_1208_, lean_object* v_a_1209_, lean_object* v_b_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_danglingDot_boxed_1219_; lean_object* v_res_1220_; 
v_danglingDot_boxed_1219_ = lean_unbox(v_danglingDot_1207_);
v_res_1220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1205_, v_id_1206_, v_danglingDot_boxed_1219_, v___x_1208_, v_a_1209_, v_b_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object* v_ctx_1221_, lean_object* v_id_1222_, uint8_t v_danglingDot_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_env_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1232_ = lean_st_ref_get(v_a_1230_);
v_env_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref_n(v_env_1233_, 2);
lean_dec(v___x_1232_);
v___x_1234_ = l_Lean_Environment_getNamespaces(v_env_1233_);
v___x_1235_ = lean_box(0);
v___x_1236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1221_, v_id_1222_, v_danglingDot_1223_, v_env_1233_, v___x_1234_, v___x_1235_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
if (lean_obj_tag(v_a_1237_) == 0)
{
lean_dec_ref_known(v_a_1237_, 1);
return v___x_1236_;
}
else
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref_known(v_a_1237_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1246_);
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
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
else
{
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object* v_ctx_1247_, lean_object* v_id_1248_, lean_object* v_danglingDot_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
uint8_t v_danglingDot_boxed_1258_; lean_object* v_res_1259_; 
v_danglingDot_boxed_1258_ = lean_unbox(v_danglingDot_1249_);
v_res_1259_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1247_, v_id_1248_, v_danglingDot_boxed_1258_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object* v_ctx_1260_, lean_object* v_id_1261_, uint8_t v_danglingDot_1262_, lean_object* v___x_1263_, lean_object* v_inst_1264_, lean_object* v_R_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_c_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1260_, v_id_1261_, v_danglingDot_1262_, v___x_1263_, v_a_1266_, v_b_1267_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object** _args){
lean_object* v_ctx_1278_ = _args[0];
lean_object* v_id_1279_ = _args[1];
lean_object* v_danglingDot_1280_ = _args[2];
lean_object* v___x_1281_ = _args[3];
lean_object* v_inst_1282_ = _args[4];
lean_object* v_R_1283_ = _args[5];
lean_object* v_a_1284_ = _args[6];
lean_object* v_b_1285_ = _args[7];
lean_object* v_c_1286_ = _args[8];
lean_object* v___y_1287_ = _args[9];
lean_object* v___y_1288_ = _args[10];
lean_object* v___y_1289_ = _args[11];
lean_object* v___y_1290_ = _args[12];
lean_object* v___y_1291_ = _args[13];
lean_object* v___y_1292_ = _args[14];
lean_object* v___y_1293_ = _args[15];
lean_object* v___y_1294_ = _args[16];
_start:
{
uint8_t v_danglingDot_boxed_1295_; lean_object* v_res_1296_; 
v_danglingDot_boxed_1295_ = lean_unbox(v_danglingDot_1280_);
v_res_1296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_ctx_1278_, v_id_1279_, v_danglingDot_boxed_1295_, v___x_1281_, v_inst_1282_, v_R_1283_, v_a_1284_, v_b_1285_, v_c_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* v_n_1297_){
_start:
{
if (lean_obj_tag(v_n_1297_) == 2)
{
lean_object* v_i_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_i_1298_ = lean_ctor_get(v_n_1297_, 1);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_nat_dec_eq(v_i_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_inc_ref(v_n_1297_);
return v_n_1297_;
}
else
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_isPrivatePrefix(v_n_1297_);
if (v___x_1301_ == 0)
{
lean_inc_ref(v_n_1297_);
return v_n_1297_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
}
}
else
{
lean_inc(v_n_1297_);
return v_n_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* v_n_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_1303_);
lean_dec(v_n_1303_);
return v_res_1304_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* v_n_u2081_1305_, lean_object* v_n_u2082_1306_){
_start:
{
lean_object* v_n_u2081_1307_; lean_object* v_n_u2082_1308_; 
v_n_u2081_1307_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2081_1305_);
lean_dec(v_n_u2081_1305_);
v_n_u2082_1308_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2082_1306_);
lean_dec(v_n_u2082_1306_);
switch(lean_obj_tag(v_n_u2081_1307_))
{
case 0:
{
if (lean_obj_tag(v_n_u2082_1308_) == 0)
{
uint8_t v___x_1309_; 
v___x_1309_ = 1;
return v___x_1309_;
}
else
{
uint8_t v___x_1310_; 
lean_dec(v_n_u2082_1308_);
v___x_1310_ = 0;
return v___x_1310_;
}
}
case 1:
{
if (lean_obj_tag(v_n_u2082_1308_) == 1)
{
lean_object* v_pre_1311_; lean_object* v_str_1312_; lean_object* v_pre_1313_; lean_object* v_str_1314_; uint8_t v___x_1315_; 
v_pre_1311_ = lean_ctor_get(v_n_u2081_1307_, 0);
lean_inc(v_pre_1311_);
v_str_1312_ = lean_ctor_get(v_n_u2081_1307_, 1);
lean_inc_ref(v_str_1312_);
lean_dec_ref_known(v_n_u2081_1307_, 2);
v_pre_1313_ = lean_ctor_get(v_n_u2082_1308_, 0);
lean_inc(v_pre_1313_);
v_str_1314_ = lean_ctor_get(v_n_u2082_1308_, 1);
lean_inc_ref(v_str_1314_);
lean_dec_ref_known(v_n_u2082_1308_, 2);
v___x_1315_ = lean_string_compare(v_str_1312_, v_str_1314_);
lean_dec_ref(v_str_1314_);
lean_dec_ref(v_str_1312_);
if (v___x_1315_ == 1)
{
v_n_u2081_1305_ = v_pre_1311_;
v_n_u2082_1306_ = v_pre_1313_;
goto _start;
}
else
{
lean_dec(v_pre_1313_);
lean_dec(v_pre_1311_);
return v___x_1315_;
}
}
else
{
uint8_t v___x_1317_; 
lean_dec_ref_known(v_n_u2081_1307_, 2);
lean_dec(v_n_u2082_1308_);
v___x_1317_ = 2;
return v___x_1317_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1308_))
{
case 0:
{
uint8_t v___x_1318_; 
lean_dec_ref_known(v_n_u2081_1307_, 2);
v___x_1318_ = 2;
return v___x_1318_;
}
case 1:
{
uint8_t v___x_1319_; 
lean_dec_ref_known(v_n_u2082_1308_, 2);
lean_dec_ref_known(v_n_u2081_1307_, 2);
v___x_1319_ = 0;
return v___x_1319_;
}
default: 
{
lean_object* v_pre_1320_; lean_object* v_i_1321_; lean_object* v_pre_1322_; lean_object* v_i_1323_; uint8_t v___x_1324_; 
v_pre_1320_ = lean_ctor_get(v_n_u2081_1307_, 0);
lean_inc(v_pre_1320_);
v_i_1321_ = lean_ctor_get(v_n_u2081_1307_, 1);
lean_inc(v_i_1321_);
lean_dec_ref_known(v_n_u2081_1307_, 2);
v_pre_1322_ = lean_ctor_get(v_n_u2082_1308_, 0);
lean_inc(v_pre_1322_);
v_i_1323_ = lean_ctor_get(v_n_u2082_1308_, 1);
lean_inc(v_i_1323_);
lean_dec_ref_known(v_n_u2082_1308_, 2);
v___x_1324_ = lean_nat_dec_lt(v_i_1321_, v_i_1323_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_nat_dec_eq(v_i_1321_, v_i_1323_);
lean_dec(v_i_1323_);
lean_dec(v_i_1321_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
lean_dec(v_pre_1322_);
lean_dec(v_pre_1320_);
v___x_1326_ = 2;
return v___x_1326_;
}
else
{
v_n_u2081_1305_ = v_pre_1320_;
v_n_u2082_1306_ = v_pre_1322_;
goto _start;
}
}
else
{
uint8_t v___x_1328_; 
lean_dec(v_i_1323_);
lean_dec(v_pre_1322_);
lean_dec(v_i_1321_);
lean_dec(v_pre_1320_);
v___x_1328_ = 0;
return v___x_1328_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1329_, lean_object* v_n_u2082_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1329_, v_n_u2082_1330_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1336_ = l_Std_TreeSet_ofArray___redArg(v_names_1334_, v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1337_);
lean_dec_ref(v_names_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1339_, lean_object* v_t_1340_){
_start:
{
if (lean_obj_tag(v_t_1340_) == 0)
{
lean_object* v_k_1341_; lean_object* v_l_1342_; lean_object* v_r_1343_; uint8_t v___x_1344_; 
v_k_1341_ = lean_ctor_get(v_t_1340_, 1);
lean_inc(v_k_1341_);
v_l_1342_ = lean_ctor_get(v_t_1340_, 3);
lean_inc(v_l_1342_);
v_r_1343_ = lean_ctor_get(v_t_1340_, 4);
lean_inc(v_r_1343_);
lean_dec_ref_known(v_t_1340_, 5);
lean_inc(v_k_1339_);
v___x_1344_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1339_, v_k_1341_);
switch(v___x_1344_)
{
case 0:
{
lean_dec(v_r_1343_);
v_t_1340_ = v_l_1342_;
goto _start;
}
case 1:
{
uint8_t v___x_1346_; 
lean_dec(v_r_1343_);
lean_dec(v_l_1342_);
lean_dec(v_k_1339_);
v___x_1346_ = 1;
return v___x_1346_;
}
default: 
{
lean_dec(v_l_1342_);
v_t_1340_ = v_r_1343_;
goto _start;
}
}
}
else
{
uint8_t v___x_1348_; 
lean_dec(v_k_1339_);
v___x_1348_ = 0;
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1349_, lean_object* v_t_1350_){
_start:
{
uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1349_, v_t_1350_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1353_, lean_object* v_v_1354_, lean_object* v_t_1355_){
_start:
{
if (lean_obj_tag(v_t_1355_) == 0)
{
lean_object* v_size_1356_; lean_object* v_k_1357_; lean_object* v_v_1358_; lean_object* v_l_1359_; lean_object* v_r_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1640_; 
v_size_1356_ = lean_ctor_get(v_t_1355_, 0);
v_k_1357_ = lean_ctor_get(v_t_1355_, 1);
v_v_1358_ = lean_ctor_get(v_t_1355_, 2);
v_l_1359_ = lean_ctor_get(v_t_1355_, 3);
v_r_1360_ = lean_ctor_get(v_t_1355_, 4);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_t_1355_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1362_ = v_t_1355_;
v_isShared_1363_ = v_isSharedCheck_1640_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_r_1360_);
lean_inc(v_l_1359_);
lean_inc(v_v_1358_);
lean_inc(v_k_1357_);
lean_inc(v_size_1356_);
lean_dec(v_t_1355_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1640_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
uint8_t v___x_1364_; 
lean_inc(v_k_1357_);
lean_inc(v_k_1353_);
v___x_1364_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1353_, v_k_1357_);
switch(v___x_1364_)
{
case 0:
{
lean_object* v_impl_1365_; lean_object* v___x_1366_; 
lean_dec(v_size_1356_);
v_impl_1365_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1353_, v_v_1354_, v_l_1359_);
v___x_1366_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1360_) == 0)
{
lean_object* v_size_1367_; lean_object* v_size_1368_; lean_object* v_k_1369_; lean_object* v_v_1370_; lean_object* v_l_1371_; lean_object* v_r_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_size_1367_ = lean_ctor_get(v_r_1360_, 0);
v_size_1368_ = lean_ctor_get(v_impl_1365_, 0);
lean_inc(v_size_1368_);
v_k_1369_ = lean_ctor_get(v_impl_1365_, 1);
lean_inc(v_k_1369_);
v_v_1370_ = lean_ctor_get(v_impl_1365_, 2);
lean_inc(v_v_1370_);
v_l_1371_ = lean_ctor_get(v_impl_1365_, 3);
lean_inc(v_l_1371_);
v_r_1372_ = lean_ctor_get(v_impl_1365_, 4);
lean_inc(v_r_1372_);
v___x_1373_ = lean_unsigned_to_nat(3u);
v___x_1374_ = lean_nat_mul(v___x_1373_, v_size_1367_);
v___x_1375_ = lean_nat_dec_lt(v___x_1374_, v_size_1368_);
lean_dec(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec(v_r_1372_);
lean_dec(v_l_1371_);
lean_dec(v_v_1370_);
lean_dec(v_k_1369_);
v___x_1376_ = lean_nat_add(v___x_1366_, v_size_1368_);
lean_dec(v_size_1368_);
v___x_1377_ = lean_nat_add(v___x_1376_, v_size_1367_);
lean_dec(v___x_1376_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 3, v_impl_1365_);
lean_ctor_set(v___x_1362_, 0, v___x_1377_);
v___x_1379_ = v___x_1362_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_impl_1365_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_r_1360_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1446_; 
v_isSharedCheck_1446_ = !lean_is_exclusive(v_impl_1365_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; 
v_unused_1447_ = lean_ctor_get(v_impl_1365_, 4);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_impl_1365_, 3);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_impl_1365_, 2);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_impl_1365_, 1);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_impl_1365_, 0);
lean_dec(v_unused_1451_);
v___x_1382_ = v_impl_1365_;
v_isShared_1383_ = v_isSharedCheck_1446_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v_impl_1365_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1446_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_size_1384_; lean_object* v_size_1385_; lean_object* v_k_1386_; lean_object* v_v_1387_; lean_object* v_l_1388_; lean_object* v_r_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_size_1384_ = lean_ctor_get(v_l_1371_, 0);
v_size_1385_ = lean_ctor_get(v_r_1372_, 0);
v_k_1386_ = lean_ctor_get(v_r_1372_, 1);
v_v_1387_ = lean_ctor_get(v_r_1372_, 2);
v_l_1388_ = lean_ctor_get(v_r_1372_, 3);
v_r_1389_ = lean_ctor_get(v_r_1372_, 4);
v___x_1390_ = lean_unsigned_to_nat(2u);
v___x_1391_ = lean_nat_mul(v___x_1390_, v_size_1384_);
v___x_1392_ = lean_nat_dec_lt(v_size_1385_, v___x_1391_);
lean_dec(v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1421_; 
lean_inc(v_r_1389_);
lean_inc(v_l_1388_);
lean_inc(v_v_1387_);
lean_inc(v_k_1386_);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_r_1372_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; 
v_unused_1422_ = lean_ctor_get(v_r_1372_, 4);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_r_1372_, 3);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_r_1372_, 2);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_r_1372_, 1);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_r_1372_, 0);
lean_dec(v_unused_1426_);
v___x_1394_ = v_r_1372_;
v_isShared_1395_ = v_isSharedCheck_1421_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_r_1372_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1421_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___x_1409_; lean_object* v___y_1411_; 
v___x_1396_ = lean_nat_add(v___x_1366_, v_size_1368_);
lean_dec(v_size_1368_);
v___x_1397_ = lean_nat_add(v___x_1396_, v_size_1367_);
lean_dec(v___x_1396_);
v___x_1409_ = lean_nat_add(v___x_1366_, v_size_1384_);
if (lean_obj_tag(v_l_1388_) == 0)
{
lean_object* v_size_1419_; 
v_size_1419_ = lean_ctor_get(v_l_1388_, 0);
lean_inc(v_size_1419_);
v___y_1411_ = v_size_1419_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___y_1411_ = v___x_1420_;
goto v___jp_1410_;
}
v___jp_1398_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_nat_add(v___y_1399_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec(v___y_1399_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_r_1360_);
lean_ctor_set(v___x_1394_, 3, v_r_1389_);
lean_ctor_set(v___x_1394_, 2, v_v_1358_);
lean_ctor_set(v___x_1394_, 1, v_k_1357_);
lean_ctor_set(v___x_1394_, 0, v___x_1402_);
v___x_1404_ = v___x_1394_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_r_1389_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_r_1360_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 4, v___x_1404_);
lean_ctor_set(v___x_1382_, 3, v___y_1400_);
lean_ctor_set(v___x_1382_, 2, v_v_1387_);
lean_ctor_set(v___x_1382_, 1, v_k_1386_);
lean_ctor_set(v___x_1382_, 0, v___x_1397_);
v___x_1406_ = v___x_1382_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v___y_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
v___jp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_nat_add(v___x_1409_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___x_1409_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_l_1388_);
lean_ctor_set(v___x_1362_, 3, v_l_1371_);
lean_ctor_set(v___x_1362_, 2, v_v_1370_);
lean_ctor_set(v___x_1362_, 1, v_k_1369_);
lean_ctor_set(v___x_1362_, 0, v___x_1412_);
v___x_1414_ = v___x_1362_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1369_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1370_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_l_1371_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_l_1388_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_nat_add(v___x_1366_, v_size_1367_);
if (lean_obj_tag(v_r_1389_) == 0)
{
lean_object* v_size_1416_; 
v_size_1416_ = lean_ctor_get(v_r_1389_, 0);
lean_inc(v_size_1416_);
v___y_1399_ = v___x_1415_;
v___y_1400_ = v___x_1414_;
v___y_1401_ = v_size_1416_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v___y_1399_ = v___x_1415_;
v___y_1400_ = v___x_1414_;
v___y_1401_ = v___x_1417_;
goto v___jp_1398_;
}
}
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_del_object(v___x_1362_);
v___x_1427_ = lean_nat_add(v___x_1366_, v_size_1368_);
lean_dec(v_size_1368_);
v___x_1428_ = lean_nat_add(v___x_1427_, v_size_1367_);
lean_dec(v___x_1427_);
v___x_1429_ = lean_nat_add(v___x_1366_, v_size_1367_);
v___x_1430_ = lean_nat_add(v___x_1429_, v_size_1385_);
lean_dec(v___x_1429_);
lean_inc_ref(v_r_1360_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 4, v_r_1360_);
lean_ctor_set(v___x_1382_, 3, v_r_1372_);
lean_ctor_set(v___x_1382_, 2, v_v_1358_);
lean_ctor_set(v___x_1382_, 1, v_k_1357_);
lean_ctor_set(v___x_1382_, 0, v___x_1430_);
v___x_1432_ = v___x_1382_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_r_1372_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1360_);
v___x_1432_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v_r_1360_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; 
v_unused_1440_ = lean_ctor_get(v_r_1360_, 4);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_r_1360_, 3);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_r_1360_, 2);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_r_1360_, 1);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_r_1360_, 0);
lean_dec(v_unused_1444_);
v___x_1434_ = v_r_1360_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v_r_1360_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 4, v___x_1432_);
lean_ctor_set(v___x_1434_, 3, v_l_1371_);
lean_ctor_set(v___x_1434_, 2, v_v_1370_);
lean_ctor_set(v___x_1434_, 1, v_k_1369_);
lean_ctor_set(v___x_1434_, 0, v___x_1428_);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1369_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1370_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_l_1371_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v___x_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1452_; 
v_l_1452_ = lean_ctor_get(v_impl_1365_, 3);
lean_inc(v_l_1452_);
if (lean_obj_tag(v_l_1452_) == 0)
{
lean_object* v_r_1453_; lean_object* v_k_1454_; lean_object* v_v_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1466_; 
v_r_1453_ = lean_ctor_get(v_impl_1365_, 4);
v_k_1454_ = lean_ctor_get(v_impl_1365_, 1);
v_v_1455_ = lean_ctor_get(v_impl_1365_, 2);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_impl_1365_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; lean_object* v_unused_1468_; 
v_unused_1467_ = lean_ctor_get(v_impl_1365_, 3);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_impl_1365_, 0);
lean_dec(v_unused_1468_);
v___x_1457_ = v_impl_1365_;
v_isShared_1458_ = v_isSharedCheck_1466_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_r_1453_);
lean_inc(v_v_1455_);
lean_inc(v_k_1454_);
lean_dec(v_impl_1365_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1466_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1453_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 3, v_r_1453_);
lean_ctor_set(v___x_1457_, 2, v_v_1358_);
lean_ctor_set(v___x_1457_, 1, v_k_1357_);
lean_ctor_set(v___x_1457_, 0, v___x_1366_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_r_1453_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_r_1453_);
v___x_1461_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v___x_1461_);
lean_ctor_set(v___x_1362_, 3, v_l_1452_);
lean_ctor_set(v___x_1362_, 2, v_v_1455_);
lean_ctor_set(v___x_1362_, 1, v_k_1454_);
lean_ctor_set(v___x_1362_, 0, v___x_1459_);
v___x_1463_ = v___x_1362_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1454_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1455_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_l_1452_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v___x_1461_);
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
else
{
lean_object* v_r_1469_; 
v_r_1469_ = lean_ctor_get(v_impl_1365_, 4);
lean_inc(v_r_1469_);
if (lean_obj_tag(v_r_1469_) == 0)
{
lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1494_; 
v_k_1470_ = lean_ctor_get(v_impl_1365_, 1);
v_v_1471_ = lean_ctor_get(v_impl_1365_, 2);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_impl_1365_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; lean_object* v_unused_1496_; lean_object* v_unused_1497_; 
v_unused_1495_ = lean_ctor_get(v_impl_1365_, 4);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_impl_1365_, 3);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_impl_1365_, 0);
lean_dec(v_unused_1497_);
v___x_1473_ = v_impl_1365_;
v_isShared_1474_ = v_isSharedCheck_1494_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
lean_dec(v_impl_1365_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1494_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_k_1475_; lean_object* v_v_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1490_; 
v_k_1475_ = lean_ctor_get(v_r_1469_, 1);
v_v_1476_ = lean_ctor_get(v_r_1469_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_r_1469_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1491_ = lean_ctor_get(v_r_1469_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_r_1469_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_r_1469_, 0);
lean_dec(v_unused_1493_);
v___x_1478_ = v_r_1469_;
v_isShared_1479_ = v_isSharedCheck_1490_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_v_1476_);
lean_inc(v_k_1475_);
lean_dec(v_r_1469_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1490_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_unsigned_to_nat(3u);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 4, v_l_1452_);
lean_ctor_set(v___x_1478_, 3, v_l_1452_);
lean_ctor_set(v___x_1478_, 2, v_v_1471_);
lean_ctor_set(v___x_1478_, 1, v_k_1470_);
lean_ctor_set(v___x_1478_, 0, v___x_1366_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_l_1452_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_l_1452_);
v___x_1482_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v_l_1452_);
lean_ctor_set(v___x_1473_, 2, v_v_1358_);
lean_ctor_set(v___x_1473_, 1, v_k_1357_);
lean_ctor_set(v___x_1473_, 0, v___x_1366_);
v___x_1484_ = v___x_1473_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_l_1452_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v_l_1452_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v___x_1484_);
lean_ctor_set(v___x_1362_, 3, v___x_1482_);
lean_ctor_set(v___x_1362_, 2, v_v_1476_);
lean_ctor_set(v___x_1362_, 1, v_k_1475_);
lean_ctor_set(v___x_1362_, 0, v___x_1480_);
v___x_1486_ = v___x_1362_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v___x_1484_);
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
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_unsigned_to_nat(2u);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1469_);
lean_ctor_set(v___x_1362_, 3, v_impl_1365_);
lean_ctor_set(v___x_1362_, 0, v___x_1498_);
v___x_1500_ = v___x_1362_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_impl_1365_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1469_);
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
case 1:
{
lean_object* v___x_1503_; 
lean_dec(v_v_1358_);
lean_dec(v_k_1357_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 2, v_v_1354_);
lean_ctor_set(v___x_1362_, 1, v_k_1353_);
v___x_1503_ = v___x_1362_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_size_1356_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_l_1359_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1360_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
default: 
{
lean_object* v_impl_1505_; lean_object* v___x_1506_; 
lean_dec(v_size_1356_);
v_impl_1505_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1353_, v_v_1354_, v_r_1360_);
v___x_1506_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1359_) == 0)
{
lean_object* v_size_1507_; lean_object* v_size_1508_; lean_object* v_k_1509_; lean_object* v_v_1510_; lean_object* v_l_1511_; lean_object* v_r_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_size_1507_ = lean_ctor_get(v_l_1359_, 0);
v_size_1508_ = lean_ctor_get(v_impl_1505_, 0);
lean_inc(v_size_1508_);
v_k_1509_ = lean_ctor_get(v_impl_1505_, 1);
lean_inc(v_k_1509_);
v_v_1510_ = lean_ctor_get(v_impl_1505_, 2);
lean_inc(v_v_1510_);
v_l_1511_ = lean_ctor_get(v_impl_1505_, 3);
lean_inc(v_l_1511_);
v_r_1512_ = lean_ctor_get(v_impl_1505_, 4);
lean_inc(v_r_1512_);
v___x_1513_ = lean_unsigned_to_nat(3u);
v___x_1514_ = lean_nat_mul(v___x_1513_, v_size_1507_);
v___x_1515_ = lean_nat_dec_lt(v___x_1514_, v_size_1508_);
lean_dec(v___x_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_dec(v_r_1512_);
lean_dec(v_l_1511_);
lean_dec(v_v_1510_);
lean_dec(v_k_1509_);
v___x_1516_ = lean_nat_add(v___x_1506_, v_size_1507_);
v___x_1517_ = lean_nat_add(v___x_1516_, v_size_1508_);
lean_dec(v_size_1508_);
lean_dec(v___x_1516_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_impl_1505_);
lean_ctor_set(v___x_1362_, 0, v___x_1517_);
v___x_1519_ = v___x_1362_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_l_1359_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_impl_1505_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
else
{
lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v_impl_1505_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1585_ = lean_ctor_get(v_impl_1505_, 4);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_impl_1505_, 3);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_impl_1505_, 2);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_impl_1505_, 1);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_impl_1505_, 0);
lean_dec(v_unused_1589_);
v___x_1522_ = v_impl_1505_;
v_isShared_1523_ = v_isSharedCheck_1584_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v_impl_1505_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1584_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_size_1524_; lean_object* v_k_1525_; lean_object* v_v_1526_; lean_object* v_l_1527_; lean_object* v_r_1528_; lean_object* v_size_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_size_1524_ = lean_ctor_get(v_l_1511_, 0);
v_k_1525_ = lean_ctor_get(v_l_1511_, 1);
v_v_1526_ = lean_ctor_get(v_l_1511_, 2);
v_l_1527_ = lean_ctor_get(v_l_1511_, 3);
v_r_1528_ = lean_ctor_get(v_l_1511_, 4);
v_size_1529_ = lean_ctor_get(v_r_1512_, 0);
v___x_1530_ = lean_unsigned_to_nat(2u);
v___x_1531_ = lean_nat_mul(v___x_1530_, v_size_1529_);
v___x_1532_ = lean_nat_dec_lt(v_size_1524_, v___x_1531_);
lean_dec(v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1560_; 
lean_inc(v_r_1528_);
lean_inc(v_l_1527_);
lean_inc(v_v_1526_);
lean_inc(v_k_1525_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_l_1511_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; 
v_unused_1561_ = lean_ctor_get(v_l_1511_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_l_1511_, 3);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_l_1511_, 2);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_l_1511_, 1);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_l_1511_, 0);
lean_dec(v_unused_1565_);
v___x_1534_ = v_l_1511_;
v_isShared_1535_ = v_isSharedCheck_1560_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v_l_1511_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1560_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1550_; 
v___x_1536_ = lean_nat_add(v___x_1506_, v_size_1507_);
v___x_1537_ = lean_nat_add(v___x_1536_, v_size_1508_);
lean_dec(v_size_1508_);
if (lean_obj_tag(v_l_1527_) == 0)
{
lean_object* v_size_1558_; 
v_size_1558_ = lean_ctor_get(v_l_1527_, 0);
lean_inc(v_size_1558_);
v___y_1550_ = v_size_1558_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___y_1550_ = v___x_1559_;
goto v___jp_1549_;
}
v___jp_1538_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_nat_add(v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec(v___y_1540_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 4, v_r_1512_);
lean_ctor_set(v___x_1534_, 3, v_r_1528_);
lean_ctor_set(v___x_1534_, 2, v_v_1510_);
lean_ctor_set(v___x_1534_, 1, v_k_1509_);
lean_ctor_set(v___x_1534_, 0, v___x_1542_);
v___x_1544_ = v___x_1534_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1512_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 4, v___x_1544_);
lean_ctor_set(v___x_1522_, 3, v___y_1539_);
lean_ctor_set(v___x_1522_, 2, v_v_1526_);
lean_ctor_set(v___x_1522_, 1, v_k_1525_);
lean_ctor_set(v___x_1522_, 0, v___x_1537_);
v___x_1546_ = v___x_1522_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1525_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1526_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___y_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
v___jp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_nat_add(v___x_1536_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec(v___x_1536_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_l_1527_);
lean_ctor_set(v___x_1362_, 0, v___x_1551_);
v___x_1553_ = v___x_1362_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_l_1359_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_l_1527_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_nat_add(v___x_1506_, v_size_1529_);
if (lean_obj_tag(v_r_1528_) == 0)
{
lean_object* v_size_1555_; 
v_size_1555_ = lean_ctor_get(v_r_1528_, 0);
lean_inc(v_size_1555_);
v___y_1539_ = v___x_1553_;
v___y_1540_ = v___x_1554_;
v___y_1541_ = v_size_1555_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_unsigned_to_nat(0u);
v___y_1539_ = v___x_1553_;
v___y_1540_ = v___x_1554_;
v___y_1541_ = v___x_1556_;
goto v___jp_1538_;
}
}
}
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_del_object(v___x_1362_);
v___x_1566_ = lean_nat_add(v___x_1506_, v_size_1507_);
v___x_1567_ = lean_nat_add(v___x_1566_, v_size_1508_);
lean_dec(v_size_1508_);
v___x_1568_ = lean_nat_add(v___x_1566_, v_size_1524_);
lean_dec(v___x_1566_);
lean_inc_ref(v_l_1359_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 4, v_l_1511_);
lean_ctor_set(v___x_1522_, 3, v_l_1359_);
lean_ctor_set(v___x_1522_, 2, v_v_1358_);
lean_ctor_set(v___x_1522_, 1, v_k_1357_);
lean_ctor_set(v___x_1522_, 0, v___x_1568_);
v___x_1570_ = v___x_1522_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_l_1359_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_l_1511_);
v___x_1570_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_isSharedCheck_1577_ = !lean_is_exclusive(v_l_1359_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; lean_object* v_unused_1579_; lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1578_ = lean_ctor_get(v_l_1359_, 4);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_l_1359_, 3);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v_l_1359_, 2);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_l_1359_, 1);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_l_1359_, 0);
lean_dec(v_unused_1582_);
v___x_1572_ = v_l_1359_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_l_1359_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 4, v_r_1512_);
lean_ctor_set(v___x_1572_, 3, v___x_1570_);
lean_ctor_set(v___x_1572_, 2, v_v_1510_);
lean_ctor_set(v___x_1572_, 1, v_k_1509_);
lean_ctor_set(v___x_1572_, 0, v___x_1567_);
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_r_1512_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1590_; 
v_l_1590_ = lean_ctor_get(v_impl_1505_, 3);
lean_inc(v_l_1590_);
if (lean_obj_tag(v_l_1590_) == 0)
{
lean_object* v_r_1591_; lean_object* v_k_1592_; lean_object* v_v_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1616_; 
v_r_1591_ = lean_ctor_get(v_impl_1505_, 4);
v_k_1592_ = lean_ctor_get(v_impl_1505_, 1);
v_v_1593_ = lean_ctor_get(v_impl_1505_, 2);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_impl_1505_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; 
v_unused_1617_ = lean_ctor_get(v_impl_1505_, 3);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_impl_1505_, 0);
lean_dec(v_unused_1618_);
v___x_1595_ = v_impl_1505_;
v_isShared_1596_ = v_isSharedCheck_1616_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_r_1591_);
lean_inc(v_v_1593_);
lean_inc(v_k_1592_);
lean_dec(v_impl_1505_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1616_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_k_1597_; lean_object* v_v_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1612_; 
v_k_1597_ = lean_ctor_get(v_l_1590_, 1);
v_v_1598_ = lean_ctor_get(v_l_1590_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_l_1590_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; 
v_unused_1613_ = lean_ctor_get(v_l_1590_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_l_1590_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_l_1590_, 0);
lean_dec(v_unused_1615_);
v___x_1600_ = v_l_1590_;
v_isShared_1601_ = v_isSharedCheck_1612_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_v_1598_);
lean_inc(v_k_1597_);
lean_dec(v_l_1590_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1612_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1591_, 2);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 4, v_r_1591_);
lean_ctor_set(v___x_1600_, 3, v_r_1591_);
lean_ctor_set(v___x_1600_, 2, v_v_1358_);
lean_ctor_set(v___x_1600_, 1, v_k_1357_);
lean_ctor_set(v___x_1600_, 0, v___x_1506_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_r_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_r_1591_);
v___x_1604_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
lean_inc(v_r_1591_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 3, v_r_1591_);
lean_ctor_set(v___x_1595_, 0, v___x_1506_);
v___x_1606_ = v___x_1595_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_r_1591_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1591_);
v___x_1606_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v___x_1606_);
lean_ctor_set(v___x_1362_, 3, v___x_1604_);
lean_ctor_set(v___x_1362_, 2, v_v_1598_);
lean_ctor_set(v___x_1362_, 1, v_k_1597_);
lean_ctor_set(v___x_1362_, 0, v___x_1602_);
v___x_1608_ = v___x_1362_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1597_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1598_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
}
else
{
lean_object* v_r_1619_; 
v_r_1619_ = lean_ctor_get(v_impl_1505_, 4);
lean_inc(v_r_1619_);
if (lean_obj_tag(v_r_1619_) == 0)
{
lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1632_; 
v_k_1620_ = lean_ctor_get(v_impl_1505_, 1);
v_v_1621_ = lean_ctor_get(v_impl_1505_, 2);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_impl_1505_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; lean_object* v_unused_1634_; lean_object* v_unused_1635_; 
v_unused_1633_ = lean_ctor_get(v_impl_1505_, 4);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_impl_1505_, 3);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_impl_1505_, 0);
lean_dec(v_unused_1635_);
v___x_1623_ = v_impl_1505_;
v_isShared_1624_ = v_isSharedCheck_1632_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_v_1621_);
lean_inc(v_k_1620_);
lean_dec(v_impl_1505_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1632_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_unsigned_to_nat(3u);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_l_1590_);
lean_ctor_set(v___x_1623_, 2, v_v_1358_);
lean_ctor_set(v___x_1623_, 1, v_k_1357_);
lean_ctor_set(v___x_1623_, 0, v___x_1506_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_l_1590_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_l_1590_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1619_);
lean_ctor_set(v___x_1362_, 3, v___x_1627_);
lean_ctor_set(v___x_1362_, 2, v_v_1621_);
lean_ctor_set(v___x_1362_, 1, v_k_1620_);
lean_ctor_set(v___x_1362_, 0, v___x_1625_);
v___x_1629_ = v___x_1362_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_r_1619_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = lean_unsigned_to_nat(2u);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_impl_1505_);
lean_ctor_set(v___x_1362_, 3, v_r_1619_);
lean_ctor_set(v___x_1362_, 0, v___x_1636_);
v___x_1638_ = v___x_1362_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_r_1619_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_impl_1505_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
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
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_k_1353_);
lean_ctor_set(v___x_1642_, 2, v_v_1354_);
lean_ctor_set(v___x_1642_, 3, v_t_1355_);
lean_ctor_set(v___x_1642_, 4, v_t_1355_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_1643_, size_t v_sz_1644_, size_t v_i_1645_, lean_object* v_b_1646_){
_start:
{
lean_object* v___y_1649_; uint8_t v___x_1653_; 
v___x_1653_ = lean_usize_dec_lt(v_i_1645_, v_sz_1644_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_b_1646_);
return v___x_1654_;
}
else
{
lean_object* v_a_1655_; uint8_t v___x_1656_; 
v_a_1655_ = lean_array_uget_borrowed(v_as_1643_, v_i_1645_);
lean_inc(v_b_1646_);
lean_inc(v_a_1655_);
v___x_1656_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_1655_, v_b_1646_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_box(0);
lean_inc(v_a_1655_);
v___x_1658_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_1655_, v___x_1657_, v_b_1646_);
v___y_1649_ = v___x_1658_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v_b_1646_;
goto v___jp_1648_;
}
}
v___jp_1648_:
{
size_t v___x_1650_; size_t v___x_1651_; 
v___x_1650_ = ((size_t)1ULL);
v___x_1651_ = lean_usize_add(v_i_1645_, v___x_1650_);
v_i_1645_ = v___x_1651_;
v_b_1646_ = v___y_1649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_1659_, lean_object* v_sz_1660_, lean_object* v_i_1661_, lean_object* v_b_1662_, lean_object* v___y_1663_){
_start:
{
size_t v_sz_boxed_1664_; size_t v_i_boxed_1665_; lean_object* v_res_1666_; 
v_sz_boxed_1664_ = lean_unbox_usize(v_sz_1660_);
lean_dec(v_sz_1660_);
v_i_boxed_1665_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1659_, v_sz_boxed_1664_, v_i_boxed_1665_, v_b_1662_);
lean_dec_ref(v_as_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_set_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_set_1675_ = lean_box(1);
v_sz_1676_ = lean_array_size(v_a_1674_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_1674_, v_sz_1676_, v___x_1677_, v_set_1675_);
lean_dec(v_a_1674_);
return v___x_1678_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1673_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1673_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
return v_res_1693_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_1694_, lean_object* v_k_1695_, lean_object* v_t_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1695_, v_t_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_1698_, lean_object* v_k_1699_, lean_object* v_t_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_1698_, v_k_1699_, v_t_1700_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_1703_, lean_object* v_k_1704_, lean_object* v_v_1705_, lean_object* v_t_1706_, lean_object* v_hl_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1704_, v_v_1705_, v_t_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1709_, v_sz_1710_, v_i_1711_, v_b_1712_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_1719_, lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_b_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
size_t v_sz_boxed_1728_; size_t v_i_boxed_1729_; lean_object* v_res_1730_; 
v_sz_boxed_1728_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1729_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1719_, v_sz_boxed_1728_, v_i_boxed_1729_, v_b_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec_ref(v_as_1719_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_1731_, lean_object* v_declName_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
uint8_t v___y_1739_; uint8_t v___y_1761_; lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Expr_getAppFn(v_e_1731_);
if (lean_obj_tag(v___x_1764_) == 4)
{
lean_object* v_declName_1765_; lean_object* v___x_1766_; 
v_declName_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_n(v_declName_1765_, 2);
lean_dec_ref_known(v___x_1764_, 2);
v___x_1766_ = l_Lean_privateToUserName_x3f(v_declName_1765_);
if (lean_obj_tag(v___x_1766_) == 0)
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_name_eq(v_declName_1765_, v_declName_1732_);
lean_dec(v_declName_1765_);
v___y_1761_ = v___x_1767_;
goto v___jp_1760_;
}
else
{
lean_object* v_val_1768_; uint8_t v___x_1769_; 
lean_dec(v_declName_1765_);
v_val_1768_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1768_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1769_ = lean_name_eq(v_val_1768_, v_declName_1732_);
lean_dec(v_val_1768_);
v___y_1761_ = v___x_1769_;
goto v___jp_1760_;
}
}
else
{
uint8_t v___x_1770_; 
lean_dec_ref(v___x_1764_);
v___x_1770_ = 0;
v___y_1739_ = v___x_1770_;
goto v___jp_1738_;
}
v___jp_1738_:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_1731_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1751_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
if (lean_obj_tag(v_a_1741_) == 1)
{
lean_object* v_val_1745_; 
lean_del_object(v___x_1743_);
v_val_1745_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v_a_1741_, 1);
v_e_1731_ = v_val_1745_;
goto _start;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v_a_1741_);
v___x_1747_ = lean_box(v___y_1739_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1747_);
v___x_1749_ = v___x_1743_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1740_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1740_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
v___jp_1760_:
{
if (v___y_1761_ == 0)
{
v___y_1739_ = v___y_1761_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec_ref(v_e_1731_);
v___x_1762_ = lean_box(v___y_1761_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_1771_, lean_object* v_declName_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1771_, v_declName_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_declName_1772_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_1779_, lean_object* v_b_1780_, lean_object* v_c_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; 
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_1787_ = lean_apply_7(v_k_1779_, v_b_1780_, v_c_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_1788_, lean_object* v_b_1789_, lean_object* v_c_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1788_, v_b_1789_, v_c_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_1797_, lean_object* v_k_1798_, uint8_t v_cleanupAnnotations_1799_, uint8_t v_whnfType_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___f_1806_; lean_object* v___x_1807_; 
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1806_, 0, v_k_1798_);
v___x_1807_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1797_, v___f_1806_, v_cleanupAnnotations_1799_, v_whnfType_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1807_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1807_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_1824_, lean_object* v_k_1825_, lean_object* v_cleanupAnnotations_1826_, lean_object* v_whnfType_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1833_; uint8_t v_whnfType_boxed_1834_; lean_object* v_res_1835_; 
v_cleanupAnnotations_boxed_1833_ = lean_unbox(v_cleanupAnnotations_1826_);
v_whnfType_boxed_1834_ = lean_unbox(v_whnfType_1827_);
v_res_1835_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1824_, v_k_1825_, v_cleanupAnnotations_boxed_1833_, v_whnfType_boxed_1834_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_1836_, lean_object* v_type_1837_, lean_object* v_k_1838_, uint8_t v_cleanupAnnotations_1839_, uint8_t v_whnfType_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1837_, v_k_1838_, v_cleanupAnnotations_1839_, v_whnfType_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_type_1848_, lean_object* v_k_1849_, lean_object* v_cleanupAnnotations_1850_, lean_object* v_whnfType_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1857_; uint8_t v_whnfType_boxed_1858_; lean_object* v_res_1859_; 
v_cleanupAnnotations_boxed_1857_ = lean_unbox(v_cleanupAnnotations_1850_);
v_whnfType_boxed_1858_ = lean_unbox(v_whnfType_1851_);
v_res_1859_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_1847_, v_type_1848_, v_k_1849_, v_cleanupAnnotations_boxed_1857_, v_whnfType_boxed_1858_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_1863_, lean_object* v_as_1864_, size_t v_sz_1865_, size_t v_i_1866_, lean_object* v_b_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_lt(v_i_1866_, v_sz_1865_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_b_1867_);
return v___x_1874_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_b_1867_);
v_a_1875_ = lean_array_uget_borrowed(v_as_1864_, v_i_1866_);
v___x_1876_ = l_Lean_Expr_fvarId_x21(v_a_1875_);
v___x_1877_ = l_Lean_FVarId_getDecl___redArg(v___x_1876_, v___y_1868_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l_Lean_LocalDecl_type(v_a_1878_);
lean_dec(v_a_1878_);
v___x_1880_ = l_Lean_Expr_consumeMData(v___x_1879_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_1880_, v_typeName_1863_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1897_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1897_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1897_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_unbox(v_a_1882_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; 
lean_del_object(v___x_1884_);
lean_dec(v_a_1882_);
v___x_1888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1866_, v___x_1889_);
v_i_1866_ = v___x_1890_;
v_b_1867_ = v___x_1888_;
goto _start;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_a_1882_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1886_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1893_);
v___x_1895_ = v___x_1884_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1881_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1881_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1877_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1877_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_1914_, lean_object* v_as_1915_, lean_object* v_sz_1916_, lean_object* v_i_1917_, lean_object* v_b_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
size_t v_sz_boxed_1924_; size_t v_i_boxed_1925_; lean_object* v_res_1926_; 
v_sz_boxed_1924_ = lean_unbox_usize(v_sz_1916_);
lean_dec(v_sz_1916_);
v_i_boxed_1925_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1914_, v_as_1915_, v_sz_boxed_1924_, v_i_boxed_1925_, v_b_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_as_1915_);
lean_dec(v_typeName_1914_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_1927_, lean_object* v_xs_1928_, lean_object* v_x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; size_t v_sz_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_1936_ = lean_array_size(v_xs_1928_);
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1927_, v_xs_1928_, v_sz_1936_, v___x_1937_, v___x_1935_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1953_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1953_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1953_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_fst_1943_; 
v_fst_1943_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_fst_1943_);
lean_dec(v_a_1939_);
if (lean_obj_tag(v_fst_1943_) == 0)
{
uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1944_ = 0;
v___x_1945_ = lean_box(v___x_1944_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1945_);
v___x_1947_ = v___x_1941_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
lean_object* v_val_1949_; lean_object* v___x_1951_; 
v_val_1949_ = lean_ctor_get(v_fst_1943_, 0);
lean_inc(v_val_1949_);
lean_dec_ref_known(v_fst_1943_, 1);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v_val_1949_);
v___x_1951_ = v___x_1941_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_val_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1938_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1938_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_1962_, lean_object* v_xs_1963_, lean_object* v_x_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_1962_, v_xs_1963_, v_x_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_x_1964_);
lean_dec_ref(v_xs_1963_);
lean_dec(v_typeName_1962_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_1971_, lean_object* v_info_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___f_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; 
v___f_1978_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1978_, 0, v_typeName_1971_);
v___x_1979_ = l_Lean_ConstantInfo_type(v_info_1972_);
v___x_1980_ = 0;
v___x_1981_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_1979_, v___f_1978_, v___x_1980_, v___x_1980_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_1982_, lean_object* v_info_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_1982_, v_info_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_info_1983_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Expr_hasMVar(v_e_1990_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_e_1990_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; lean_object* v_mctx_1996_; lean_object* v___x_1997_; lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2000_; lean_object* v_cache_2001_; lean_object* v_zetaDeltaFVarIds_2002_; lean_object* v_postponed_2003_; lean_object* v_diag_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2013_; 
v___x_1995_ = lean_st_ref_get(v___y_1991_);
v_mctx_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_mctx_1996_);
lean_dec(v___x_1995_);
v___x_1997_ = l_Lean_instantiateMVarsCore(v_mctx_1996_, v_e_1990_);
v_fst_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_fst_1998_);
v_snd_1999_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_snd_1999_);
lean_dec_ref(v___x_1997_);
v___x_2000_ = lean_st_ref_take(v___y_1991_);
v_cache_2001_ = lean_ctor_get(v___x_2000_, 1);
v_zetaDeltaFVarIds_2002_ = lean_ctor_get(v___x_2000_, 2);
v_postponed_2003_ = lean_ctor_get(v___x_2000_, 3);
v_diag_2004_ = lean_ctor_get(v___x_2000_, 4);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2014_);
v___x_2006_ = v___x_2000_;
v_isShared_2007_ = v_isSharedCheck_2013_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_diag_2004_);
lean_inc(v_postponed_2003_);
lean_inc(v_zetaDeltaFVarIds_2002_);
lean_inc(v_cache_2001_);
lean_dec(v___x_2000_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2013_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v_snd_1999_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_snd_1999_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_cache_2001_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_zetaDeltaFVarIds_2002_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_postponed_2003_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_diag_2004_);
v___x_2009_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_st_ref_put(v___y_1991_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_fst_1998_);
return v___x_2011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object* v_e_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2015_, v___y_2016_);
lean_dec(v___y_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object* v_e_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2019_, v___y_2021_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object* v_e_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object* v_type_2033_, lean_object* v_k_2034_, uint8_t v_cleanupAnnotations_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___f_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2041_, 0, v_k_2034_);
v___x_2042_ = 0;
v___x_2043_ = lean_box(0);
v___x_2044_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2042_, v___x_2043_, v_type_2033_, v___f_2041_, v_cleanupAnnotations_2035_, v___x_2042_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
v_a_2053_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2044_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2044_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object* v_type_2061_, lean_object* v_k_2062_, lean_object* v_cleanupAnnotations_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2069_; lean_object* v_res_2070_; 
v_cleanupAnnotations_boxed_2069_ = lean_unbox(v_cleanupAnnotations_2063_);
v_res_2070_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2061_, v_k_2062_, v_cleanupAnnotations_boxed_2069_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object* v_00_u03b1_2071_, lean_object* v_type_2072_, lean_object* v_k_2073_, uint8_t v_cleanupAnnotations_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2072_, v_k_2073_, v_cleanupAnnotations_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_type_2082_, lean_object* v_k_2083_, lean_object* v_cleanupAnnotations_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2090_; lean_object* v_res_2091_; 
v_cleanupAnnotations_boxed_2090_ = lean_unbox(v_cleanupAnnotations_2084_);
v_res_2091_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(v_00_u03b1_2081_, v_type_2082_, v_k_2083_, v_cleanupAnnotations_boxed_2090_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object* v_typeNameSet_2092_, lean_object* v_x_2093_, lean_object* v_type_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2092_, v_x_2093_, v_type_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_x_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object* v_typeNameSet_2101_, lean_object* v_type_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___f_2108_; lean_object* v_a_2110_; lean_object* v___y_2160_; lean_object* v___x_2170_; 
lean_inc(v_typeNameSet_2101_);
v___f_2108_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2108_, 0, v_typeNameSet_2101_);
lean_inc_ref(v_type_2102_);
v___x_2170_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(v_type_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_dec_ref(v_type_2102_);
v___y_2160_ = v___x_2170_;
goto v___jp_2159_;
}
else
{
lean_object* v_a_2171_; uint8_t v___y_2173_; uint8_t v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
v___x_2174_ = l_Lean_Exception_isInterrupt(v_a_2171_);
if (v___x_2174_ == 0)
{
uint8_t v___x_2175_; 
v___x_2175_ = l_Lean_Exception_isRuntime(v_a_2171_);
v___y_2173_ = v___x_2175_;
goto v___jp_2172_;
}
else
{
lean_dec(v_a_2171_);
v___y_2173_ = v___x_2174_;
goto v___jp_2172_;
}
v___jp_2172_:
{
if (v___y_2173_ == 0)
{
lean_dec_ref_known(v___x_2170_, 1);
v_a_2110_ = v_type_2102_;
goto v___jp_2109_;
}
else
{
lean_dec_ref(v_type_2102_);
v___y_2160_ = v___x_2170_;
goto v___jp_2159_;
}
}
}
v___jp_2109_:
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Lean_Expr_isForall(v_a_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec_ref(v___f_2108_);
v___x_2112_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_a_2110_, v_a_2104_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2148_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2148_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2148_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Expr_getAppFn(v_a_2113_);
if (lean_obj_tag(v___x_2117_) == 4)
{
lean_object* v_declName_2118_; uint8_t v___x_2119_; 
v_declName_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_declName_2118_);
lean_dec_ref_known(v___x_2117_, 2);
lean_inc(v_typeNameSet_2101_);
v___x_2119_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_declName_2118_, v_typeNameSet_2101_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_del_object(v___x_2115_);
v___x_2120_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_a_2113_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2131_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
if (lean_obj_tag(v_a_2121_) == 1)
{
lean_object* v_val_2125_; 
lean_del_object(v___x_2123_);
v_val_2125_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_a_2121_, 1);
v_type_2102_ = v_val_2125_;
goto _start;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_dec(v_a_2121_);
lean_dec(v_typeNameSet_2101_);
v___x_2127_ = lean_box(v___x_2119_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2127_);
v___x_2129_ = v___x_2123_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_typeNameSet_2101_);
v_a_2132_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2120_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2120_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
lean_dec(v_a_2113_);
lean_dec(v_typeNameSet_2101_);
v___x_2140_ = lean_box(v___x_2119_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2140_);
v___x_2142_ = v___x_2115_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_dec_ref(v___x_2117_);
lean_dec(v_a_2113_);
lean_dec(v_typeNameSet_2101_);
v___x_2144_ = lean_box(v___x_2111_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2144_);
v___x_2146_ = v___x_2115_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_typeNameSet_2101_);
v_a_2149_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2112_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2112_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
uint8_t v___x_2157_; lean_object* v___x_2158_; 
lean_dec(v_typeNameSet_2101_);
v___x_2157_ = 0;
v___x_2158_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_a_2110_, v___f_2108_, v___x_2157_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
return v___x_2158_;
}
}
v___jp_2159_:
{
if (lean_obj_tag(v___y_2160_) == 0)
{
lean_object* v_a_2161_; 
v_a_2161_ = lean_ctor_get(v___y_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___y_2160_, 1);
v_a_2110_ = v_a_2161_;
goto v___jp_2109_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v___f_2108_);
lean_dec(v_typeNameSet_2101_);
v_a_2162_ = lean_ctor_get(v___y_2160_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___y_2160_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___y_2160_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___y_2160_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object* v_typeNameSet_2176_, lean_object* v_x_2177_, lean_object* v_type_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2176_, v_type_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object* v_typeNameSet_2185_, lean_object* v_type_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2185_, v_type_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* v_typeNameSet_2193_, lean_object* v_info_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = l_Lean_ConstantInfo_type(v_info_2194_);
v___x_2201_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2193_, v___x_2200_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* v_typeNameSet_2202_, lean_object* v_info_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2202_, v_info_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_info_2203_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* v_matchAlias_2210_, lean_object* v_addAlias_2211_, lean_object* v_alias_2212_, lean_object* v_declNames_2213_, lean_object* v_ns_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
lean_inc_ref(v_matchAlias_2210_);
lean_inc(v_alias_2212_);
lean_inc(v_ns_2214_);
v___x_2223_ = lean_apply_2(v_matchAlias_2210_, v_ns_2214_, v_alias_2212_);
v___x_2224_ = lean_unbox(v___x_2223_);
if (v___x_2224_ == 0)
{
if (lean_obj_tag(v_ns_2214_) == 1)
{
lean_object* v_pre_2225_; 
v_pre_2225_ = lean_ctor_get(v_ns_2214_, 0);
lean_inc(v_pre_2225_);
lean_dec_ref_known(v_ns_2214_, 2);
v_ns_2214_ = v_pre_2225_;
goto _start;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec(v_ns_2214_);
lean_dec(v_declNames_2213_);
lean_dec(v_alias_2212_);
lean_dec_ref(v_addAlias_2211_);
lean_dec_ref(v_matchAlias_2210_);
v___x_2227_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
else
{
lean_object* v___x_2229_; 
lean_dec(v_ns_2214_);
lean_dec_ref(v_matchAlias_2210_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
v___x_2229_ = lean_apply_10(v_addAlias_2211_, v_alias_2212_, v_declNames_2213_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, lean_box(0));
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object* v_matchAlias_2230_, lean_object* v_addAlias_2231_, lean_object* v_alias_2232_, lean_object* v_declNames_2233_, lean_object* v_ns_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2230_, v_addAlias_2231_, v_alias_2232_, v_declNames_2233_, v_ns_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object* v_a_2246_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_2246_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0));
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object* v_a_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2253_);
lean_dec_ref(v_a_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object* v_a_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2256_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object* v_a_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object* v_ctx_2270_, lean_object* v_id_2271_, uint8_t v_danglingDot_2272_, lean_object* v_declName_2273_, lean_object* v_decl_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
lean_inc(v_declName_2273_);
v___x_2283_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_2270_, v_declName_2273_, v_id_2271_, v_danglingDot_2272_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2336_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2336_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2336_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
if (lean_obj_tag(v_a_2284_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_decl_2274_);
lean_dec(v_declName_2273_);
v_a_2288_ = lean_ctor_get(v_a_2284_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2290_ = v_a_2284_;
v_isShared_2291_ = v_isSharedCheck_2298_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v_a_2284_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2298_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2295_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2293_);
v___x_2295_ = v___x_2286_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2299_; 
v_a_2299_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v_a_2284_, 1);
if (lean_obj_tag(v_a_2299_) == 1)
{
lean_object* v_val_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2331_; 
lean_del_object(v___x_2286_);
v_val_2300_ = lean_ctor_get(v_a_2299_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_a_2299_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2302_ = v_a_2299_;
v_isShared_2303_ = v_isSharedCheck_2331_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_val_2300_);
lean_dec(v_a_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2331_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_kind_2304_; lean_object* v_tags_2305_; lean_object* v___x_2306_; 
v_kind_2304_ = lean_ctor_get(v_decl_2274_, 1);
lean_inc_ref(v_kind_2304_);
v_tags_2305_ = lean_ctor_get(v_decl_2274_, 2);
lean_inc_ref(v_tags_2305_);
lean_dec_ref(v_decl_2274_);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
v___x_2306_ = lean_apply_5(v_kind_2304_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
v___x_2308_ = lean_apply_5(v_tags_2305_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
if (v_isShared_2303_ == 0)
{
lean_ctor_set_tag(v___x_2302_, 0);
lean_ctor_set(v___x_2302_, 0, v_declName_2273_);
v___x_2311_ = v___x_2302_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_declName_2273_);
v___x_2311_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
uint8_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_unbox(v_a_2307_);
lean_dec(v_a_2307_);
v___x_2313_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_2300_, v___x_2311_, v___x_2312_, v_a_2309_, v___y_2275_, v___y_2276_);
return v___x_2313_;
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2307_);
lean_del_object(v___x_2302_);
lean_dec(v_val_2300_);
lean_dec(v_declName_2273_);
v_a_2315_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2308_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2308_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_tags_2305_);
lean_del_object(v___x_2302_);
lean_dec(v_val_2300_);
lean_dec(v_declName_2273_);
v_a_2323_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2306_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2306_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
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
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec(v_a_2299_);
lean_dec_ref(v_decl_2274_);
lean_dec(v_declName_2273_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2332_);
v___x_2334_ = v___x_2286_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_decl_2274_);
lean_dec(v_declName_2273_);
v_a_2337_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2283_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2283_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object* v_ctx_2345_, lean_object* v_id_2346_, lean_object* v_danglingDot_2347_, lean_object* v_declName_2348_, lean_object* v_decl_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_danglingDot_boxed_2358_; lean_object* v_res_2359_; 
v_danglingDot_boxed_2358_ = lean_unbox(v_danglingDot_2347_);
v_res_2359_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2345_, v_id_2346_, v_danglingDot_boxed_2358_, v_declName_2348_, v_decl_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object* v_id_2360_, uint8_t v_danglingDot_2361_, lean_object* v_ns_2362_, lean_object* v_alias_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Lean_Name_isPrefixOf(v_ns_2362_, v_alias_2363_);
if (v___x_2364_ == 0)
{
lean_dec(v_alias_2363_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = l_Lean_Name_replacePrefix(v_alias_2363_, v_ns_2362_, v___x_2365_);
v___x_2367_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_2360_, v___x_2366_, v_danglingDot_2361_);
lean_dec(v___x_2366_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object* v_id_2368_, lean_object* v_danglingDot_2369_, lean_object* v_ns_2370_, lean_object* v_alias_2371_){
_start:
{
uint8_t v_danglingDot_boxed_2372_; uint8_t v_res_2373_; lean_object* v_r_2374_; 
v_danglingDot_boxed_2372_ = lean_unbox(v_danglingDot_2369_);
v_res_2373_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2368_, v_danglingDot_boxed_2372_, v_ns_2370_, v_alias_2371_);
lean_dec(v_ns_2370_);
lean_dec(v_id_2368_);
v_r_2374_ = lean_box(v_res_2373_);
return v_r_2374_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object* v_a_2375_, lean_object* v___x_2376_, lean_object* v_alias_2377_, lean_object* v_as_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
if (lean_obj_tag(v_as_2378_) == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref(v___x_2376_);
v___x_2386_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
else
{
lean_object* v_head_2388_; lean_object* v_tail_2389_; uint8_t v___x_2390_; 
v_head_2388_ = lean_ctor_get(v_as_2378_, 0);
lean_inc_n(v_head_2388_, 2);
v_tail_2389_ = lean_ctor_get(v_as_2378_, 1);
lean_inc(v_tail_2389_);
lean_dec_ref_known(v_as_2378_, 2);
lean_inc_ref(v___x_2376_);
v___x_2390_ = l_Lean_Server_Completion_allowCompletion(v_a_2375_, v___x_2376_, v_head_2388_);
if (v___x_2390_ == 0)
{
lean_dec(v_head_2388_);
v_as_2378_ = v_tail_2389_;
goto _start;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = l_Lean_Name_getString_x21(v_alias_2377_);
v___x_2393_ = lean_box(0);
v___x_2394_ = l_Lean_Name_str___override(v___x_2393_, v___x_2392_);
v___x_2395_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_2394_, v_head_2388_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_dec_ref_known(v___x_2395_, 1);
v_as_2378_ = v_tail_2389_;
goto _start;
}
else
{
lean_dec(v_tail_2389_);
lean_dec_ref(v___x_2376_);
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object* v_a_2397_, lean_object* v___x_2398_, lean_object* v_alias_2399_, lean_object* v_as_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2397_, v___x_2398_, v_alias_2399_, v_as_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_alias_2399_);
lean_dec_ref(v_a_2397_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object* v_a_2409_, lean_object* v_env_2410_, lean_object* v_alias_2411_, lean_object* v_declNames_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2409_, v_env_2410_, v_alias_2411_, v_declNames_2412_, v___y_2413_, v___y_2414_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object* v_a_2422_, lean_object* v_env_2423_, lean_object* v_alias_2424_, lean_object* v_declNames_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2422_, v_env_2423_, v_alias_2424_, v_declNames_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v_alias_2424_);
lean_dec_ref(v_a_2422_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object* v___f_2435_, lean_object* v___f_2436_, lean_object* v_currNamespace_2437_, lean_object* v_alias_2438_, lean_object* v_declNames_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v___f_2435_, v___f_2436_, v_alias_2438_, v_declNames_2439_, v_currNamespace_2437_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object* v___f_2449_, lean_object* v___f_2450_, lean_object* v_currNamespace_2451_, lean_object* v_alias_2452_, lean_object* v_declNames_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2449_, v___f_2450_, v_currNamespace_2451_, v_alias_2452_, v_declNames_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg(lean_object* v_f_2463_, lean_object* v_keys_2464_, lean_object* v_vals_2465_, lean_object* v_i_2466_, lean_object* v_acc_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = lean_array_get_size(v_keys_2464_);
v___x_2477_ = lean_nat_dec_lt(v_i_2466_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v_i_2466_);
lean_dec_ref(v_f_2463_);
v___x_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_acc_2467_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
else
{
lean_object* v_k_2480_; lean_object* v_v_2481_; lean_object* v___x_2482_; 
v_k_2480_ = lean_array_fget_borrowed(v_keys_2464_, v_i_2466_);
v_v_2481_ = lean_array_fget_borrowed(v_vals_2465_, v_i_2466_);
lean_inc_ref(v_f_2463_);
lean_inc(v___y_2474_);
lean_inc_ref(v___y_2473_);
lean_inc(v___y_2472_);
lean_inc_ref(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc_ref(v___y_2468_);
lean_inc(v_v_2481_);
lean_inc(v_k_2480_);
v___x_2482_ = lean_apply_11(v_f_2463_, v_acc_2467_, v_k_2480_, v_v_2481_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, lean_box(0));
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
if (lean_obj_tag(v_a_2483_) == 0)
{
lean_dec_ref_known(v_a_2483_, 1);
lean_dec(v_i_2466_);
lean_dec_ref(v_f_2463_);
return v___x_2482_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2482_, 1);
v_a_2484_ = lean_ctor_get(v_a_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v_a_2483_, 1);
v___x_2485_ = lean_unsigned_to_nat(1u);
v___x_2486_ = lean_nat_add(v_i_2466_, v___x_2485_);
lean_dec(v_i_2466_);
v_i_2466_ = v___x_2486_;
v_acc_2467_ = v_a_2484_;
goto _start;
}
}
else
{
lean_dec(v_i_2466_);
lean_dec_ref(v_f_2463_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg___boxed(lean_object* v_f_2488_, lean_object* v_keys_2489_, lean_object* v_vals_2490_, lean_object* v_i_2491_, lean_object* v_acc_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg(v_f_2488_, v_keys_2489_, v_vals_2490_, v_i_2491_, v_acc_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v_vals_2490_);
lean_dec_ref(v_keys_2489_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(lean_object* v_f_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
if (lean_obj_tag(v_x_2503_) == 0)
{
lean_object* v_es_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2535_; 
v_es_2513_ = lean_ctor_get(v_x_2503_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_x_2503_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2515_ = v_x_2503_;
v_isShared_2516_ = v_isSharedCheck_2535_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_es_2513_);
lean_dec(v_x_2503_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2535_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v_es_2513_);
v___x_2519_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2521_; 
lean_dec_ref(v_es_2513_);
lean_dec_ref(v_f_2502_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 1);
lean_ctor_set(v___x_2515_, 0, v_x_2504_);
v___x_2521_ = v___x_2515_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_x_2504_);
v___x_2521_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_nat_dec_le(v___x_2518_, v___x_2518_);
if (v___x_2524_ == 0)
{
if (v___x_2519_ == 0)
{
lean_object* v___x_2526_; 
lean_dec_ref(v_es_2513_);
lean_dec_ref(v_f_2502_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 1);
lean_ctor_set(v___x_2515_, 0, v_x_2504_);
v___x_2526_ = v___x_2515_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_x_2504_);
v___x_2526_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
lean_del_object(v___x_2515_);
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2518_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg(v_f_2502_, v_es_2513_, v___x_2529_, v___x_2530_, v_x_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec_ref(v_es_2513_);
return v___x_2531_;
}
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
lean_del_object(v___x_2515_);
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2518_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg(v_f_2502_, v_es_2513_, v___x_2532_, v___x_2533_, v_x_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec_ref(v_es_2513_);
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_ks_2536_; lean_object* v_vs_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_ks_2536_ = lean_ctor_get(v_x_2503_, 0);
lean_inc_ref(v_ks_2536_);
v_vs_2537_ = lean_ctor_get(v_x_2503_, 1);
lean_inc_ref(v_vs_2537_);
lean_dec_ref_known(v_x_2503_, 2);
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg(v_f_2502_, v_ks_2536_, v_vs_2537_, v___x_2538_, v_x_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec_ref(v_vs_2537_);
lean_dec_ref(v_ks_2536_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg(lean_object* v_f_2540_, lean_object* v_as_2541_, size_t v_i_2542_, size_t v_stop_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_a_2554_; lean_object* v___y_2559_; uint8_t v___x_2562_; 
v___x_2562_ = lean_usize_dec_eq(v_i_2542_, v_stop_2543_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_array_uget_borrowed(v_as_2541_, v_i_2542_);
switch(lean_obj_tag(v___x_2563_))
{
case 0:
{
lean_object* v_key_2564_; lean_object* v_val_2565_; lean_object* v___x_2566_; 
v_key_2564_ = lean_ctor_get(v___x_2563_, 0);
v_val_2565_ = lean_ctor_get(v___x_2563_, 1);
lean_inc_ref(v_f_2540_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v_val_2565_);
lean_inc(v_key_2564_);
v___x_2566_ = lean_apply_11(v_f_2540_, v_b_2544_, v_key_2564_, v_val_2565_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, lean_box(0));
v___y_2559_ = v___x_2566_;
goto v___jp_2558_;
}
case 1:
{
lean_object* v_node_2567_; lean_object* v___x_2568_; 
v_node_2567_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_node_2567_);
lean_inc_ref(v_f_2540_);
v___x_2568_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(v_f_2540_, v_node_2567_, v_b_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2568_;
goto v___jp_2558_;
}
default: 
{
v_a_2554_ = v_b_2544_;
goto v___jp_2553_;
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v_f_2540_);
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_b_2544_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
v___jp_2553_:
{
size_t v___x_2555_; size_t v___x_2556_; 
v___x_2555_ = ((size_t)1ULL);
v___x_2556_ = lean_usize_add(v_i_2542_, v___x_2555_);
v_i_2542_ = v___x_2556_;
v_b_2544_ = v_a_2554_;
goto _start;
}
v___jp_2558_:
{
if (lean_obj_tag(v___y_2559_) == 0)
{
lean_object* v_a_2560_; 
v_a_2560_ = lean_ctor_get(v___y_2559_, 0);
if (lean_obj_tag(v_a_2560_) == 0)
{
lean_dec_ref(v_f_2540_);
return v___y_2559_;
}
else
{
lean_object* v_a_2561_; 
lean_inc_ref(v_a_2560_);
lean_dec_ref_known(v___y_2559_, 1);
v_a_2561_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v_a_2560_, 1);
v_a_2554_ = v_a_2561_;
goto v___jp_2553_;
}
}
else
{
lean_dec_ref(v_f_2540_);
return v___y_2559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg___boxed(lean_object* v_f_2571_, lean_object* v_as_2572_, lean_object* v_i_2573_, lean_object* v_stop_2574_, lean_object* v_b_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
size_t v_i_boxed_2584_; size_t v_stop_boxed_2585_; lean_object* v_res_2586_; 
v_i_boxed_2584_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_stop_boxed_2585_ = lean_unbox_usize(v_stop_2574_);
lean_dec(v_stop_2574_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg(v_f_2571_, v_as_2572_, v_i_boxed_2584_, v_stop_boxed_2585_, v_b_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v_as_2572_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg___boxed(lean_object* v_f_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(v_f_2587_, v_x_2588_, v_x_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object* v_f_2599_, lean_object* v_x_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2608_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
v___x_2611_ = lean_apply_10(v_f_2599_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, lean_box(0));
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_f_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(v_f_2612_, v_x_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object* v_map_2625_, lean_object* v_f_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___f_2635_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2635_, 0, v_f_2626_);
v___x_2636_ = lean_box(0);
v___x_2637_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(v___f_2635_, v_map_2625_, v___x_2636_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object* v_map_2638_, lean_object* v_f_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_2638_, v_f_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg(lean_object* v_f_2649_, lean_object* v_b_2650_, lean_object* v_acc_2651_, lean_object* v_i_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_keyArray_2665_; lean_object* v_valueArray_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_keyArray_2665_ = lean_ctor_get(v_b_2650_, 1);
v_valueArray_2666_ = lean_ctor_get(v_b_2650_, 2);
v___x_2667_ = lean_array_get_size(v_keyArray_2665_);
v___x_2668_ = lean_nat_dec_lt(v_i_2652_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec(v_i_2652_);
lean_dec_ref(v_f_2649_);
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_acc_2651_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; uint8_t v_isSome_2672_; 
v___x_2671_ = lean_array_fget_borrowed(v_keyArray_2665_, v_i_2652_);
v_isSome_2672_ = lean_noption_is_some(v___x_2671_);
if (v_isSome_2672_ == 0)
{
goto v___jp_2661_;
}
else
{
lean_object* v___x_2673_; uint8_t v_isSome_2674_; 
v___x_2673_ = lean_array_fget_borrowed(v_valueArray_2666_, v_i_2652_);
v_isSome_2674_ = lean_noption_is_some(v___x_2673_);
if (v_isSome_2674_ == 0)
{
goto v___jp_2661_;
}
else
{
lean_object* v_val_2675_; lean_object* v_val_2676_; lean_object* v___x_2677_; 
lean_inc(v___x_2671_);
v_val_2675_ = lean_noption_get(v___x_2671_);
lean_inc(v___x_2673_);
v_val_2676_ = lean_noption_get(v___x_2673_);
lean_inc_ref(v_f_2649_);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc_ref(v___y_2655_);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
v___x_2677_ = lean_apply_10(v_f_2649_, v_val_2675_, v_val_2676_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
if (lean_obj_tag(v_a_2678_) == 0)
{
lean_dec_ref_known(v_a_2678_, 1);
lean_dec(v_i_2652_);
lean_dec_ref(v_f_2649_);
return v___x_2677_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec_ref_known(v___x_2677_, 1);
v_a_2679_ = lean_ctor_get(v_a_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v_a_2678_, 1);
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_nat_add(v_i_2652_, v___x_2680_);
lean_dec(v_i_2652_);
v_acc_2651_ = v_a_2679_;
v_i_2652_ = v___x_2681_;
goto _start;
}
}
else
{
lean_dec(v_i_2652_);
lean_dec_ref(v_f_2649_);
return v___x_2677_;
}
}
}
}
v___jp_2661_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_add(v_i_2652_, v___x_2662_);
lean_dec(v_i_2652_);
v_i_2652_ = v___x_2663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_f_2683_, lean_object* v_b_2684_, lean_object* v_acc_2685_, lean_object* v_i_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg(v_f_2683_, v_b_2684_, v_acc_2685_, v_i_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v_b_2684_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object* v_f_2696_, lean_object* v_init_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg(v_f_2696_, v_b_2698_, v_init_2697_, v___x_2707_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object* v_f_2709_, lean_object* v_init_2710_, lean_object* v_b_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2709_, v_init_2710_, v_b_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec_ref(v_b_2711_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object* v_s_2721_, lean_object* v_f_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_map_u2081_2731_; lean_object* v_map_u2082_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_map_u2081_2731_ = lean_ctor_get(v_s_2721_, 0);
lean_inc_ref(v_map_u2081_2731_);
v_map_u2082_2732_ = lean_ctor_get(v_s_2721_, 1);
lean_inc_ref(v_map_u2082_2732_);
lean_dec_ref(v_s_2721_);
v___x_2733_ = lean_box(0);
lean_inc_ref(v_f_2722_);
v___x_2734_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2722_, v___x_2733_, v_map_u2081_2731_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec_ref(v_map_u2081_2731_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
if (lean_obj_tag(v_a_2735_) == 0)
{
lean_dec_ref_known(v_a_2735_, 1);
lean_dec_ref(v_map_u2082_2732_);
lean_dec_ref(v_f_2722_);
return v___x_2734_;
}
else
{
lean_object* v___x_2736_; 
lean_dec_ref_known(v_a_2735_, 1);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2732_, v_f_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2736_;
}
}
else
{
lean_dec_ref(v_map_u2082_2732_);
lean_dec_ref(v_f_2722_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object* v_s_2737_, lean_object* v_f_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_2737_, v_f_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object* v_f_2748_, lean_object* v_decl_2749_, lean_object* v_ci_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___y_2761_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = lean_nat_add(v___y_2751_, v___x_2799_);
v___x_2801_ = lean_unsigned_to_nat(10000u);
v___x_2802_ = lean_nat_dec_le(v___x_2801_, v___x_2800_);
if (v___x_2802_ == 0)
{
v___y_2761_ = v___x_2800_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2803_; lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v___x_2800_);
v___x_2803_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_2754_);
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2820_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2820_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
if (lean_obj_tag(v_a_2804_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2818_; 
lean_dec_ref(v_ci_2750_);
lean_dec(v_decl_2749_);
lean_dec_ref(v_f_2748_);
v_a_2808_ = lean_ctor_get(v_a_2804_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2804_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2810_ = v_a_2804_;
v_isShared_2811_ = v_isSharedCheck_2818_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v_a_2804_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2818_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2813_);
v___x_2815_ = v___x_2806_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v___x_2819_; 
lean_dec_ref_known(v_a_2804_, 1);
lean_del_object(v___x_2806_);
v___x_2819_ = lean_unsigned_to_nat(0u);
v___y_2761_ = v___x_2819_;
goto v___jp_2760_;
}
}
}
v___jp_2760_:
{
lean_object* v___x_2762_; 
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc_ref(v___y_2754_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
v___x_2762_ = lean_apply_10(v_f_2748_, v_decl_2749_, v_ci_2750_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, lean_box(0));
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2790_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2790_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2790_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v___y_2761_);
v_a_2767_ = lean_ctor_get(v_a_2763_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2769_ = v_a_2763_;
v_isShared_2770_ = v_isSharedCheck_2777_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v_a_2763_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2777_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2772_);
v___x_2774_ = v___x_2765_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2789_; 
v_a_2778_ = lean_ctor_get(v_a_2763_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2780_ = v_a_2763_;
v_isShared_2781_ = v_isSharedCheck_2789_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v_a_2763_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2789_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_a_2778_);
lean_ctor_set(v___x_2782_, 1, v___y_2761_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2784_);
v___x_2786_ = v___x_2765_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v___y_2761_);
v_a_2791_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2762_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2762_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object* v_f_2821_, lean_object* v_decl_2822_, lean_object* v_ci_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2821_, v_decl_2822_, v_ci_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_spec__8(lean_object* v_f_2834_, lean_object* v_b_2835_, lean_object* v_acc_2836_, lean_object* v_i_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_keyArray_2851_; lean_object* v_valueArray_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_keyArray_2851_ = lean_ctor_get(v_b_2835_, 1);
v_valueArray_2852_ = lean_ctor_get(v_b_2835_, 2);
v___x_2853_ = lean_array_get_size(v_keyArray_2851_);
v___x_2854_ = lean_nat_dec_lt(v_i_2837_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec(v_i_2837_);
lean_dec_ref(v_f_2834_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_acc_2836_);
lean_ctor_set(v___x_2855_, 1, v___y_2838_);
v___x_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
else
{
lean_object* v___x_2858_; uint8_t v_isSome_2859_; 
v___x_2858_ = lean_array_fget_borrowed(v_keyArray_2851_, v_i_2837_);
v_isSome_2859_ = lean_noption_is_some(v___x_2858_);
if (v_isSome_2859_ == 0)
{
goto v___jp_2847_;
}
else
{
lean_object* v___x_2860_; uint8_t v_isSome_2861_; 
v___x_2860_ = lean_array_fget_borrowed(v_valueArray_2852_, v_i_2837_);
v_isSome_2861_ = lean_noption_is_some(v___x_2860_);
if (v_isSome_2861_ == 0)
{
goto v___jp_2847_;
}
else
{
lean_object* v_val_2862_; lean_object* v_val_2863_; lean_object* v___x_2864_; 
lean_inc(v___x_2858_);
v_val_2862_ = lean_noption_get(v___x_2858_);
lean_inc(v___x_2860_);
v_val_2863_ = lean_noption_get(v___x_2860_);
lean_inc_ref(v_f_2834_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v___y_2842_);
lean_inc_ref(v___y_2841_);
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
v___x_2864_ = lean_apply_11(v_f_2834_, v_val_2862_, v_val_2863_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, lean_box(0));
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
if (lean_obj_tag(v_a_2865_) == 0)
{
lean_dec_ref_known(v_a_2865_, 1);
lean_dec(v_i_2837_);
lean_dec_ref(v_f_2834_);
return v___x_2864_;
}
else
{
lean_object* v_a_2866_; lean_object* v_fst_2867_; lean_object* v_snd_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec_ref_known(v___x_2864_, 1);
v_a_2866_ = lean_ctor_get(v_a_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v_a_2865_, 1);
v_fst_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_fst_2867_);
v_snd_2868_ = lean_ctor_get(v_a_2866_, 1);
lean_inc(v_snd_2868_);
lean_dec(v_a_2866_);
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = lean_nat_add(v_i_2837_, v___x_2869_);
lean_dec(v_i_2837_);
v_acc_2836_ = v_fst_2867_;
v_i_2837_ = v___x_2870_;
v___y_2838_ = v_snd_2868_;
goto _start;
}
}
else
{
lean_dec(v_i_2837_);
lean_dec_ref(v_f_2834_);
return v___x_2864_;
}
}
}
}
v___jp_2847_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_unsigned_to_nat(1u);
v___x_2849_ = lean_nat_add(v_i_2837_, v___x_2848_);
lean_dec(v_i_2837_);
v_i_2837_ = v___x_2849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_spec__8___boxed(lean_object* v_f_2872_, lean_object* v_b_2873_, lean_object* v_acc_2874_, lean_object* v_i_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_spec__8(v_f_2872_, v_b_2873_, v_acc_2874_, v_i_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_b_2873_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object* v_f_2886_, lean_object* v_init_2887_, lean_object* v_b_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_unsigned_to_nat(0u);
v___x_2899_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2_spec__8(v_f_2886_, v_b_2888_, v_init_2887_, v___x_2898_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_f_2900_, lean_object* v_init_2901_, lean_object* v_b_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_2900_, v_init_2901_, v_b_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_b_2902_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_f_2913_, lean_object* v_x_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; 
lean_inc(v___y_2924_);
lean_inc_ref(v___y_2923_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2921_);
lean_inc_ref(v___y_2920_);
lean_inc(v___y_2919_);
lean_inc_ref(v___y_2918_);
v___x_2926_ = lean_apply_11(v_f_2913_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, lean_box(0));
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_f_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_2927_, v_x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg(lean_object* v_f_2941_, lean_object* v_keys_2942_, lean_object* v_vals_2943_, lean_object* v_i_2944_, lean_object* v_acc_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = lean_array_get_size(v_keys_2942_);
v___x_2956_ = lean_nat_dec_lt(v_i_2944_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec(v_i_2944_);
lean_dec_ref(v_f_2941_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_acc_2945_);
lean_ctor_set(v___x_2957_, 1, v___y_2946_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
else
{
lean_object* v_k_2960_; lean_object* v_v_2961_; lean_object* v___x_2962_; 
v_k_2960_ = lean_array_fget_borrowed(v_keys_2942_, v_i_2944_);
v_v_2961_ = lean_array_fget_borrowed(v_vals_2943_, v_i_2944_);
lean_inc_ref(v_f_2941_);
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc(v_v_2961_);
lean_inc(v_k_2960_);
v___x_2962_ = lean_apply_12(v_f_2941_, v_acc_2945_, v_k_2960_, v_v_2961_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, lean_box(0));
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
if (lean_obj_tag(v_a_2963_) == 0)
{
lean_dec_ref_known(v_a_2963_, 1);
lean_dec(v_i_2944_);
lean_dec_ref(v_f_2941_);
return v___x_2962_;
}
else
{
lean_object* v_a_2964_; lean_object* v_fst_2965_; lean_object* v_snd_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_dec_ref_known(v___x_2962_, 1);
v_a_2964_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v_a_2963_, 1);
v_fst_2965_ = lean_ctor_get(v_a_2964_, 0);
lean_inc(v_fst_2965_);
v_snd_2966_ = lean_ctor_get(v_a_2964_, 1);
lean_inc(v_snd_2966_);
lean_dec(v_a_2964_);
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_nat_add(v_i_2944_, v___x_2967_);
lean_dec(v_i_2944_);
v_i_2944_ = v___x_2968_;
v_acc_2945_ = v_fst_2965_;
v___y_2946_ = v_snd_2966_;
goto _start;
}
}
else
{
lean_dec(v_i_2944_);
lean_dec_ref(v_f_2941_);
return v___x_2962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg___boxed(lean_object* v_f_2970_, lean_object* v_keys_2971_, lean_object* v_vals_2972_, lean_object* v_i_2973_, lean_object* v_acc_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg(v_f_2970_, v_keys_2971_, v_vals_2972_, v_i_2973_, v_acc_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_vals_2972_);
lean_dec_ref(v_keys_2971_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(lean_object* v_f_2985_, lean_object* v_x_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
lean_object* v_es_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3021_; 
v_es_2997_ = lean_ctor_get(v_x_2986_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_x_2986_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2999_ = v_x_2986_;
v_isShared_3000_ = v_isSharedCheck_3021_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_es_2997_);
lean_dec(v_x_2986_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3021_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_array_get_size(v_es_2997_);
v___x_3003_ = lean_nat_dec_lt(v___x_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_dec_ref(v_es_2997_);
lean_dec_ref(v_f_2985_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_x_2987_);
lean_ctor_set(v___x_3004_, 1, v___y_2988_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 1);
lean_ctor_set(v___x_2999_, 0, v___x_3004_);
v___x_3006_ = v___x_2999_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
}
else
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_nat_dec_le(v___x_3002_, v___x_3002_);
if (v___x_3009_ == 0)
{
if (v___x_3003_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec_ref(v_es_2997_);
lean_dec_ref(v_f_2985_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v_x_2987_);
lean_ctor_set(v___x_3010_, 1, v___y_2988_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 1);
lean_ctor_set(v___x_2999_, 0, v___x_3010_);
v___x_3012_ = v___x_2999_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
return v___x_3013_;
}
}
else
{
size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
lean_del_object(v___x_2999_);
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_of_nat(v___x_3002_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg(v_f_2985_, v_es_2997_, v___x_3015_, v___x_3016_, v_x_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec_ref(v_es_2997_);
return v___x_3017_;
}
}
else
{
size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
lean_del_object(v___x_2999_);
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = lean_usize_of_nat(v___x_3002_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg(v_f_2985_, v_es_2997_, v___x_3018_, v___x_3019_, v_x_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec_ref(v_es_2997_);
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_ks_3022_; lean_object* v_vs_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_ks_3022_ = lean_ctor_get(v_x_2986_, 0);
lean_inc_ref(v_ks_3022_);
v_vs_3023_ = lean_ctor_get(v_x_2986_, 1);
lean_inc_ref(v_vs_3023_);
lean_dec_ref_known(v_x_2986_, 2);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg(v_f_2985_, v_ks_3022_, v_vs_3023_, v___x_3024_, v_x_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec_ref(v_vs_3023_);
lean_dec_ref(v_ks_3022_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg(lean_object* v_f_3026_, lean_object* v_as_3027_, size_t v_i_3028_, size_t v_stop_3029_, lean_object* v_b_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_fst_3041_; lean_object* v_snd_3042_; lean_object* v___y_3047_; uint8_t v___x_3052_; 
v___x_3052_ = lean_usize_dec_eq(v_i_3028_, v_stop_3029_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_array_uget_borrowed(v_as_3027_, v_i_3028_);
switch(lean_obj_tag(v___x_3053_))
{
case 0:
{
lean_object* v_key_3054_; lean_object* v_val_3055_; lean_object* v___x_3056_; 
v_key_3054_ = lean_ctor_get(v___x_3053_, 0);
v_val_3055_ = lean_ctor_get(v___x_3053_, 1);
lean_inc_ref(v_f_3026_);
lean_inc(v___y_3038_);
lean_inc_ref(v___y_3037_);
lean_inc(v___y_3036_);
lean_inc_ref(v___y_3035_);
lean_inc_ref(v___y_3034_);
lean_inc(v___y_3033_);
lean_inc_ref(v___y_3032_);
lean_inc(v_val_3055_);
lean_inc(v_key_3054_);
v___x_3056_ = lean_apply_12(v_f_3026_, v_b_3030_, v_key_3054_, v_val_3055_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, lean_box(0));
v___y_3047_ = v___x_3056_;
goto v___jp_3046_;
}
case 1:
{
lean_object* v_node_3057_; lean_object* v___x_3058_; 
v_node_3057_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_node_3057_);
lean_inc_ref(v_f_3026_);
v___x_3058_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(v_f_3026_, v_node_3057_, v_b_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
v___y_3047_ = v___x_3058_;
goto v___jp_3046_;
}
default: 
{
v_fst_3041_ = v_b_3030_;
v_snd_3042_ = v___y_3031_;
goto v___jp_3040_;
}
}
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
lean_dec_ref(v_f_3026_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_b_3030_);
lean_ctor_set(v___x_3059_, 1, v___y_3031_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
return v___x_3061_;
}
v___jp_3040_:
{
size_t v___x_3043_; size_t v___x_3044_; 
v___x_3043_ = ((size_t)1ULL);
v___x_3044_ = lean_usize_add(v_i_3028_, v___x_3043_);
v_i_3028_ = v___x_3044_;
v_b_3030_ = v_fst_3041_;
v___y_3031_ = v_snd_3042_;
goto _start;
}
v___jp_3046_:
{
if (lean_obj_tag(v___y_3047_) == 0)
{
lean_object* v_a_3048_; 
v_a_3048_ = lean_ctor_get(v___y_3047_, 0);
if (lean_obj_tag(v_a_3048_) == 0)
{
lean_dec_ref(v_f_3026_);
return v___y_3047_;
}
else
{
lean_object* v_a_3049_; lean_object* v_fst_3050_; lean_object* v_snd_3051_; 
lean_inc_ref(v_a_3048_);
lean_dec_ref_known(v___y_3047_, 1);
v_a_3049_ = lean_ctor_get(v_a_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v_a_3048_, 1);
v_fst_3050_ = lean_ctor_get(v_a_3049_, 0);
lean_inc(v_fst_3050_);
v_snd_3051_ = lean_ctor_get(v_a_3049_, 1);
lean_inc(v_snd_3051_);
lean_dec(v_a_3049_);
v_fst_3041_ = v_fst_3050_;
v_snd_3042_ = v_snd_3051_;
goto v___jp_3040_;
}
}
else
{
lean_dec_ref(v_f_3026_);
return v___y_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg___boxed(lean_object* v_f_3062_, lean_object* v_as_3063_, lean_object* v_i_3064_, lean_object* v_stop_3065_, lean_object* v_b_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
size_t v_i_boxed_3076_; size_t v_stop_boxed_3077_; lean_object* v_res_3078_; 
v_i_boxed_3076_ = lean_unbox_usize(v_i_3064_);
lean_dec(v_i_3064_);
v_stop_boxed_3077_ = lean_unbox_usize(v_stop_3065_);
lean_dec(v_stop_3065_);
v_res_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg(v_f_3062_, v_as_3063_, v_i_boxed_3076_, v_stop_boxed_3077_, v_b_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v_as_3063_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg___boxed(lean_object* v_f_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(v_f_3079_, v_x_3080_, v_x_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_map_3092_, lean_object* v_f_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___f_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3103_, 0, v_f_3093_);
v___x_3104_ = lean_box(0);
v___x_3105_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(v___f_3103_, v_map_3092_, v___x_3104_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_map_3106_, lean_object* v_f_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3106_, v_f_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object* v_env_3118_, lean_object* v_f_3119_, lean_object* v_name_3120_, lean_object* v_c_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
uint8_t v___x_3131_; 
lean_inc(v_name_3120_);
v___x_3131_ = l_Lean_Meta_allowCompletion(v_env_3118_, v_name_3120_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_c_3121_);
lean_dec(v_name_3120_);
lean_dec_ref(v_f_3119_);
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v___y_3122_);
v___x_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_inc_ref(v_c_3121_);
v___x_3136_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionKindForDecl___boxed), 6, 1);
lean_closure_set(v___x_3136_, 0, v_c_3121_);
lean_inc(v_name_3120_);
v___x_3137_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionTagsForDecl___boxed), 6, 1);
lean_closure_set(v___x_3137_, 0, v_name_3120_);
v___x_3138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3138_, 0, v_c_3121_);
lean_ctor_set(v___x_3138_, 1, v___x_3136_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3128_);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3126_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3124_);
lean_inc_ref(v___y_3123_);
v___x_3139_ = lean_apply_11(v_f_3119_, v_name_3120_, v___x_3138_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, lean_box(0));
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object* v_env_3140_, lean_object* v_f_3141_, lean_object* v_name_3142_, lean_object* v_c_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3140_, v_f_3141_, v_name_3142_, v_c_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object* v_f_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; lean_object* v_env_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_st_ref_get(v___y_3162_);
v_env_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc_ref_n(v_env_3165_, 2);
lean_dec(v___x_3164_);
v___x_3166_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_3165_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3166_, 1);
v___x_3168_ = lean_box(0);
lean_inc_ref(v_f_3154_);
v___x_3169_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3154_, v___x_3168_, v_a_3167_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v_a_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
if (lean_obj_tag(v_a_3170_) == 0)
{
lean_dec_ref_known(v_a_3170_, 1);
lean_dec_ref(v_env_3165_);
lean_dec_ref(v_f_3154_);
return v___x_3169_;
}
else
{
lean_object* v_a_3171_; lean_object* v_snd_3172_; lean_object* v___x_3173_; lean_object* v_map_u2082_3174_; lean_object* v___f_3175_; lean_object* v___x_3176_; 
lean_dec_ref_known(v___x_3169_, 1);
v_a_3171_ = lean_ctor_get(v_a_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v_a_3170_, 1);
v_snd_3172_ = lean_ctor_get(v_a_3171_, 1);
lean_inc(v_snd_3172_);
lean_dec(v_a_3171_);
lean_inc_ref(v_env_3165_);
v___x_3173_ = l_Lean_Environment_constants(v_env_3165_);
v_map_u2082_3174_ = lean_ctor_get(v___x_3173_, 1);
lean_inc_ref(v_map_u2082_3174_);
lean_dec_ref(v___x_3173_);
v___f_3175_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3175_, 0, v_env_3165_);
lean_closure_set(v___f_3175_, 1, v_f_3154_);
v___x_3176_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3174_, v___f_3175_, v_snd_3172_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3176_;
}
}
else
{
lean_dec_ref(v_env_3165_);
lean_dec_ref(v_f_3154_);
return v___x_3169_;
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v_env_3165_);
lean_dec(v___y_3155_);
lean_dec_ref(v_f_3154_);
v_a_3177_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3166_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3166_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object* v_f_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object* v_f_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___f_3205_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3205_, 0, v_f_3196_);
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v___f_3205_, v___x_3206_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3227_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3227_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3227_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
if (lean_obj_tag(v_a_3208_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3222_; 
v_a_3212_ = lean_ctor_get(v_a_3208_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_a_3208_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3214_ = v_a_3208_;
v_isShared_3215_ = v_isSharedCheck_3222_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v_a_3208_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3222_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3217_);
v___x_3219_ = v___x_3210_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_dec_ref_known(v_a_3208_, 1);
v___x_3223_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3223_);
v___x_3225_ = v___x_3210_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
v_a_3228_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3207_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3207_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object* v_f_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg(lean_object* v_id_3248_, uint8_t v_danglingDot_3249_, lean_object* v_as_3250_, size_t v_sz_3251_, size_t v_i_3252_, lean_object* v_b_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_usize_dec_lt(v_i_3252_, v_sz_3251_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_b_3253_);
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
else
{
lean_object* v_snd_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3313_; 
v_snd_3260_ = lean_ctor_get(v_b_3253_, 1);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_b_3253_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v_b_3253_, 0);
lean_dec(v_unused_3314_);
v___x_3262_ = v_b_3253_;
v_isShared_3263_ = v_isSharedCheck_3313_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_snd_3260_);
lean_dec(v_b_3253_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3313_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v_a_3266_; lean_object* v_a_3273_; 
v___x_3264_ = lean_box(0);
v_a_3273_ = lean_array_uget(v_as_3250_, v_i_3252_);
if (lean_obj_tag(v_a_3273_) == 0)
{
v_a_3266_ = v_snd_3260_;
goto v___jp_3265_;
}
else
{
lean_object* v_val_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v_snd_3260_);
v_val_3274_ = lean_ctor_get(v_a_3273_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_a_3273_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3276_ = v_a_3273_;
v_isShared_3277_ = v_isSharedCheck_3312_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_val_3274_);
lean_dec(v_a_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3312_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3278_ = lean_box(0);
v___x_3279_ = l_Lean_LocalDecl_userName(v_val_3274_);
v___x_3280_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3248_, v___x_3279_, v_danglingDot_3249_);
if (v___x_3280_ == 0)
{
lean_dec(v___x_3279_);
lean_del_object(v___x_3276_);
lean_dec(v_val_3274_);
v_a_3266_ = v___x_3278_;
goto v___jp_3265_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = l_Lean_LocalDecl_fvarId(v_val_3274_);
lean_dec(v_val_3274_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3281_);
v___x_3283_ = v___x_3276_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
uint8_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = 5;
v___x_3285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0));
v___x_3286_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3279_, v___x_3283_, v___x_3284_, v___x_3285_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3302_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3302_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3302_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
if (lean_obj_tag(v_a_3287_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3301_; 
lean_del_object(v___x_3262_);
v_a_3291_ = lean_ctor_get(v_a_3287_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3293_ = v_a_3287_;
v_isShared_3294_ = v_isSharedCheck_3301_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v_a_3287_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3301_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3296_);
v___x_3298_ = v___x_3289_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3287_, 1);
lean_del_object(v___x_3289_);
v_a_3266_ = v___x_3278_;
goto v___jp_3265_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_del_object(v___x_3262_);
v_a_3303_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3286_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3286_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
}
}
v___jp_3265_:
{
lean_object* v___x_3268_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 1, v_a_3266_);
lean_ctor_set(v___x_3262_, 0, v___x_3264_);
v___x_3268_ = v___x_3262_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_a_3266_);
v___x_3268_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
size_t v___x_3269_; size_t v___x_3270_; 
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_add(v_i_3252_, v___x_3269_);
v_i_3252_ = v___x_3270_;
v_b_3253_ = v___x_3268_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___boxed(lean_object* v_id_3315_, lean_object* v_danglingDot_3316_, lean_object* v_as_3317_, lean_object* v_sz_3318_, lean_object* v_i_3319_, lean_object* v_b_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
uint8_t v_danglingDot_boxed_3324_; size_t v_sz_boxed_3325_; size_t v_i_boxed_3326_; lean_object* v_res_3327_; 
v_danglingDot_boxed_3324_ = lean_unbox(v_danglingDot_3316_);
v_sz_boxed_3325_ = lean_unbox_usize(v_sz_3318_);
lean_dec(v_sz_3318_);
v_i_boxed_3326_ = lean_unbox_usize(v_i_3319_);
lean_dec(v_i_3319_);
v_res_3327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg(v_id_3315_, v_danglingDot_boxed_3324_, v_as_3317_, v_sz_boxed_3325_, v_i_boxed_3326_, v_b_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v_as_3317_);
lean_dec(v_id_3315_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object* v_id_3328_, uint8_t v_danglingDot_3329_, lean_object* v_as_3330_, size_t v_sz_3331_, size_t v_i_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_usize_dec_lt(v_i_3332_, v_sz_3331_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_b_3333_);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
else
{
lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3398_; 
v_snd_3345_ = lean_ctor_get(v_b_3333_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_b_3333_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v_b_3333_, 0);
lean_dec(v_unused_3399_);
v___x_3347_ = v_b_3333_;
v_isShared_3348_ = v_isSharedCheck_3398_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_dec(v_b_3333_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3398_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v_a_3351_; lean_object* v_a_3358_; 
v___x_3349_ = lean_box(0);
v_a_3358_ = lean_array_uget(v_as_3330_, v_i_3332_);
if (lean_obj_tag(v_a_3358_) == 0)
{
v_a_3351_ = v_snd_3345_;
goto v___jp_3350_;
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_snd_3345_);
v_val_3359_ = lean_ctor_get(v_a_3358_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3358_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3361_ = v_a_3358_;
v_isShared_3362_ = v_isSharedCheck_3397_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_val_3359_);
lean_dec(v_a_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3397_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3363_ = lean_box(0);
v___x_3364_ = l_Lean_LocalDecl_userName(v_val_3359_);
v___x_3365_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3328_, v___x_3364_, v_danglingDot_3329_);
if (v___x_3365_ == 0)
{
lean_dec(v___x_3364_);
lean_del_object(v___x_3361_);
lean_dec(v_val_3359_);
v_a_3351_ = v___x_3363_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = l_Lean_LocalDecl_fvarId(v_val_3359_);
lean_dec(v_val_3359_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3366_);
v___x_3368_ = v___x_3361_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
uint8_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = 5;
v___x_3370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0));
v___x_3371_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3364_, v___x_3368_, v___x_3369_, v___x_3370_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3387_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3387_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3387_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
if (lean_obj_tag(v_a_3372_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3386_; 
lean_del_object(v___x_3347_);
v_a_3376_ = lean_ctor_get(v_a_3372_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3378_ = v_a_3372_;
v_isShared_3379_ = v_isSharedCheck_3386_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v_a_3372_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3386_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3381_);
v___x_3383_ = v___x_3374_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3372_, 1);
lean_del_object(v___x_3374_);
v_a_3351_ = v___x_3363_;
goto v___jp_3350_;
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_del_object(v___x_3347_);
v_a_3388_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3371_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3371_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
}
}
v___jp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v_a_3351_);
lean_ctor_set(v___x_3347_, 0, v___x_3349_);
v___x_3353_ = v___x_3347_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_a_3351_);
v___x_3353_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
size_t v___x_3354_; size_t v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3332_, v___x_3354_);
v___x_3356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg(v_id_3328_, v_danglingDot_3329_, v_as_3330_, v_sz_3331_, v___x_3355_, v___x_3353_, v___y_3334_, v___y_3335_);
return v___x_3356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object* v_id_3400_, lean_object* v_danglingDot_3401_, lean_object* v_as_3402_, lean_object* v_sz_3403_, lean_object* v_i_3404_, lean_object* v_b_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_danglingDot_boxed_3414_; size_t v_sz_boxed_3415_; size_t v_i_boxed_3416_; lean_object* v_res_3417_; 
v_danglingDot_boxed_3414_ = lean_unbox(v_danglingDot_3401_);
v_sz_boxed_3415_ = lean_unbox_usize(v_sz_3403_);
lean_dec(v_sz_3403_);
v_i_boxed_3416_ = lean_unbox_usize(v_i_3404_);
lean_dec(v_i_3404_);
v_res_3417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_id_3400_, v_danglingDot_boxed_3414_, v_as_3402_, v_sz_boxed_3415_, v_i_boxed_3416_, v_b_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec_ref(v_as_3402_);
lean_dec(v_id_3400_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg(lean_object* v_id_3418_, uint8_t v_danglingDot_3419_, lean_object* v_as_3420_, size_t v_sz_3421_, size_t v_i_3422_, lean_object* v_b_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_usize_dec_lt(v_i_3422_, v_sz_3421_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3428_, 0, v_b_3423_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
else
{
lean_object* v_snd_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3483_; 
v_snd_3430_ = lean_ctor_get(v_b_3423_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_b_3423_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v_b_3423_, 0);
lean_dec(v_unused_3484_);
v___x_3432_ = v_b_3423_;
v_isShared_3433_ = v_isSharedCheck_3483_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_snd_3430_);
lean_dec(v_b_3423_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3483_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v_a_3436_; lean_object* v_a_3443_; 
v___x_3434_ = lean_box(0);
v_a_3443_ = lean_array_uget(v_as_3420_, v_i_3422_);
if (lean_obj_tag(v_a_3443_) == 0)
{
v_a_3436_ = v_snd_3430_;
goto v___jp_3435_;
}
else
{
lean_object* v_val_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_snd_3430_);
v_val_3444_ = lean_ctor_get(v_a_3443_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_a_3443_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3446_ = v_a_3443_;
v_isShared_3447_ = v_isSharedCheck_3482_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_val_3444_);
lean_dec(v_a_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3482_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_box(0);
v___x_3449_ = l_Lean_LocalDecl_userName(v_val_3444_);
v___x_3450_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3418_, v___x_3449_, v_danglingDot_3419_);
if (v___x_3450_ == 0)
{
lean_dec(v___x_3449_);
lean_del_object(v___x_3446_);
lean_dec(v_val_3444_);
v_a_3436_ = v___x_3448_;
goto v___jp_3435_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = l_Lean_LocalDecl_fvarId(v_val_3444_);
lean_dec(v_val_3444_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3451_);
v___x_3453_ = v___x_3446_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
uint8_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = 5;
v___x_3455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0));
v___x_3456_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3449_, v___x_3453_, v___x_3454_, v___x_3455_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3472_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3472_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3472_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
if (lean_obj_tag(v_a_3457_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3471_; 
lean_del_object(v___x_3432_);
v_a_3461_ = lean_ctor_get(v_a_3457_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3463_ = v_a_3457_;
v_isShared_3464_ = v_isSharedCheck_3471_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v_a_3457_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3471_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3466_);
v___x_3468_ = v___x_3459_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3457_, 1);
lean_del_object(v___x_3459_);
v_a_3436_ = v___x_3448_;
goto v___jp_3435_;
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3432_);
v_a_3473_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3456_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3456_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
}
}
v___jp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_a_3436_);
lean_ctor_set(v___x_3432_, 0, v___x_3434_);
v___x_3438_ = v___x_3432_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_a_3436_);
v___x_3438_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
size_t v___x_3439_; size_t v___x_3440_; 
v___x_3439_ = ((size_t)1ULL);
v___x_3440_ = lean_usize_add(v_i_3422_, v___x_3439_);
v_i_3422_ = v___x_3440_;
v_b_3423_ = v___x_3438_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg___boxed(lean_object* v_id_3485_, lean_object* v_danglingDot_3486_, lean_object* v_as_3487_, lean_object* v_sz_3488_, lean_object* v_i_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
uint8_t v_danglingDot_boxed_3494_; size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_danglingDot_boxed_3494_ = lean_unbox(v_danglingDot_3486_);
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3488_);
lean_dec(v_sz_3488_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3489_);
lean_dec(v_i_3489_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg(v_id_3485_, v_danglingDot_boxed_3494_, v_as_3487_, v_sz_boxed_3495_, v_i_boxed_3496_, v_b_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v_as_3487_);
lean_dec(v_id_3485_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16(lean_object* v_id_3498_, uint8_t v_danglingDot_3499_, lean_object* v_as_3500_, size_t v_sz_3501_, size_t v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_usize_dec_lt(v_i_3502_, v_sz_3501_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_b_3503_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
else
{
lean_object* v_snd_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3568_; 
v_snd_3515_ = lean_ctor_get(v_b_3503_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_b_3503_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_b_3503_, 0);
lean_dec(v_unused_3569_);
v___x_3517_ = v_b_3503_;
v_isShared_3518_ = v_isSharedCheck_3568_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_snd_3515_);
lean_dec(v_b_3503_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3568_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v_a_3521_; lean_object* v_a_3528_; 
v___x_3519_ = lean_box(0);
v_a_3528_ = lean_array_uget(v_as_3500_, v_i_3502_);
if (lean_obj_tag(v_a_3528_) == 0)
{
v_a_3521_ = v_snd_3515_;
goto v___jp_3520_;
}
else
{
lean_object* v_val_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v_snd_3515_);
v_val_3529_ = lean_ctor_get(v_a_3528_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_a_3528_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3531_ = v_a_3528_;
v_isShared_3532_ = v_isSharedCheck_3567_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_val_3529_);
lean_dec(v_a_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3567_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3533_ = lean_box(0);
v___x_3534_ = l_Lean_LocalDecl_userName(v_val_3529_);
v___x_3535_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3498_, v___x_3534_, v_danglingDot_3499_);
if (v___x_3535_ == 0)
{
lean_dec(v___x_3534_);
lean_del_object(v___x_3531_);
lean_dec(v_val_3529_);
v_a_3521_ = v___x_3533_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3536_ = l_Lean_LocalDecl_fvarId(v_val_3529_);
lean_dec(v_val_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3536_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = 5;
v___x_3540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg___closed__0));
v___x_3541_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3534_, v___x_3538_, v___x_3539_, v___x_3540_, v___y_3504_, v___y_3505_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3557_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3557_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3557_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
if (lean_obj_tag(v_a_3542_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3556_; 
lean_del_object(v___x_3517_);
v_a_3546_ = lean_ctor_get(v_a_3542_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_a_3542_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3548_ = v_a_3542_;
v_isShared_3549_ = v_isSharedCheck_3556_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v_a_3542_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3556_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3551_);
v___x_3553_ = v___x_3544_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
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
lean_dec_ref_known(v_a_3542_, 1);
lean_del_object(v___x_3544_);
v_a_3521_ = v___x_3533_;
goto v___jp_3520_;
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_del_object(v___x_3517_);
v_a_3558_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3541_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3541_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
}
v___jp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 1, v_a_3521_);
lean_ctor_set(v___x_3517_, 0, v___x_3519_);
v___x_3523_ = v___x_3517_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_a_3521_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = ((size_t)1ULL);
v___x_3525_ = lean_usize_add(v_i_3502_, v___x_3524_);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg(v_id_3498_, v_danglingDot_3499_, v_as_3500_, v_sz_3501_, v___x_3525_, v___x_3523_, v___y_3504_, v___y_3505_);
return v___x_3526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16___boxed(lean_object* v_id_3570_, lean_object* v_danglingDot_3571_, lean_object* v_as_3572_, lean_object* v_sz_3573_, lean_object* v_i_3574_, lean_object* v_b_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
uint8_t v_danglingDot_boxed_3584_; size_t v_sz_boxed_3585_; size_t v_i_boxed_3586_; lean_object* v_res_3587_; 
v_danglingDot_boxed_3584_ = lean_unbox(v_danglingDot_3571_);
v_sz_boxed_3585_ = lean_unbox_usize(v_sz_3573_);
lean_dec(v_sz_3573_);
v_i_boxed_3586_ = lean_unbox_usize(v_i_3574_);
lean_dec(v_i_3574_);
v_res_3587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16(v_id_3570_, v_danglingDot_boxed_3584_, v_as_3572_, v_sz_boxed_3585_, v_i_boxed_3586_, v_b_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec_ref(v_as_3572_);
lean_dec(v_id_3570_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10(lean_object* v_init_3588_, lean_object* v_id_3589_, uint8_t v_danglingDot_3590_, lean_object* v_n_3591_, lean_object* v_b_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
if (lean_obj_tag(v_n_3591_) == 0)
{
lean_object* v_cs_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; size_t v_sz_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v_cs_3601_ = lean_ctor_get(v_n_3591_, 0);
v___x_3602_ = lean_box(0);
v___x_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v_b_3592_);
v_sz_3604_ = lean_array_size(v_cs_3601_);
v___x_3605_ = ((size_t)0ULL);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__15(v_init_3588_, v_id_3589_, v_danglingDot_3590_, v_cs_3601_, v_sz_3604_, v___x_3605_, v___x_3603_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3643_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3643_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3643_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
if (lean_obj_tag(v_a_3607_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3621_; 
v_a_3611_ = lean_ctor_get(v_a_3607_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_a_3607_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3613_ = v_a_3607_;
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v_a_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3618_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3616_);
v___x_3618_ = v___x_3609_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
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
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3642_; 
v_a_3622_ = lean_ctor_get(v_a_3607_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_a_3607_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3624_ = v_a_3607_;
v_isShared_3625_ = v_isSharedCheck_3642_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v_a_3607_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3642_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v_fst_3626_; 
v_fst_3626_ = lean_ctor_get(v_a_3622_, 0);
if (lean_obj_tag(v_fst_3626_) == 0)
{
lean_object* v_snd_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v_snd_3627_ = lean_ctor_get(v_a_3622_, 1);
lean_inc(v_snd_3627_);
lean_dec(v_a_3622_);
v___x_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3628_, 0, v_snd_3627_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3628_);
v___x_3630_ = v___x_3624_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3630_);
v___x_3632_ = v___x_3609_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
else
{
lean_object* v_val_3635_; lean_object* v___x_3637_; 
lean_inc_ref(v_fst_3626_);
lean_dec(v_a_3622_);
v_val_3635_ = lean_ctor_get(v_fst_3626_, 0);
lean_inc(v_val_3635_);
lean_dec_ref_known(v_fst_3626_, 1);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v_val_3635_);
v___x_3637_ = v___x_3624_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_val_3635_);
v___x_3637_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3637_);
v___x_3639_ = v___x_3609_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3606_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3606_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
lean_object* v_vs_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; size_t v_sz_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v_vs_3652_ = lean_ctor_get(v_n_3591_, 0);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v_b_3592_);
v_sz_3655_ = lean_array_size(v_vs_3652_);
v___x_3656_ = ((size_t)0ULL);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16(v_id_3589_, v_danglingDot_3590_, v_vs_3652_, v_sz_3655_, v___x_3656_, v___x_3654_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3694_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3694_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3694_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
if (lean_obj_tag(v_a_3658_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3672_; 
v_a_3662_ = lean_ctor_get(v_a_3658_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_a_3658_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3664_ = v_a_3658_;
v_isShared_3665_ = v_isSharedCheck_3672_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v_a_3658_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3672_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3667_);
v___x_3669_ = v___x_3660_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3693_; 
v_a_3673_ = lean_ctor_get(v_a_3658_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_a_3658_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3675_ = v_a_3658_;
v_isShared_3676_ = v_isSharedCheck_3693_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v_a_3658_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3693_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_fst_3677_; 
v_fst_3677_ = lean_ctor_get(v_a_3673_, 0);
if (lean_obj_tag(v_fst_3677_) == 0)
{
lean_object* v_snd_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v_snd_3678_ = lean_ctor_get(v_a_3673_, 1);
lean_inc(v_snd_3678_);
lean_dec(v_a_3673_);
v___x_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3679_, 0, v_snd_3678_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3679_);
v___x_3681_ = v___x_3675_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3683_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3681_);
v___x_3683_ = v___x_3660_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
else
{
lean_object* v_val_3686_; lean_object* v___x_3688_; 
lean_inc_ref(v_fst_3677_);
lean_dec(v_a_3673_);
v_val_3686_ = lean_ctor_get(v_fst_3677_, 0);
lean_inc(v_val_3686_);
lean_dec_ref_known(v_fst_3677_, 1);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_val_3686_);
v___x_3688_ = v___x_3675_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_val_3686_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3688_);
v___x_3690_ = v___x_3660_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
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
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
v_a_3695_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3657_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3657_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__15(lean_object* v_init_3703_, lean_object* v_id_3704_, uint8_t v_danglingDot_3705_, lean_object* v_as_3706_, size_t v_sz_3707_, size_t v_i_3708_, lean_object* v_b_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_usize_dec_lt(v_i_3708_, v_sz_3707_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3719_, 0, v_b_3709_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
else
{
lean_object* v_snd_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3774_; 
v_snd_3721_ = lean_ctor_get(v_b_3709_, 1);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_b_3709_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v_b_3709_, 0);
lean_dec(v_unused_3775_);
v___x_3723_ = v_b_3709_;
v_isShared_3724_ = v_isSharedCheck_3774_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_snd_3721_);
lean_dec(v_b_3709_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3774_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_a_3725_; lean_object* v___x_3726_; 
v_a_3725_ = lean_array_uget_borrowed(v_as_3706_, v_i_3708_);
lean_inc(v_snd_3721_);
v___x_3726_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10(v_init_3703_, v_id_3704_, v_danglingDot_3705_, v_a_3725_, v_snd_3721_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3765_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3765_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3765_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
if (lean_obj_tag(v_a_3727_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3723_);
lean_dec(v_snd_3721_);
v_a_3731_ = lean_ctor_get(v_a_3727_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3733_ = v_a_3727_;
v_isShared_3734_ = v_isSharedCheck_3741_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v_a_3727_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3741_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3738_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3736_);
v___x_3738_ = v___x_3729_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3764_; 
v_a_3742_ = lean_ctor_get(v_a_3727_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3744_ = v_a_3727_;
v_isShared_3745_ = v_isSharedCheck_3764_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v_a_3727_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3764_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
if (lean_obj_tag(v_a_3742_) == 0)
{
lean_object* v___x_3746_; lean_object* v___x_3748_; 
v___x_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_a_3742_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3746_);
v___x_3748_ = v___x_3723_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_snd_3721_);
v___x_3748_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3748_);
v___x_3750_ = v___x_3744_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3752_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3750_);
v___x_3752_ = v___x_3729_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_del_object(v___x_3744_);
lean_del_object(v___x_3729_);
lean_dec(v_snd_3721_);
v_a_3756_ = lean_ctor_get(v_a_3742_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v_a_3742_, 1);
v___x_3757_ = lean_box(0);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 1, v_a_3756_);
lean_ctor_set(v___x_3723_, 0, v___x_3757_);
v___x_3759_ = v___x_3723_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_a_3756_);
v___x_3759_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
size_t v___x_3760_; size_t v___x_3761_; 
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_add(v_i_3708_, v___x_3760_);
v_i_3708_ = v___x_3761_;
v_b_3709_ = v___x_3759_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3723_);
lean_dec(v_snd_3721_);
v_a_3766_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3726_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3726_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__15___boxed(lean_object* v_init_3776_, lean_object* v_id_3777_, lean_object* v_danglingDot_3778_, lean_object* v_as_3779_, lean_object* v_sz_3780_, lean_object* v_i_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_danglingDot_boxed_3791_; size_t v_sz_boxed_3792_; size_t v_i_boxed_3793_; lean_object* v_res_3794_; 
v_danglingDot_boxed_3791_ = lean_unbox(v_danglingDot_3778_);
v_sz_boxed_3792_ = lean_unbox_usize(v_sz_3780_);
lean_dec(v_sz_3780_);
v_i_boxed_3793_ = lean_unbox_usize(v_i_3781_);
lean_dec(v_i_3781_);
v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__15(v_init_3776_, v_id_3777_, v_danglingDot_boxed_3791_, v_as_3779_, v_sz_boxed_3792_, v_i_boxed_3793_, v_b_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_as_3779_);
lean_dec(v_id_3777_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10___boxed(lean_object* v_init_3795_, lean_object* v_id_3796_, lean_object* v_danglingDot_3797_, lean_object* v_n_3798_, lean_object* v_b_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
uint8_t v_danglingDot_boxed_3808_; lean_object* v_res_3809_; 
v_danglingDot_boxed_3808_ = lean_unbox(v_danglingDot_3797_);
v_res_3809_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10(v_init_3795_, v_id_3796_, v_danglingDot_boxed_3808_, v_n_3798_, v_b_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec_ref(v_n_3798_);
lean_dec(v_id_3796_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object* v_id_3810_, uint8_t v_danglingDot_3811_, lean_object* v_t_3812_, lean_object* v_init_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_b_3823_; lean_object* v_root_3826_; lean_object* v_tail_3827_; lean_object* v___x_3828_; 
v_root_3826_ = lean_ctor_get(v_t_3812_, 0);
v_tail_3827_ = lean_ctor_get(v_t_3812_, 1);
v___x_3828_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10(v_init_3813_, v_id_3810_, v_danglingDot_3811_, v_root_3826_, v_init_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3890_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3890_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3890_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
if (lean_obj_tag(v_a_3829_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3843_; 
v_a_3833_ = lean_ctor_get(v_a_3829_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_a_3829_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3835_ = v_a_3829_;
v_isShared_3836_ = v_isSharedCheck_3843_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v_a_3829_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3843_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3838_);
v___x_3840_ = v___x_3831_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
else
{
lean_object* v_a_3844_; 
lean_del_object(v___x_3831_);
v_a_3844_ = lean_ctor_get(v_a_3829_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v_a_3829_, 1);
if (lean_obj_tag(v_a_3844_) == 0)
{
lean_object* v_a_3845_; 
v_a_3845_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v_a_3844_, 1);
v_b_3823_ = v_a_3845_;
goto v___jp_3822_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; size_t v_sz_3849_; size_t v___x_3850_; lean_object* v___x_3851_; 
v_a_3846_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v_a_3844_, 1);
v___x_3847_ = lean_box(0);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v_a_3846_);
v_sz_3849_ = lean_array_size(v_tail_3827_);
v___x_3850_ = ((size_t)0ULL);
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_id_3810_, v_danglingDot_3811_, v_tail_3827_, v_sz_3849_, v___x_3850_, v___x_3848_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3881_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3881_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3881_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
if (lean_obj_tag(v_a_3852_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3866_; 
v_a_3856_ = lean_ctor_get(v_a_3852_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_a_3852_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3858_ = v_a_3852_;
v_isShared_3859_ = v_isSharedCheck_3866_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v_a_3852_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3866_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3861_);
v___x_3863_ = v___x_3854_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3880_; 
v_a_3867_ = lean_ctor_get(v_a_3852_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_a_3852_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3869_ = v_a_3852_;
v_isShared_3870_ = v_isSharedCheck_3880_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v_a_3852_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3880_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v_fst_3871_; 
v_fst_3871_ = lean_ctor_get(v_a_3867_, 0);
if (lean_obj_tag(v_fst_3871_) == 0)
{
lean_object* v_snd_3872_; lean_object* v___x_3874_; 
v_snd_3872_ = lean_ctor_get(v_a_3867_, 1);
lean_inc(v_snd_3872_);
lean_dec(v_a_3867_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v_snd_3872_);
v___x_3874_ = v___x_3869_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_snd_3872_);
v___x_3874_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3876_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3874_);
v___x_3876_ = v___x_3854_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
else
{
lean_object* v_val_3879_; 
lean_inc_ref(v_fst_3871_);
lean_del_object(v___x_3869_);
lean_dec(v_a_3867_);
lean_del_object(v___x_3854_);
v_val_3879_ = lean_ctor_get(v_fst_3871_, 0);
lean_inc(v_val_3879_);
lean_dec_ref_known(v_fst_3871_, 1);
v_b_3823_ = v_val_3879_;
goto v___jp_3822_;
}
}
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3851_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3851_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v_a_3891_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3828_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3828_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
v___jp_3822_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3823_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
return v___x_3825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object* v_id_3899_, lean_object* v_danglingDot_3900_, lean_object* v_t_3901_, lean_object* v_init_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v_danglingDot_boxed_3911_; lean_object* v_res_3912_; 
v_danglingDot_boxed_3911_ = lean_unbox(v_danglingDot_3900_);
v_res_3912_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_3899_, v_danglingDot_boxed_3911_, v_t_3901_, v_init_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v_t_3901_);
lean_dec(v_id_3899_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object* v_as_3913_, size_t v_sz_3914_, size_t v_i_3915_, lean_object* v_b_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
uint8_t v___x_3920_; 
v___x_3920_ = lean_usize_dec_lt(v_i_3915_, v_sz_3914_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v_b_3916_);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3924_; 
v_a_3923_ = lean_array_uget_borrowed(v_as_3913_, v_i_3915_);
lean_inc(v_a_3923_);
v___x_3924_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_3923_, v___y_3917_, v___y_3918_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
if (lean_obj_tag(v_a_3925_) == 0)
{
lean_dec_ref_known(v_a_3925_, 1);
return v___x_3924_;
}
else
{
lean_object* v___x_3926_; size_t v___x_3927_; size_t v___x_3928_; 
lean_dec_ref_known(v_a_3925_, 1);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = lean_box(0);
v___x_3927_ = ((size_t)1ULL);
v___x_3928_ = lean_usize_add(v_i_3915_, v___x_3927_);
v_i_3915_ = v___x_3928_;
v_b_3916_ = v___x_3926_;
goto _start;
}
}
else
{
return v___x_3924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object* v_as_3930_, lean_object* v_sz_3931_, lean_object* v_i_3932_, lean_object* v_b_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
size_t v_sz_boxed_3937_; size_t v_i_boxed_3938_; lean_object* v_res_3939_; 
v_sz_boxed_3937_ = lean_unbox_usize(v_sz_3931_);
lean_dec(v_sz_3931_);
v_i_boxed_3938_ = lean_unbox_usize(v_i_3932_);
lean_dec(v_i_3932_);
v_res_3939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_3930_, v_sz_boxed_3937_, v_i_boxed_3938_, v_b_3933_, v___y_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v_as_3930_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object* v___x_3940_, lean_object* v_a_3941_, lean_object* v___x_3942_, lean_object* v_ns_3943_, lean_object* v_id_3944_, uint8_t v_danglingDot_3945_, lean_object* v_alias_3946_, lean_object* v_declNames_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v___y_3957_; uint8_t v___x_3961_; 
v___x_3961_ = l_Lean_Name_isPrefixOf(v_ns_3943_, v_alias_3946_);
if (v___x_3961_ == 0)
{
v___y_3957_ = v___x_3961_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3962_ = lean_box(0);
lean_inc(v_alias_3946_);
v___x_3963_ = l_Lean_Name_replacePrefix(v_alias_3946_, v_ns_3943_, v___x_3962_);
v___x_3964_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3944_, v___x_3963_, v_danglingDot_3945_);
lean_dec(v___x_3963_);
v___y_3957_ = v___x_3964_;
goto v___jp_3956_;
}
v___jp_3956_:
{
if (v___y_3957_ == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec(v_declNames_3947_);
lean_dec(v_alias_3946_);
lean_dec_ref(v___x_3942_);
v___x_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3940_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
else
{
lean_object* v___x_3960_; 
v___x_3960_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_3941_, v___x_3942_, v_alias_3946_, v_declNames_3947_, v___y_3948_, v___y_3949_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v_alias_3946_);
return v___x_3960_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_3965_, lean_object* v_a_3966_, lean_object* v___x_3967_, lean_object* v_ns_3968_, lean_object* v_id_3969_, lean_object* v_danglingDot_3970_, lean_object* v_alias_3971_, lean_object* v_declNames_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
uint8_t v_danglingDot_boxed_3981_; lean_object* v_res_3982_; 
v_danglingDot_boxed_3981_ = lean_unbox(v_danglingDot_3970_);
v_res_3982_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_3965_, v_a_3966_, v___x_3967_, v_ns_3968_, v_id_3969_, v_danglingDot_boxed_3981_, v_alias_3971_, v_declNames_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v_id_3969_);
lean_dec(v_ns_3968_);
lean_dec_ref(v_a_3966_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(lean_object* v_a_3983_, lean_object* v___x_3984_, lean_object* v_id_3985_, uint8_t v_danglingDot_3986_, lean_object* v_as_x27_3987_, lean_object* v_b_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_a_3998_; 
if (lean_obj_tag(v_as_x27_3987_) == 0)
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
lean_dec(v_id_3985_);
lean_dec_ref(v___x_3984_);
lean_dec_ref(v_a_3983_);
v___x_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4001_, 0, v_b_3988_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
else
{
lean_object* v_head_4003_; lean_object* v_tail_4004_; lean_object* v___x_4005_; 
v_head_4003_ = lean_ctor_get(v_as_x27_3987_, 0);
v_tail_4004_ = lean_ctor_get(v_as_x27_3987_, 1);
v___x_4005_ = lean_box(0);
if (lean_obj_tag(v_head_4003_) == 0)
{
lean_object* v_ns_4006_; lean_object* v___x_4007_; lean_object* v___f_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_ns_4006_ = lean_ctor_get(v_head_4003_, 0);
v___x_4007_ = lean_box(v_danglingDot_3986_);
lean_inc(v_id_3985_);
lean_inc(v_ns_4006_);
lean_inc_ref_n(v___x_3984_, 2);
lean_inc_ref(v_a_3983_);
v___f_4008_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4008_, 0, v___x_4005_);
lean_closure_set(v___f_4008_, 1, v_a_3983_);
lean_closure_set(v___f_4008_, 2, v___x_3984_);
lean_closure_set(v___f_4008_, 3, v_ns_4006_);
lean_closure_set(v___f_4008_, 4, v_id_3985_);
lean_closure_set(v___f_4008_, 5, v___x_4007_);
v___x_4009_ = l_Lean_getAliasState(v___x_3984_);
v___x_4010_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4009_, v___f_4008_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
if (lean_obj_tag(v_a_4011_) == 0)
{
lean_object* v_a_4012_; 
lean_dec(v_id_3985_);
lean_dec_ref(v___x_3984_);
lean_dec_ref(v_a_3983_);
v_a_4012_ = lean_ctor_get(v_a_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v_a_4011_, 1);
v_a_3998_ = v_a_4012_;
goto v___jp_3997_;
}
else
{
lean_dec_ref_known(v_a_4011_, 1);
v_as_x27_3987_ = v_tail_4004_;
v_b_3988_ = v___x_4005_;
goto _start;
}
}
else
{
lean_dec(v_id_3985_);
lean_dec_ref(v___x_3984_);
lean_dec_ref(v_a_3983_);
return v___x_4010_;
}
}
else
{
lean_object* v_id_4014_; lean_object* v_declName_4015_; uint8_t v___x_4016_; 
v_id_4014_ = lean_ctor_get(v_head_4003_, 0);
v_declName_4015_ = lean_ctor_get(v_head_4003_, 1);
lean_inc(v_declName_4015_);
lean_inc_ref(v___x_3984_);
v___x_4016_ = l_Lean_Server_Completion_allowCompletion(v_a_3983_, v___x_3984_, v_declName_4015_);
if (v___x_4016_ == 0)
{
v_as_x27_3987_ = v_tail_4004_;
v_b_3988_ = v___x_4005_;
goto _start;
}
else
{
uint8_t v___x_4018_; 
v___x_4018_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3985_, v_id_4014_, v_danglingDot_3986_);
if (v___x_4018_ == 0)
{
v_as_x27_3987_ = v_tail_4004_;
v_b_3988_ = v___x_4005_;
goto _start;
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4020_ = l_Lean_Name_getString_x21(v_id_4014_);
v___x_4021_ = lean_box(0);
v___x_4022_ = l_Lean_Name_str___override(v___x_4021_, v___x_4020_);
lean_inc(v_declName_4015_);
v___x_4023_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4022_, v_declName_4015_, v___y_3989_, v___y_3990_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_dec_ref_known(v___x_4023_, 1);
v_as_x27_3987_ = v_tail_4004_;
v_b_3988_ = v___x_4005_;
goto _start;
}
else
{
lean_dec(v_id_3985_);
lean_dec_ref(v___x_3984_);
lean_dec_ref(v_a_3983_);
return v___x_4023_;
}
}
}
}
}
v___jp_3997_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v_a_3998_);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg___boxed(lean_object* v_a_4025_, lean_object* v___x_4026_, lean_object* v_id_4027_, lean_object* v_danglingDot_4028_, lean_object* v_as_x27_4029_, lean_object* v_b_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
uint8_t v_danglingDot_boxed_4039_; lean_object* v_res_4040_; 
v_danglingDot_boxed_4039_ = lean_unbox(v_danglingDot_4028_);
v_res_4040_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(v_a_4025_, v___x_4026_, v_id_4027_, v_danglingDot_boxed_4039_, v_as_x27_4029_, v_b_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v_as_x27_4029_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_id_4041_, uint8_t v_danglingDot_4042_, lean_object* v_a_4043_, lean_object* v___x_4044_, lean_object* v_as_4045_, lean_object* v_as_x27_4046_, lean_object* v_b_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_a_4057_; 
if (lean_obj_tag(v_as_x27_4046_) == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
lean_dec_ref(v___x_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_id_4041_);
v___x_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_b_4047_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
return v___x_4061_;
}
else
{
lean_object* v_head_4062_; lean_object* v_tail_4063_; lean_object* v___x_4064_; 
v_head_4062_ = lean_ctor_get(v_as_x27_4046_, 0);
v_tail_4063_ = lean_ctor_get(v_as_x27_4046_, 1);
v___x_4064_ = lean_box(0);
if (lean_obj_tag(v_head_4062_) == 0)
{
lean_object* v_ns_4065_; lean_object* v___x_4066_; lean_object* v___f_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_ns_4065_ = lean_ctor_get(v_head_4062_, 0);
v___x_4066_ = lean_box(v_danglingDot_4042_);
lean_inc(v_id_4041_);
lean_inc(v_ns_4065_);
lean_inc_ref_n(v___x_4044_, 2);
lean_inc_ref(v_a_4043_);
v___f_4067_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4067_, 0, v___x_4064_);
lean_closure_set(v___f_4067_, 1, v_a_4043_);
lean_closure_set(v___f_4067_, 2, v___x_4044_);
lean_closure_set(v___f_4067_, 3, v_ns_4065_);
lean_closure_set(v___f_4067_, 4, v_id_4041_);
lean_closure_set(v___f_4067_, 5, v___x_4066_);
v___x_4068_ = l_Lean_getAliasState(v___x_4044_);
v___x_4069_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4068_, v___f_4067_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
if (lean_obj_tag(v_a_4070_) == 0)
{
lean_object* v_a_4071_; 
lean_dec_ref(v___x_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_id_4041_);
v_a_4071_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v_a_4070_, 1);
v_a_4057_ = v_a_4071_;
goto v___jp_4056_;
}
else
{
lean_object* v___x_4072_; 
lean_dec_ref_known(v_a_4070_, 1);
v___x_4072_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(v_a_4043_, v___x_4044_, v_id_4041_, v_danglingDot_4042_, v_tail_4063_, v___x_4064_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v___x_4072_;
}
}
else
{
lean_dec_ref(v___x_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_id_4041_);
return v___x_4069_;
}
}
else
{
lean_object* v_id_4073_; lean_object* v_declName_4074_; uint8_t v___x_4075_; 
v_id_4073_ = lean_ctor_get(v_head_4062_, 0);
v_declName_4074_ = lean_ctor_get(v_head_4062_, 1);
lean_inc(v_declName_4074_);
lean_inc_ref(v___x_4044_);
v___x_4075_ = l_Lean_Server_Completion_allowCompletion(v_a_4043_, v___x_4044_, v_declName_4074_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; 
v___x_4076_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(v_a_4043_, v___x_4044_, v_id_4041_, v_danglingDot_4042_, v_tail_4063_, v___x_4064_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v___x_4076_;
}
else
{
uint8_t v___x_4077_; 
v___x_4077_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4041_, v_id_4073_, v_danglingDot_4042_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(v_a_4043_, v___x_4044_, v_id_4041_, v_danglingDot_4042_, v_tail_4063_, v___x_4064_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v___x_4078_;
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4079_ = l_Lean_Name_getString_x21(v_id_4073_);
v___x_4080_ = lean_box(0);
v___x_4081_ = l_Lean_Name_str___override(v___x_4080_, v___x_4079_);
lean_inc(v_declName_4074_);
v___x_4082_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4081_, v_declName_4074_, v___y_4048_, v___y_4049_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v___x_4083_; 
lean_dec_ref_known(v___x_4082_, 1);
v___x_4083_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(v_a_4043_, v___x_4044_, v_id_4041_, v_danglingDot_4042_, v_tail_4063_, v___x_4064_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v___x_4083_;
}
else
{
lean_dec_ref(v___x_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_id_4041_);
return v___x_4082_;
}
}
}
}
}
v___jp_4056_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_a_4057_);
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
return v___x_4059_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_id_4084_, lean_object* v_danglingDot_4085_, lean_object* v_a_4086_, lean_object* v___x_4087_, lean_object* v_as_4088_, lean_object* v_as_x27_4089_, lean_object* v_b_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
uint8_t v_danglingDot_boxed_4099_; lean_object* v_res_4100_; 
v_danglingDot_boxed_4099_ = lean_unbox(v_danglingDot_4085_);
v_res_4100_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4084_, v_danglingDot_boxed_4099_, v_a_4086_, v___x_4087_, v_as_4088_, v_as_x27_4089_, v_b_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v_as_x27_4089_);
lean_dec(v_as_4088_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4101_, lean_object* v_stx_4102_, lean_object* v_id_4103_, lean_object* v_hoverInfo_4104_, uint8_t v_danglingDot_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; uint8_t v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v_id_4166_; uint8_t v_danglingDot_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v_id_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; uint8_t v___x_4197_; 
v___x_4197_ = l_Lean_Name_hasMacroScopes(v_id_4103_);
if (v___x_4197_ == 0)
{
v_id_4186_ = v_id_4103_;
v___y_4187_ = v_a_4106_;
v___y_4188_ = v_a_4107_;
v___y_4189_ = v_a_4108_;
v___y_4190_ = v_a_4109_;
v___y_4191_ = v_a_4110_;
v___y_4192_ = v_a_4111_;
v___y_4193_ = v_a_4112_;
goto v___jp_4185_;
}
else
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lean_Syntax_getHeadInfo(v_stx_4102_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_id_4199_; 
lean_dec_ref_known(v___x_4198_, 4);
v_id_4199_ = l_Lean_Name_eraseMacroScopes(v_id_4103_);
lean_dec(v_id_4103_);
v_id_4186_ = v_id_4199_;
v___y_4187_ = v_a_4106_;
v___y_4188_ = v_a_4107_;
v___y_4189_ = v_a_4108_;
v___y_4190_ = v_a_4109_;
v___y_4191_ = v_a_4110_;
v___y_4192_ = v_a_4111_;
v___y_4193_ = v_a_4112_;
goto v___jp_4185_;
}
else
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
lean_dec(v___x_4198_);
lean_dec(v_hoverInfo_4104_);
lean_dec(v_id_4103_);
lean_dec_ref(v_ctx_4101_);
v___x_4200_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
return v___x_4201_;
}
}
v___jp_4114_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_st_ref_get(v___y_4118_);
v___x_4127_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4116_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
if (lean_obj_tag(v_a_4128_) == 0)
{
lean_dec_ref_known(v_a_4128_, 1);
lean_dec(v___x_4126_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4127_;
}
else
{
lean_object* v___x_4129_; lean_object* v_a_4130_; 
lean_dec_ref_known(v_a_4128_, 1);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4125_);
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
if (lean_obj_tag(v_a_4130_) == 0)
{
lean_dec_ref_known(v_a_4130_, 1);
lean_dec(v___x_4126_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4129_;
}
else
{
lean_object* v_env_4131_; lean_object* v___x_4132_; 
lean_dec_ref_known(v_a_4130_, 1);
lean_dec_ref(v___x_4129_);
v_env_4131_ = lean_ctor_get(v___x_4126_, 0);
lean_inc_ref_n(v_env_4131_, 2);
lean_dec(v___x_4126_);
v___x_4132_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4131_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_toCommandContextInfo_4133_; lean_object* v_a_4134_; lean_object* v_currNamespace_4135_; lean_object* v_openDecls_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v_toCommandContextInfo_4133_ = lean_ctor_get(v_ctx_4101_, 0);
v_a_4134_ = lean_ctor_get(v___x_4132_, 0);
lean_inc_n(v_a_4134_, 2);
lean_dec_ref_known(v___x_4132_, 1);
v_currNamespace_4135_ = lean_ctor_get(v_toCommandContextInfo_4133_, 5);
v_openDecls_4136_ = lean_ctor_get(v_toCommandContextInfo_4133_, 6);
v___x_4137_ = lean_box(0);
lean_inc_ref(v_env_4131_);
lean_inc(v___y_4117_);
v___x_4138_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___y_4117_, v___y_4123_, v_a_4134_, v_env_4131_, v_openDecls_4136_, v_openDecls_4136_, v___x_4137_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
if (lean_obj_tag(v_a_4139_) == 0)
{
lean_dec_ref_known(v_a_4139_, 1);
lean_dec(v_a_4134_);
lean_dec_ref(v_env_4131_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4138_;
}
else
{
lean_object* v___f_4140_; lean_object* v___f_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec_ref_known(v_a_4139_, 1);
lean_dec_ref_known(v___x_4138_, 1);
lean_inc_ref_n(v_env_4131_, 2);
v___f_4140_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4140_, 0, v_a_4134_);
lean_closure_set(v___f_4140_, 1, v_env_4131_);
lean_inc(v_currNamespace_4135_);
v___f_4141_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4141_, 0, v___y_4121_);
lean_closure_set(v___f_4141_, 1, v___f_4140_);
lean_closure_set(v___f_4141_, 2, v_currNamespace_4135_);
v___x_4142_ = l_Lean_getAliasState(v_env_4131_);
v___x_4143_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4142_, v___f_4141_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
if (lean_obj_tag(v_a_4144_) == 0)
{
lean_dec_ref_known(v_a_4144_, 1);
lean_dec_ref(v_env_4131_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4143_;
}
else
{
lean_dec_ref_known(v_a_4144_, 1);
lean_dec_ref_known(v___x_4143_, 1);
if (v___y_4123_ == 0)
{
if (lean_obj_tag(v___y_4117_) == 1)
{
lean_object* v_pre_4145_; 
v_pre_4145_ = lean_ctor_get(v___y_4117_, 0);
if (lean_obj_tag(v_pre_4145_) == 0)
{
lean_object* v_str_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; size_t v_sz_4149_; size_t v___x_4150_; lean_object* v___x_4151_; 
v_str_4146_ = lean_ctor_get(v___y_4117_, 1);
v___x_4147_ = l_Lean_Parser_getTokenTable(v_env_4131_);
v___x_4148_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4147_, v_str_4146_);
lean_dec_ref(v___x_4147_);
v_sz_4149_ = lean_array_size(v___x_4148_);
v___x_4150_ = ((size_t)0ULL);
v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v___x_4148_, v_sz_4149_, v___x_4150_, v___x_4137_, v___y_4115_, v___y_4120_);
lean_dec_ref(v___x_4148_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
if (lean_obj_tag(v_a_4152_) == 0)
{
lean_dec_ref_known(v_a_4152_, 1);
lean_dec_ref_known(v___y_4117_, 2);
lean_dec_ref(v_ctx_4101_);
return v___x_4151_;
}
else
{
lean_object* v___x_4153_; 
lean_dec_ref_known(v_a_4152_, 1);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4101_, v___y_4117_, v___y_4123_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
return v___x_4153_;
}
}
else
{
lean_dec_ref_known(v___y_4117_, 2);
lean_dec_ref(v_ctx_4101_);
return v___x_4151_;
}
}
else
{
lean_object* v___x_4154_; 
lean_dec_ref(v_env_4131_);
v___x_4154_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4101_, v___y_4117_, v___y_4123_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
return v___x_4154_;
}
}
else
{
lean_object* v___x_4155_; 
lean_dec_ref(v_env_4131_);
v___x_4155_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4101_, v___y_4117_, v___y_4123_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
return v___x_4155_;
}
}
else
{
lean_object* v___x_4156_; 
lean_dec_ref(v_env_4131_);
v___x_4156_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4101_, v___y_4117_, v___y_4123_, v___y_4115_, v___y_4120_, v___y_4125_, v___y_4122_, v___y_4124_, v___y_4119_, v___y_4118_);
return v___x_4156_;
}
}
}
else
{
lean_dec_ref(v_env_4131_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4143_;
}
}
}
else
{
lean_dec(v_a_4134_);
lean_dec_ref(v_env_4131_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4138_;
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec_ref(v_env_4131_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
v_a_4157_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4132_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4132_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4126_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v_ctx_4101_);
return v___x_4127_;
}
}
v___jp_4165_:
{
lean_object* v___x_4175_; lean_object* v___f_4176_; lean_object* v___x_4177_; lean_object* v___f_4178_; uint8_t v___x_4179_; 
v___x_4175_ = lean_box(v_danglingDot_4167_);
lean_inc_n(v_id_4166_, 2);
lean_inc_ref(v_ctx_4101_);
v___f_4176_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4176_, 0, v_ctx_4101_);
lean_closure_set(v___f_4176_, 1, v_id_4166_);
lean_closure_set(v___f_4176_, 2, v___x_4175_);
v___x_4177_ = lean_box(v_danglingDot_4167_);
v___f_4178_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4178_, 0, v_id_4166_);
lean_closure_set(v___f_4178_, 1, v___x_4177_);
v___x_4179_ = l_Lean_Name_isAtomic(v_id_4166_);
if (v___x_4179_ == 0)
{
v___y_4115_ = v___y_4168_;
v___y_4116_ = v___f_4176_;
v___y_4117_ = v_id_4166_;
v___y_4118_ = v___y_4174_;
v___y_4119_ = v___y_4173_;
v___y_4120_ = v___y_4169_;
v___y_4121_ = v___f_4178_;
v___y_4122_ = v___y_4171_;
v___y_4123_ = v_danglingDot_4167_;
v___y_4124_ = v___y_4172_;
v___y_4125_ = v___y_4170_;
goto v___jp_4114_;
}
else
{
lean_object* v_lctx_4180_; lean_object* v_decls_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_lctx_4180_ = lean_ctor_get(v___y_4171_, 2);
v_decls_4181_ = lean_ctor_get(v_lctx_4180_, 1);
v___x_4182_ = lean_box(0);
v___x_4183_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4166_, v_danglingDot_4167_, v_decls_4181_, v___x_4182_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
if (lean_obj_tag(v_a_4184_) == 0)
{
lean_dec_ref_known(v_a_4184_, 1);
lean_dec_ref(v___f_4178_);
lean_dec_ref(v___f_4176_);
lean_dec(v_id_4166_);
lean_dec_ref(v_ctx_4101_);
return v___x_4183_;
}
else
{
lean_dec_ref_known(v_a_4184_, 1);
lean_dec_ref_known(v___x_4183_, 1);
v___y_4115_ = v___y_4168_;
v___y_4116_ = v___f_4176_;
v___y_4117_ = v_id_4166_;
v___y_4118_ = v___y_4174_;
v___y_4119_ = v___y_4173_;
v___y_4120_ = v___y_4169_;
v___y_4121_ = v___f_4178_;
v___y_4122_ = v___y_4171_;
v___y_4123_ = v_danglingDot_4167_;
v___y_4124_ = v___y_4172_;
v___y_4125_ = v___y_4170_;
goto v___jp_4114_;
}
}
else
{
lean_dec_ref(v___f_4178_);
lean_dec_ref(v___f_4176_);
lean_dec(v_id_4166_);
lean_dec_ref(v_ctx_4101_);
return v___x_4183_;
}
}
}
v___jp_4185_:
{
if (lean_obj_tag(v_hoverInfo_4104_) == 1)
{
lean_object* v_delta_4194_; lean_object* v_id_4195_; uint8_t v_danglingDot_4196_; 
v_delta_4194_ = lean_ctor_get(v_hoverInfo_4104_, 0);
lean_inc(v_delta_4194_);
lean_dec_ref_known(v_hoverInfo_4104_, 1);
v_id_4195_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4186_, v_delta_4194_);
v_danglingDot_4196_ = 0;
v_id_4166_ = v_id_4195_;
v_danglingDot_4167_ = v_danglingDot_4196_;
v___y_4168_ = v___y_4187_;
v___y_4169_ = v___y_4188_;
v___y_4170_ = v___y_4189_;
v___y_4171_ = v___y_4190_;
v___y_4172_ = v___y_4191_;
v___y_4173_ = v___y_4192_;
v___y_4174_ = v___y_4193_;
goto v___jp_4165_;
}
else
{
lean_dec(v_hoverInfo_4104_);
v_id_4166_ = v_id_4186_;
v_danglingDot_4167_ = v_danglingDot_4105_;
v___y_4168_ = v___y_4187_;
v___y_4169_ = v___y_4188_;
v___y_4170_ = v___y_4189_;
v___y_4171_ = v___y_4190_;
v___y_4172_ = v___y_4191_;
v___y_4173_ = v___y_4192_;
v___y_4174_ = v___y_4193_;
goto v___jp_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4202_, lean_object* v_stx_4203_, lean_object* v_id_4204_, lean_object* v_hoverInfo_4205_, lean_object* v_danglingDot_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
uint8_t v_danglingDot_boxed_4215_; lean_object* v_res_4216_; 
v_danglingDot_boxed_4215_ = lean_unbox(v_danglingDot_4206_);
v_res_4216_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4202_, v_stx_4203_, v_id_4204_, v_hoverInfo_4205_, v_danglingDot_boxed_4215_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_stx_4203_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4217_, lean_object* v___x_4218_, lean_object* v_alias_4219_, lean_object* v_as_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4217_, v___x_4218_, v_alias_4219_, v_as_4220_, v___y_4221_, v___y_4222_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4230_, lean_object* v___x_4231_, lean_object* v_alias_4232_, lean_object* v_as_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4230_, v___x_4231_, v_alias_4232_, v_as_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v_alias_4232_);
lean_dec_ref(v_a_4230_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_00_u03b2_4243_, lean_object* v_s_4244_, lean_object* v_f_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_4244_, v_f_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_00_u03b2_4255_, lean_object* v_s_4256_, lean_object* v_f_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_00_u03b2_4255_, v_s_4256_, v_f_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_id_4267_, uint8_t v_danglingDot_4268_, lean_object* v_a_4269_, lean_object* v___x_4270_, lean_object* v_as_4271_, lean_object* v_as_x27_4272_, lean_object* v_b_4273_, lean_object* v_a_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4267_, v_danglingDot_4268_, v_a_4269_, v___x_4270_, v_as_4271_, v_as_x27_4272_, v_b_4273_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_id_4284_, lean_object* v_danglingDot_4285_, lean_object* v_a_4286_, lean_object* v___x_4287_, lean_object* v_as_4288_, lean_object* v_as_x27_4289_, lean_object* v_b_4290_, lean_object* v_a_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
uint8_t v_danglingDot_boxed_4300_; lean_object* v_res_4301_; 
v_danglingDot_boxed_4300_ = lean_unbox(v_danglingDot_4285_);
v_res_4301_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4284_, v_danglingDot_boxed_4300_, v_a_4286_, v___x_4287_, v_as_4288_, v_as_x27_4289_, v_b_4290_, v_a_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v_as_x27_4289_);
lean_dec(v_as_4288_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_as_4302_, size_t v_sz_4303_, size_t v_i_4304_, lean_object* v_b_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4302_, v_sz_4303_, v_i_4304_, v_b_4305_, v___y_4306_, v___y_4307_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_as_4315_, lean_object* v_sz_4316_, lean_object* v_i_4317_, lean_object* v_b_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
size_t v_sz_boxed_4327_; size_t v_i_boxed_4328_; lean_object* v_res_4329_; 
v_sz_boxed_4327_ = lean_unbox_usize(v_sz_4316_);
lean_dec(v_sz_4316_);
v_i_boxed_4328_ = lean_unbox_usize(v_i_4317_);
lean_dec(v_i_4317_);
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4315_, v_sz_boxed_4327_, v_i_boxed_4328_, v_b_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec_ref(v_as_4315_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_00_u03b2_4330_, lean_object* v_f_4331_, lean_object* v_init_4332_, lean_object* v_b_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_4331_, v_init_4332_, v_b_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4343_, lean_object* v_f_4344_, lean_object* v_init_4345_, lean_object* v_b_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_00_u03b2_4343_, v_f_4344_, v_init_4345_, v_b_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec_ref(v_b_4346_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object* v_00_u03b2_4356_, lean_object* v_map_4357_, lean_object* v_f_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_4357_, v_f_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4368_, lean_object* v_map_4369_, lean_object* v_f_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(v_00_u03b2_4368_, v_map_4369_, v_f_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7(lean_object* v_a_4380_, lean_object* v___x_4381_, lean_object* v_id_4382_, uint8_t v_danglingDot_4383_, lean_object* v_as_4384_, lean_object* v_as_x27_4385_, lean_object* v_b_4386_, lean_object* v_a_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___redArg(v_a_4380_, v___x_4381_, v_id_4382_, v_danglingDot_4383_, v_as_x27_4385_, v_b_4386_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7___boxed(lean_object* v_a_4397_, lean_object* v___x_4398_, lean_object* v_id_4399_, lean_object* v_danglingDot_4400_, lean_object* v_as_4401_, lean_object* v_as_x27_4402_, lean_object* v_b_4403_, lean_object* v_a_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
uint8_t v_danglingDot_boxed_4413_; lean_object* v_res_4414_; 
v_danglingDot_boxed_4413_ = lean_unbox(v_danglingDot_4400_);
v_res_4414_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__7(v_a_4397_, v___x_4398_, v_id_4399_, v_danglingDot_boxed_4413_, v_as_4401_, v_as_x27_4402_, v_b_4403_, v_a_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v_as_x27_4402_);
lean_dec(v_as_4401_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4415_, lean_object* v_map_4416_, lean_object* v_f_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4416_, v_f_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4428_, lean_object* v_map_4429_, lean_object* v_f_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4428_, v_map_4429_, v_f_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_4441_, lean_object* v_f_4442_, lean_object* v_b_4443_, lean_object* v_acc_4444_, lean_object* v_i_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v___x_4454_; 
v___x_4454_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___redArg(v_f_4442_, v_b_4443_, v_acc_4444_, v_i_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_4455_, lean_object* v_f_4456_, lean_object* v_b_4457_, lean_object* v_acc_4458_, lean_object* v_i_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4_spec__7(v_00_u03b2_4455_, v_f_4456_, v_b_4457_, v_acc_4458_, v_i_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec_ref(v_b_4457_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object* v_map_4469_, lean_object* v_f_4470_, lean_object* v_init_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(v_f_4470_, v_map_4469_, v_init_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_map_4481_, lean_object* v_f_4482_, lean_object* v_init_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4481_, v_f_4482_, v_init_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_4493_, lean_object* v_00_u03b2_4494_, lean_object* v_map_4495_, lean_object* v_f_4496_, lean_object* v_init_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(v_f_4496_, v_map_4495_, v_init_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_4507_, lean_object* v_00_u03b2_4508_, lean_object* v_map_4509_, lean_object* v_f_4510_, lean_object* v_init_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(v_00_u03c3_4507_, v_00_u03b2_4508_, v_map_4509_, v_f_4510_, v_init_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18(lean_object* v_id_4521_, uint8_t v_danglingDot_4522_, lean_object* v_as_4523_, size_t v_sz_4524_, size_t v_i_4525_, lean_object* v_b_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___redArg(v_id_4521_, v_danglingDot_4522_, v_as_4523_, v_sz_4524_, v_i_4525_, v_b_4526_, v___y_4527_, v___y_4528_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18___boxed(lean_object* v_id_4536_, lean_object* v_danglingDot_4537_, lean_object* v_as_4538_, lean_object* v_sz_4539_, lean_object* v_i_4540_, lean_object* v_b_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
uint8_t v_danglingDot_boxed_4550_; size_t v_sz_boxed_4551_; size_t v_i_boxed_4552_; lean_object* v_res_4553_; 
v_danglingDot_boxed_4550_ = lean_unbox(v_danglingDot_4537_);
v_sz_boxed_4551_ = lean_unbox_usize(v_sz_4539_);
lean_dec(v_sz_4539_);
v_i_boxed_4552_ = lean_unbox_usize(v_i_4540_);
lean_dec(v_i_4540_);
v_res_4553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__18(v_id_4536_, v_danglingDot_boxed_4550_, v_as_4538_, v_sz_boxed_4551_, v_i_boxed_4552_, v_b_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec_ref(v_as_4538_);
lean_dec(v_id_4536_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_map_4554_, lean_object* v_f_4555_, lean_object* v_init_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(v_f_4555_, v_map_4554_, v_init_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_map_4567_, lean_object* v_f_4568_, lean_object* v_init_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___redArg(v_map_4567_, v_f_4568_, v_init_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03c3_4580_, lean_object* v_00_u03b2_4581_, lean_object* v_map_4582_, lean_object* v_f_4583_, lean_object* v_init_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(v_f_4583_, v_map_4582_, v_init_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03c3_4595_, lean_object* v_00_u03b2_4596_, lean_object* v_map_4597_, lean_object* v_f_4598_, lean_object* v_init_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10(v_00_u03c3_4595_, v_00_u03b2_4596_, v_map_4597_, v_f_4598_, v_init_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15(lean_object* v_00_u03c3_4610_, lean_object* v_00_u03b1_4611_, lean_object* v_00_u03b2_4612_, lean_object* v_f_4613_, lean_object* v_x_4614_, lean_object* v_x_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v___x_4624_; 
v___x_4624_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___redArg(v_f_4613_, v_x_4614_, v_x_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15___boxed(lean_object* v_00_u03c3_4625_, lean_object* v_00_u03b1_4626_, lean_object* v_00_u03b2_4627_, lean_object* v_f_4628_, lean_object* v_x_4629_, lean_object* v_x_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15(v_00_u03c3_4625_, v_00_u03b1_4626_, v_00_u03b2_4627_, v_f_4628_, v_x_4629_, v_x_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20(lean_object* v_id_4640_, uint8_t v_danglingDot_4641_, lean_object* v_as_4642_, size_t v_sz_4643_, size_t v_i_4644_, lean_object* v_b_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___redArg(v_id_4640_, v_danglingDot_4641_, v_as_4642_, v_sz_4643_, v_i_4644_, v_b_4645_, v___y_4646_, v___y_4647_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20___boxed(lean_object* v_id_4655_, lean_object* v_danglingDot_4656_, lean_object* v_as_4657_, lean_object* v_sz_4658_, lean_object* v_i_4659_, lean_object* v_b_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
uint8_t v_danglingDot_boxed_4669_; size_t v_sz_boxed_4670_; size_t v_i_boxed_4671_; lean_object* v_res_4672_; 
v_danglingDot_boxed_4669_ = lean_unbox(v_danglingDot_4656_);
v_sz_boxed_4670_ = lean_unbox_usize(v_sz_4658_);
lean_dec(v_sz_4658_);
v_i_boxed_4671_ = lean_unbox_usize(v_i_4659_);
lean_dec(v_i_4659_);
v_res_4672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__10_spec__16_spec__20(v_id_4655_, v_danglingDot_boxed_4669_, v_as_4657_, v_sz_boxed_4670_, v_i_boxed_4671_, v_b_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v_as_4657_);
lean_dec(v_id_4655_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16(lean_object* v_00_u03c3_4673_, lean_object* v_00_u03b1_4674_, lean_object* v_00_u03b2_4675_, lean_object* v_f_4676_, lean_object* v_x_4677_, lean_object* v_x_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___redArg(v_f_4676_, v_x_4677_, v_x_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16___boxed(lean_object* v_00_u03c3_4689_, lean_object* v_00_u03b1_4690_, lean_object* v_00_u03b2_4691_, lean_object* v_f_4692_, lean_object* v_x_4693_, lean_object* v_x_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16(v_00_u03c3_4689_, v_00_u03b1_4690_, v_00_u03b2_4691_, v_f_4692_, v_x_4693_, v_x_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20(lean_object* v_00_u03b1_4705_, lean_object* v_00_u03b2_4706_, lean_object* v_00_u03c3_4707_, lean_object* v_f_4708_, lean_object* v_as_4709_, size_t v_i_4710_, size_t v_stop_4711_, lean_object* v_b_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___redArg(v_f_4708_, v_as_4709_, v_i_4710_, v_stop_4711_, v_b_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20___boxed(lean_object* v_00_u03b1_4722_, lean_object* v_00_u03b2_4723_, lean_object* v_00_u03c3_4724_, lean_object* v_f_4725_, lean_object* v_as_4726_, lean_object* v_i_4727_, lean_object* v_stop_4728_, lean_object* v_b_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
size_t v_i_boxed_4738_; size_t v_stop_boxed_4739_; lean_object* v_res_4740_; 
v_i_boxed_4738_ = lean_unbox_usize(v_i_4727_);
lean_dec(v_i_4727_);
v_stop_boxed_4739_ = lean_unbox_usize(v_stop_4728_);
lean_dec(v_stop_4728_);
v_res_4740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__20(v_00_u03b1_4722_, v_00_u03b2_4723_, v_00_u03c3_4724_, v_f_4725_, v_as_4726_, v_i_boxed_4738_, v_stop_boxed_4739_, v_b_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec_ref(v_as_4726_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21(lean_object* v_00_u03c3_4741_, lean_object* v_00_u03b1_4742_, lean_object* v_00_u03b2_4743_, lean_object* v_f_4744_, lean_object* v_keys_4745_, lean_object* v_vals_4746_, lean_object* v_heq_4747_, lean_object* v_i_4748_, lean_object* v_acc_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v___x_4758_; 
v___x_4758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___redArg(v_f_4744_, v_keys_4745_, v_vals_4746_, v_i_4748_, v_acc_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21___boxed(lean_object** _args){
lean_object* v_00_u03c3_4759_ = _args[0];
lean_object* v_00_u03b1_4760_ = _args[1];
lean_object* v_00_u03b2_4761_ = _args[2];
lean_object* v_f_4762_ = _args[3];
lean_object* v_keys_4763_ = _args[4];
lean_object* v_vals_4764_ = _args[5];
lean_object* v_heq_4765_ = _args[6];
lean_object* v_i_4766_ = _args[7];
lean_object* v_acc_4767_ = _args[8];
lean_object* v___y_4768_ = _args[9];
lean_object* v___y_4769_ = _args[10];
lean_object* v___y_4770_ = _args[11];
lean_object* v___y_4771_ = _args[12];
lean_object* v___y_4772_ = _args[13];
lean_object* v___y_4773_ = _args[14];
lean_object* v___y_4774_ = _args[15];
lean_object* v___y_4775_ = _args[16];
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__15_spec__21(v_00_u03c3_4759_, v_00_u03b1_4760_, v_00_u03b2_4761_, v_f_4762_, v_keys_4763_, v_vals_4764_, v_heq_4765_, v_i_4766_, v_acc_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec_ref(v_vals_4764_);
lean_dec_ref(v_keys_4763_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22(lean_object* v_00_u03b1_4777_, lean_object* v_00_u03b2_4778_, lean_object* v_00_u03c3_4779_, lean_object* v_f_4780_, lean_object* v_as_4781_, size_t v_i_4782_, size_t v_stop_4783_, lean_object* v_b_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___redArg(v_f_4780_, v_as_4781_, v_i_4782_, v_stop_4783_, v_b_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22___boxed(lean_object** _args){
lean_object* v_00_u03b1_4795_ = _args[0];
lean_object* v_00_u03b2_4796_ = _args[1];
lean_object* v_00_u03c3_4797_ = _args[2];
lean_object* v_f_4798_ = _args[3];
lean_object* v_as_4799_ = _args[4];
lean_object* v_i_4800_ = _args[5];
lean_object* v_stop_4801_ = _args[6];
lean_object* v_b_4802_ = _args[7];
lean_object* v___y_4803_ = _args[8];
lean_object* v___y_4804_ = _args[9];
lean_object* v___y_4805_ = _args[10];
lean_object* v___y_4806_ = _args[11];
lean_object* v___y_4807_ = _args[12];
lean_object* v___y_4808_ = _args[13];
lean_object* v___y_4809_ = _args[14];
lean_object* v___y_4810_ = _args[15];
lean_object* v___y_4811_ = _args[16];
_start:
{
size_t v_i_boxed_4812_; size_t v_stop_boxed_4813_; lean_object* v_res_4814_; 
v_i_boxed_4812_ = lean_unbox_usize(v_i_4800_);
lean_dec(v_i_4800_);
v_stop_boxed_4813_ = lean_unbox_usize(v_stop_4801_);
lean_dec(v_stop_4801_);
v_res_4814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__22(v_00_u03b1_4795_, v_00_u03b2_4796_, v_00_u03c3_4797_, v_f_4798_, v_as_4799_, v_i_boxed_4812_, v_stop_boxed_4813_, v_b_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec_ref(v_as_4799_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23(lean_object* v_00_u03c3_4815_, lean_object* v_00_u03b1_4816_, lean_object* v_00_u03b2_4817_, lean_object* v_f_4818_, lean_object* v_keys_4819_, lean_object* v_vals_4820_, lean_object* v_heq_4821_, lean_object* v_i_4822_, lean_object* v_acc_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___redArg(v_f_4818_, v_keys_4819_, v_vals_4820_, v_i_4822_, v_acc_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_00_u03c3_4834_ = _args[0];
lean_object* v_00_u03b1_4835_ = _args[1];
lean_object* v_00_u03b2_4836_ = _args[2];
lean_object* v_f_4837_ = _args[3];
lean_object* v_keys_4838_ = _args[4];
lean_object* v_vals_4839_ = _args[5];
lean_object* v_heq_4840_ = _args[6];
lean_object* v_i_4841_ = _args[7];
lean_object* v_acc_4842_ = _args[8];
lean_object* v___y_4843_ = _args[9];
lean_object* v___y_4844_ = _args[10];
lean_object* v___y_4845_ = _args[11];
lean_object* v___y_4846_ = _args[12];
lean_object* v___y_4847_ = _args[13];
lean_object* v___y_4848_ = _args[14];
lean_object* v___y_4849_ = _args[15];
lean_object* v___y_4850_ = _args[16];
lean_object* v___y_4851_ = _args[17];
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__10_spec__16_spec__23(v_00_u03c3_4834_, v_00_u03b1_4835_, v_00_u03b2_4836_, v_f_4837_, v_keys_4838_, v_vals_4839_, v_heq_4840_, v_i_4841_, v_acc_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec_ref(v_vals_4839_);
lean_dec_ref(v_keys_4838_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4853_, lean_object* v_pos_4854_, lean_object* v_completionInfoPos_4855_, lean_object* v_ctx_4856_, lean_object* v_lctx_4857_, lean_object* v_stx_4858_, lean_object* v_id_4859_, lean_object* v_hoverInfo_4860_, uint8_t v_danglingDot_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4864_ = lean_box(v_danglingDot_4861_);
lean_inc_ref(v_ctx_4856_);
v___x_4865_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_4865_, 0, v_ctx_4856_);
lean_closure_set(v___x_4865_, 1, v_stx_4858_);
lean_closure_set(v___x_4865_, 2, v_id_4859_);
lean_closure_set(v___x_4865_, 3, v_hoverInfo_4860_);
lean_closure_set(v___x_4865_, 4, v___x_4864_);
v___x_4866_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4853_, v_pos_4854_, v_completionInfoPos_4855_, v_ctx_4856_, v_lctx_4857_, v___x_4865_, v_a_4862_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_4867_, lean_object* v_pos_4868_, lean_object* v_completionInfoPos_4869_, lean_object* v_ctx_4870_, lean_object* v_lctx_4871_, lean_object* v_stx_4872_, lean_object* v_id_4873_, lean_object* v_hoverInfo_4874_, lean_object* v_danglingDot_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
uint8_t v_danglingDot_boxed_4878_; lean_object* v_res_4879_; 
v_danglingDot_boxed_4878_ = lean_unbox(v_danglingDot_4875_);
v_res_4879_ = l_Lean_Server_Completion_idCompletion(v_uri_4867_, v_pos_4868_, v_completionInfoPos_4869_, v_ctx_4870_, v_lctx_4871_, v_stx_4872_, v_id_4873_, v_hoverInfo_4874_, v_danglingDot_boxed_4878_, v_a_4876_);
lean_dec_ref(v_a_4876_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_4880_, lean_object* v___y_4881_){
_start:
{
uint8_t v___x_4883_; 
v___x_4883_ = l_Lean_Expr_hasMVar(v_e_4880_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4884_, 0, v_e_4880_);
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
return v___x_4885_;
}
else
{
lean_object* v___x_4886_; lean_object* v_mctx_4887_; lean_object* v___x_4888_; lean_object* v_fst_4889_; lean_object* v_snd_4890_; lean_object* v___x_4891_; lean_object* v_cache_4892_; lean_object* v_zetaDeltaFVarIds_4893_; lean_object* v_postponed_4894_; lean_object* v_diag_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4905_; 
v___x_4886_ = lean_st_ref_get(v___y_4881_);
v_mctx_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc_ref(v_mctx_4887_);
lean_dec(v___x_4886_);
v___x_4888_ = l_Lean_instantiateMVarsCore(v_mctx_4887_, v_e_4880_);
v_fst_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_fst_4889_);
v_snd_4890_ = lean_ctor_get(v___x_4888_, 1);
lean_inc(v_snd_4890_);
lean_dec_ref(v___x_4888_);
v___x_4891_ = lean_st_ref_take(v___y_4881_);
v_cache_4892_ = lean_ctor_get(v___x_4891_, 1);
v_zetaDeltaFVarIds_4893_ = lean_ctor_get(v___x_4891_, 2);
v_postponed_4894_ = lean_ctor_get(v___x_4891_, 3);
v_diag_4895_ = lean_ctor_get(v___x_4891_, 4);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; 
v_unused_4906_ = lean_ctor_get(v___x_4891_, 0);
lean_dec(v_unused_4906_);
v___x_4897_ = v___x_4891_;
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_diag_4895_);
lean_inc(v_postponed_4894_);
lean_inc(v_zetaDeltaFVarIds_4893_);
lean_inc(v_cache_4892_);
lean_dec(v___x_4891_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v_snd_4890_);
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_snd_4890_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_cache_4892_);
lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_zetaDeltaFVarIds_4893_);
lean_ctor_set(v_reuseFailAlloc_4904_, 3, v_postponed_4894_);
lean_ctor_set(v_reuseFailAlloc_4904_, 4, v_diag_4895_);
v___x_4900_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4901_ = lean_st_ref_put(v___y_4881_, v___x_4900_);
v___x_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4902_, 0, v_fst_4889_);
v___x_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
return v___x_4903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v_res_4910_; 
v_res_4910_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4907_, v___y_4908_);
lean_dec(v___y_4908_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4911_, v___y_4916_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_4931_, lean_object* v_declName_4932_, lean_object* v_decl_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v_unnormedTypeName_4942_; uint8_t v___x_4943_; 
v_unnormedTypeName_4942_ = l_Lean_Name_getPrefix(v_declName_4932_);
v___x_4943_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_4942_, v_a_4931_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
lean_dec_ref(v_decl_4933_);
lean_dec(v_declName_4932_);
v___x_4944_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
return v___x_4945_;
}
else
{
lean_object* v___x_4946_; lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_5012_; 
v___x_4946_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_4932_, v___y_4940_);
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_4949_ = v___x_4946_;
v_isShared_4950_ = v_isSharedCheck_5012_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4946_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_5012_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
if (lean_obj_tag(v_a_4947_) == 1)
{
lean_object* v_val_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_5007_; 
lean_del_object(v___x_4949_);
v_val_4951_ = lean_ctor_get(v_a_4947_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v_a_4947_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_4953_ = v_a_4947_;
v_isShared_4954_ = v_isSharedCheck_5007_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_val_4951_);
lean_dec(v_a_4947_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_5007_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v_info_4955_; lean_object* v_kind_4956_; lean_object* v_tags_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v_info_4955_ = lean_ctor_get(v_decl_4933_, 0);
lean_inc_ref(v_info_4955_);
v_kind_4956_ = lean_ctor_get(v_decl_4933_, 1);
lean_inc_ref(v_kind_4956_);
v_tags_4957_ = lean_ctor_get(v_decl_4933_, 2);
lean_inc_ref(v_tags_4957_);
lean_dec_ref(v_decl_4933_);
v___x_4958_ = l_Lean_Name_getPrefix(v_val_4951_);
lean_dec(v_val_4951_);
v___x_4959_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_4958_, v_info_4955_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4998_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4962_ = v___x_4959_;
v_isShared_4963_ = v_isSharedCheck_4998_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4998_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
uint8_t v___x_4964_; 
v___x_4964_ = lean_unbox(v_a_4960_);
lean_dec(v_a_4960_);
if (v___x_4964_ == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4967_; 
lean_dec_ref(v_tags_4957_);
lean_dec_ref(v_kind_4956_);
lean_dec_ref(v_info_4955_);
lean_del_object(v___x_4953_);
v___x_4965_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 0, v___x_4965_);
v___x_4967_ = v___x_4962_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4965_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
else
{
lean_object* v___x_4969_; 
lean_del_object(v___x_4962_);
lean_inc(v___y_4940_);
lean_inc_ref(v___y_4939_);
lean_inc(v___y_4938_);
lean_inc_ref(v___y_4937_);
v___x_4969_ = lean_apply_5(v_kind_4956_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, lean_box(0));
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4971_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref_known(v___x_4969_, 1);
lean_inc(v___y_4940_);
lean_inc_ref(v___y_4939_);
lean_inc(v___y_4938_);
lean_inc_ref(v___y_4937_);
v___x_4971_ = lean_apply_5(v_tags_4957_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, lean_box(0));
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4978_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref_known(v___x_4971_, 1);
v___x_4973_ = l_Lean_ConstantInfo_name(v_info_4955_);
lean_dec_ref(v_info_4955_);
v___x_4974_ = l_Lean_Name_getString_x21(v___x_4973_);
v___x_4975_ = lean_box(0);
v___x_4976_ = l_Lean_Name_str___override(v___x_4975_, v___x_4974_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set_tag(v___x_4953_, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4973_);
v___x_4978_ = v___x_4953_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4973_);
v___x_4978_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
uint8_t v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = lean_unbox(v_a_4970_);
lean_dec(v_a_4970_);
v___x_4980_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_4976_, v___x_4978_, v___x_4979_, v_a_4972_, v___y_4934_, v___y_4935_);
return v___x_4980_;
}
}
else
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
lean_dec(v_a_4970_);
lean_dec_ref(v_info_4955_);
lean_del_object(v___x_4953_);
v_a_4982_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4984_ = v___x_4971_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4971_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec_ref(v_tags_4957_);
lean_dec_ref(v_info_4955_);
lean_del_object(v___x_4953_);
v_a_4990_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4969_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4969_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v_tags_4957_);
lean_dec_ref(v_kind_4956_);
lean_dec_ref(v_info_4955_);
lean_del_object(v___x_4953_);
v_a_4999_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4959_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4959_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5010_; 
lean_dec(v_a_4947_);
lean_dec_ref(v_decl_4933_);
v___x_5008_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 0, v___x_5008_);
v___x_5010_ = v___x_4949_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_5013_, lean_object* v_declName_5014_, lean_object* v_decl_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5013_, v_declName_5014_, v_decl_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v_a_5038_; lean_object* v___y_5042_; uint8_t v___y_5043_; lean_object* v___y_5053_; lean_object* v_a_5054_; lean_object* v___x_5057_; 
lean_inc(v___y_5032_);
lean_inc_ref(v___y_5031_);
lean_inc(v___y_5030_);
lean_inc_ref(v___y_5029_);
v___x_5057_ = lean_infer_type(v_expr_5025_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5059_; lean_object* v_a_5060_; lean_object* v_a_5061_; lean_object* v___x_5062_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v___x_5059_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_5058_, v___y_5030_);
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_a_5060_);
lean_dec_ref(v___x_5059_);
v_a_5061_ = lean_ctor_get(v_a_5060_, 0);
lean_inc(v_a_5061_);
lean_dec(v_a_5060_);
v___x_5062_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_5061_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v_a_5038_ = v_a_5063_;
goto v___jp_5037_;
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
v_a_5064_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_5062_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5062_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
lean_inc(v_a_5064_);
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
v___y_5053_ = v___x_5069_;
v_a_5054_ = v_a_5064_;
goto v___jp_5052_;
}
}
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
v_a_5072_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5057_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5057_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
lean_inc(v_a_5072_);
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
v___y_5053_ = v___x_5077_;
v_a_5054_ = v_a_5072_;
goto v___jp_5052_;
}
}
}
v___jp_5034_:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
}
v___jp_5037_:
{
if (lean_obj_tag(v_a_5038_) == 0)
{
lean_object* v___f_5039_; lean_object* v___x_5040_; 
v___f_5039_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5039_, 0, v_a_5038_);
v___x_5040_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5039_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
return v___x_5040_;
}
else
{
goto v___jp_5034_;
}
}
v___jp_5041_:
{
if (v___y_5043_ == 0)
{
lean_dec_ref(v___y_5042_);
goto v___jp_5034_;
}
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v___y_5042_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___y_5042_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___y_5042_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___y_5042_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
v___jp_5052_:
{
uint8_t v___x_5055_; 
v___x_5055_ = l_Lean_Exception_isInterrupt(v_a_5054_);
if (v___x_5055_ == 0)
{
uint8_t v___x_5056_; 
v___x_5056_ = l_Lean_Exception_isRuntime(v_a_5054_);
v___y_5042_ = v___y_5053_;
v___y_5043_ = v___x_5056_;
goto v___jp_5041_;
}
else
{
lean_dec_ref(v_a_5054_);
v___y_5042_ = v___y_5053_;
v___y_5043_ = v___x_5055_;
goto v___jp_5041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5090_, lean_object* v_pos_5091_, lean_object* v_completionInfoPos_5092_, lean_object* v_ctx_5093_, lean_object* v_info_5094_, lean_object* v_a_5095_){
_start:
{
lean_object* v_lctx_5097_; lean_object* v_expr_5098_; lean_object* v___f_5099_; lean_object* v___x_5100_; 
v_lctx_5097_ = lean_ctor_get(v_info_5094_, 1);
lean_inc_ref(v_lctx_5097_);
v_expr_5098_ = lean_ctor_get(v_info_5094_, 3);
lean_inc_ref(v_expr_5098_);
lean_dec_ref(v_info_5094_);
v___f_5099_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5099_, 0, v_expr_5098_);
v___x_5100_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5090_, v_pos_5091_, v_completionInfoPos_5092_, v_ctx_5093_, v_lctx_5097_, v___f_5099_, v_a_5095_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5101_, lean_object* v_pos_5102_, lean_object* v_completionInfoPos_5103_, lean_object* v_ctx_5104_, lean_object* v_info_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_Server_Completion_dotCompletion(v_uri_5101_, v_pos_5102_, v_completionInfoPos_5103_, v_ctx_5104_, v_info_5105_, v_a_5106_);
lean_dec_ref(v_a_5106_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5109_, uint8_t v___x_5110_, lean_object* v_id_5111_, lean_object* v_declName_5112_, lean_object* v_decl_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v___x_5125_; uint8_t v___x_5126_; 
v___x_5125_ = l_Lean_Name_getPrefix(v_declName_5112_);
lean_inc(v___x_5109_);
v___x_5126_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5125_, v___x_5109_);
if (v___x_5126_ == 0)
{
lean_dec_ref(v_decl_5113_);
lean_dec(v_declName_5112_);
lean_dec(v___x_5109_);
goto v___jp_5122_;
}
else
{
if (v___x_5110_ == 0)
{
lean_object* v___x_5127_; lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5224_; 
v___x_5127_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5112_, v___y_5120_);
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5130_ = v___x_5127_;
v_isShared_5131_ = v_isSharedCheck_5224_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5127_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5224_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
if (lean_obj_tag(v_a_5128_) == 1)
{
lean_object* v_val_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5219_; 
lean_del_object(v___x_5130_);
v_val_5132_ = lean_ctor_get(v_a_5128_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_a_5128_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5134_ = v_a_5128_;
v_isShared_5135_ = v_isSharedCheck_5219_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_val_5132_);
lean_dec(v_a_5128_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5219_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v_info_5136_; lean_object* v_kind_5137_; lean_object* v_tags_5138_; lean_object* v___x_5139_; 
v_info_5136_ = lean_ctor_get(v_decl_5113_, 0);
lean_inc_ref(v_info_5136_);
v_kind_5137_ = lean_ctor_get(v_decl_5113_, 1);
lean_inc_ref(v_kind_5137_);
v_tags_5138_ = lean_ctor_get(v_decl_5113_, 2);
lean_inc_ref(v_tags_5138_);
lean_dec_ref(v_decl_5113_);
v___x_5139_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5109_, v_info_5136_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5210_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5210_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5210_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
uint8_t v___x_5144_; 
v___x_5144_ = lean_unbox(v_a_5140_);
lean_dec(v_a_5140_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; lean_object* v___x_5147_; 
lean_dec_ref(v_tags_5138_);
lean_dec_ref(v_kind_5137_);
lean_dec_ref(v_info_5136_);
lean_del_object(v___x_5134_);
lean_dec(v_val_5132_);
v___x_5145_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 0, v___x_5145_);
v___x_5147_ = v___x_5142_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5145_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
else
{
lean_object* v___x_5149_; 
lean_del_object(v___x_5142_);
lean_inc(v___y_5120_);
lean_inc_ref(v___y_5119_);
lean_inc(v___y_5118_);
lean_inc_ref(v___y_5117_);
v___x_5149_ = lean_apply_5(v_kind_5137_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, lean_box(0));
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; lean_object* v___x_5151_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
lean_inc(v___y_5120_);
lean_inc_ref(v___y_5119_);
lean_inc(v___y_5118_);
lean_inc_ref(v___y_5117_);
v___x_5151_ = lean_apply_5(v_tags_5138_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, lean_box(0));
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; uint8_t v___x_5153_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
lean_dec_ref_known(v___x_5151_, 1);
v___x_5153_ = l_Lean_Name_isAnonymous(v_id_5111_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5175_; 
lean_del_object(v___x_5134_);
v___x_5154_ = l_Lean_Name_getPrefix(v_val_5132_);
v___x_5155_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5154_, v_id_5111_, v___x_5153_, v_val_5132_, v___y_5120_);
lean_dec(v___x_5154_);
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5158_ = v___x_5155_;
v_isShared_5159_ = v_isSharedCheck_5175_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5155_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5175_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
if (lean_obj_tag(v_a_5156_) == 1)
{
lean_object* v_val_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5170_; 
lean_del_object(v___x_5158_);
v_val_5160_ = lean_ctor_get(v_a_5156_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v_a_5156_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5162_ = v_a_5156_;
v_isShared_5163_ = v_isSharedCheck_5170_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_val_5160_);
lean_dec(v_a_5156_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5170_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5164_; lean_object* v___x_5166_; 
v___x_5164_ = l_Lean_ConstantInfo_name(v_info_5136_);
lean_dec_ref(v_info_5136_);
if (v_isShared_5163_ == 0)
{
lean_ctor_set_tag(v___x_5162_, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5164_);
v___x_5166_ = v___x_5162_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
uint8_t v___x_5167_; lean_object* v___x_5168_; 
v___x_5167_ = lean_unbox(v_a_5150_);
lean_dec(v_a_5150_);
v___x_5168_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5160_, v___x_5166_, v___x_5167_, v_a_5152_, v___y_5114_, v___y_5115_);
return v___x_5168_;
}
}
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5173_; 
lean_dec(v_a_5156_);
lean_dec(v_a_5152_);
lean_dec(v_a_5150_);
lean_dec_ref(v_info_5136_);
v___x_5171_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 0, v___x_5171_);
v___x_5173_ = v___x_5158_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
else
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5181_; 
lean_dec(v_val_5132_);
v___x_5176_ = l_Lean_ConstantInfo_name(v_info_5136_);
lean_dec_ref(v_info_5136_);
v___x_5177_ = l_Lean_Name_getString_x21(v___x_5176_);
v___x_5178_ = lean_box(0);
v___x_5179_ = l_Lean_Name_str___override(v___x_5178_, v___x_5177_);
if (v_isShared_5135_ == 0)
{
lean_ctor_set_tag(v___x_5134_, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5176_);
v___x_5181_ = v___x_5134_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5176_);
v___x_5181_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
uint8_t v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5191_; 
v___x_5182_ = lean_unbox(v_a_5150_);
lean_dec(v_a_5150_);
v___x_5183_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5179_, v___x_5181_, v___x_5182_, v_a_5152_, v___y_5114_, v___y_5115_);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5191_ == 0)
{
lean_object* v_unused_5192_; 
v_unused_5192_ = lean_ctor_get(v___x_5183_, 0);
lean_dec(v_unused_5192_);
v___x_5185_ = v___x_5183_;
v_isShared_5186_ = v_isSharedCheck_5191_;
goto v_resetjp_5184_;
}
else
{
lean_dec(v___x_5183_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5191_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5187_; lean_object* v___x_5189_; 
v___x_5187_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 0, v___x_5187_);
v___x_5189_ = v___x_5185_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5187_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec(v_a_5150_);
lean_dec_ref(v_info_5136_);
lean_del_object(v___x_5134_);
lean_dec(v_val_5132_);
v_a_5194_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5151_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5151_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_dec_ref(v_tags_5138_);
lean_dec_ref(v_info_5136_);
lean_del_object(v___x_5134_);
lean_dec(v_val_5132_);
v_a_5202_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5149_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5149_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_dec_ref(v_tags_5138_);
lean_dec_ref(v_kind_5137_);
lean_dec_ref(v_info_5136_);
lean_del_object(v___x_5134_);
lean_dec(v_val_5132_);
v_a_5211_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5139_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5139_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5222_; 
lean_dec(v_a_5128_);
lean_dec_ref(v_decl_5113_);
lean_dec(v___x_5109_);
v___x_5220_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v___x_5220_);
v___x_5222_ = v___x_5130_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5220_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_dec_ref(v_decl_5113_);
lean_dec(v_declName_5112_);
lean_dec(v___x_5109_);
goto v___jp_5122_;
}
}
v___jp_5122_:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v___x_5123_);
return v___x_5124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5225_, lean_object* v___x_5226_, lean_object* v_id_5227_, lean_object* v_declName_5228_, lean_object* v_decl_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
uint8_t v___x_21334__boxed_5238_; lean_object* v_res_5239_; 
v___x_21334__boxed_5238_ = lean_unbox(v___x_5226_);
v_res_5239_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5225_, v___x_21334__boxed_5238_, v_id_5227_, v_declName_5228_, v_decl_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v_id_5227_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5240_, lean_object* v_id_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5240_) == 1)
{
lean_object* v_val_5250_; lean_object* v___x_5251_; 
v_val_5250_ = lean_ctor_get(v_expectedType_x3f_5240_, 0);
lean_inc(v_val_5250_);
lean_dec_ref_known(v_expectedType_x3f_5240_, 1);
v___x_5251_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5250_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5251_) == 0)
{
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5267_; 
v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5254_ = v___x_5251_;
v_isShared_5255_ = v_isSharedCheck_5267_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5251_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5267_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; uint8_t v___x_5258_; 
v___x_5256_ = lean_array_get_size(v_a_5252_);
v___x_5257_ = lean_unsigned_to_nat(0u);
v___x_5258_ = lean_nat_dec_eq(v___x_5256_, v___x_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___f_5261_; lean_object* v___x_5262_; 
lean_del_object(v___x_5254_);
v___x_5259_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5252_);
lean_dec(v_a_5252_);
v___x_5260_ = lean_box(v___x_5258_);
v___f_5261_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 13, 3);
lean_closure_set(v___f_5261_, 0, v___x_5259_);
lean_closure_set(v___f_5261_, 1, v___x_5260_);
lean_closure_set(v___f_5261_, 2, v_id_5241_);
v___x_5262_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5261_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
return v___x_5262_;
}
else
{
lean_object* v___x_5263_; lean_object* v___x_5265_; 
lean_dec(v_a_5252_);
lean_dec(v_id_5241_);
v___x_5263_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5255_ == 0)
{
lean_ctor_set(v___x_5254_, 0, v___x_5263_);
v___x_5265_ = v___x_5254_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5263_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
else
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5275_; 
lean_dec(v_id_5241_);
v_a_5268_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5270_ = v___x_5251_;
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v___x_5251_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
}
}
}
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
lean_dec(v_id_5241_);
lean_dec(v_expectedType_x3f_5240_);
v___x_5276_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5278_, lean_object* v_id_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5278_, v_id_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5289_, lean_object* v_pos_5290_, lean_object* v_completionInfoPos_5291_, lean_object* v_ctx_5292_, lean_object* v_lctx_5293_, lean_object* v_id_5294_, lean_object* v_expectedType_x3f_5295_, lean_object* v_a_5296_){
_start:
{
lean_object* v___y_5298_; lean_object* v___x_5299_; 
v___y_5298_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5298_, 0, v_expectedType_x3f_5295_);
lean_closure_set(v___y_5298_, 1, v_id_5294_);
v___x_5299_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5289_, v_pos_5290_, v_completionInfoPos_5291_, v_ctx_5292_, v_lctx_5293_, v___y_5298_, v_a_5296_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5300_, lean_object* v_pos_5301_, lean_object* v_completionInfoPos_5302_, lean_object* v_ctx_5303_, lean_object* v_lctx_5304_, lean_object* v_id_5305_, lean_object* v_expectedType_x3f_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5300_, v_pos_5301_, v_completionInfoPos_5302_, v_ctx_5303_, v_lctx_5304_, v_id_5305_, v_expectedType_x3f_5306_, v_a_5307_);
lean_dec_ref(v_a_5307_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5316_, lean_object* v_as_5317_, size_t v_sz_5318_, size_t v_i_5319_, lean_object* v_b_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v_a_5325_; uint8_t v___x_5329_; 
v___x_5329_ = lean_usize_dec_lt(v_i_5319_, v_sz_5318_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v___x_5331_; 
v___x_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5330_, 0, v_b_5320_);
v___x_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5330_);
return v___x_5331_;
}
else
{
lean_object* v___x_5332_; lean_object* v_a_5333_; 
v___x_5332_ = lean_box(0);
v_a_5333_ = lean_array_uget_borrowed(v_as_5317_, v_i_5319_);
if (lean_obj_tag(v_a_5333_) == 1)
{
lean_object* v_str_5334_; uint8_t v___x_5335_; 
v_str_5334_ = lean_ctor_get(v_a_5333_, 1);
v___x_5335_ = l_Lean_String_charactersIn(v___y_5316_, v_str_5334_);
if (v___x_5335_ == 0)
{
v_a_5325_ = v___x_5332_;
goto v___jp_5324_;
}
else
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5337_ = lean_box(0);
v___x_5338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5334_);
v___x_5339_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5339_, 0, v_str_5334_);
lean_ctor_set(v___x_5339_, 1, v___x_5336_);
lean_ctor_set(v___x_5339_, 2, v___x_5337_);
lean_ctor_set(v___x_5339_, 3, v___x_5338_);
lean_ctor_set(v___x_5339_, 4, v___x_5337_);
lean_ctor_set(v___x_5339_, 5, v___x_5337_);
lean_ctor_set(v___x_5339_, 6, v___x_5337_);
lean_ctor_set(v___x_5339_, 7, v___x_5337_);
v___x_5340_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5339_, v___x_5337_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
if (lean_obj_tag(v_a_5341_) == 0)
{
lean_dec_ref_known(v_a_5341_, 1);
return v___x_5340_;
}
else
{
lean_dec_ref_known(v_a_5341_, 1);
lean_dec_ref_known(v___x_5340_, 1);
v_a_5325_ = v___x_5332_;
goto v___jp_5324_;
}
}
else
{
return v___x_5340_;
}
}
}
else
{
v_a_5325_ = v___x_5332_;
goto v___jp_5324_;
}
}
v___jp_5324_:
{
size_t v___x_5326_; size_t v___x_5327_; 
v___x_5326_ = ((size_t)1ULL);
v___x_5327_ = lean_usize_add(v_i_5319_, v___x_5326_);
v_i_5319_ = v___x_5327_;
v_b_5320_ = v_a_5325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5342_, lean_object* v_as_5343_, lean_object* v_sz_5344_, lean_object* v_i_5345_, lean_object* v_b_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
size_t v_sz_boxed_5350_; size_t v_i_boxed_5351_; lean_object* v_res_5352_; 
v_sz_boxed_5350_ = lean_unbox_usize(v_sz_5344_);
lean_dec(v_sz_5344_);
v_i_boxed_5351_ = lean_unbox_usize(v_i_5345_);
lean_dec(v_i_5345_);
v_res_5352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5342_, v_as_5343_, v_sz_boxed_5350_, v_i_boxed_5351_, v_b_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec_ref(v_as_5343_);
lean_dec_ref(v___y_5342_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_){
_start:
{
lean_object* v___x_5363_; lean_object* v_env_5364_; uint8_t v___x_5365_; lean_object* v_fieldNames_5366_; lean_object* v___x_5367_; size_t v_sz_5368_; size_t v___x_5369_; lean_object* v___x_5370_; 
v___x_5363_ = lean_st_ref_get(v___y_5361_);
v_env_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc_ref(v_env_5364_);
lean_dec(v___x_5363_);
v___x_5365_ = 0;
v_fieldNames_5366_ = l_Lean_getStructureFieldsFlattened(v_env_5364_, v_structName_5353_, v___x_5365_);
v___x_5367_ = lean_box(0);
v_sz_5368_ = lean_array_size(v_fieldNames_5366_);
v___x_5369_ = ((size_t)0ULL);
v___x_5370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5354_, v_fieldNames_5366_, v_sz_5368_, v___x_5369_, v___x_5367_, v___y_5355_, v___y_5356_);
lean_dec_ref(v_fieldNames_5366_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v_a_5371_; 
v_a_5371_ = lean_ctor_get(v___x_5370_, 0);
lean_inc(v_a_5371_);
if (lean_obj_tag(v_a_5371_) == 0)
{
lean_dec_ref_known(v_a_5371_, 1);
return v___x_5370_;
}
else
{
lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5379_; 
lean_dec_ref_known(v_a_5371_, 1);
v_isSharedCheck_5379_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5379_ == 0)
{
lean_object* v_unused_5380_; 
v_unused_5380_ = lean_ctor_get(v___x_5370_, 0);
lean_dec(v_unused_5380_);
v___x_5373_ = v___x_5370_;
v_isShared_5374_ = v_isSharedCheck_5379_;
goto v_resetjp_5372_;
}
else
{
lean_dec(v___x_5370_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5379_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5375_; lean_object* v___x_5377_; 
v___x_5375_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 0, v___x_5375_);
v___x_5377_ = v___x_5373_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
}
}
else
{
return v___x_5370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec_ref(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec_ref(v___y_5382_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5393_, lean_object* v_pos_5394_, lean_object* v_completionInfoPos_5395_, lean_object* v_ctx_5396_, lean_object* v_lctx_5397_, lean_object* v_id_5398_, lean_object* v_structName_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v___y_5403_; 
if (lean_obj_tag(v_id_5398_) == 0)
{
lean_object* v___x_5406_; 
v___x_5406_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5403_ = v___x_5406_;
goto v___jp_5402_;
}
else
{
lean_object* v_val_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; 
v_val_5407_ = lean_ctor_get(v_id_5398_, 0);
lean_inc(v_val_5407_);
lean_dec_ref_known(v_id_5398_, 1);
v___x_5408_ = 1;
v___x_5409_ = l_Lean_Name_toString(v_val_5407_, v___x_5408_);
v___y_5403_ = v___x_5409_;
goto v___jp_5402_;
}
v___jp_5402_:
{
lean_object* v___f_5404_; lean_object* v___x_5405_; 
v___f_5404_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5404_, 0, v_structName_5399_);
lean_closure_set(v___f_5404_, 1, v___y_5403_);
v___x_5405_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5393_, v_pos_5394_, v_completionInfoPos_5395_, v_ctx_5396_, v_lctx_5397_, v___f_5404_, v_a_5400_);
return v___x_5405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5410_, lean_object* v_pos_5411_, lean_object* v_completionInfoPos_5412_, lean_object* v_ctx_5413_, lean_object* v_lctx_5414_, lean_object* v_id_5415_, lean_object* v_structName_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5410_, v_pos_5411_, v_completionInfoPos_5412_, v_ctx_5413_, v_lctx_5414_, v_id_5415_, v_structName_5416_, v_a_5417_);
lean_dec_ref(v_a_5417_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5420_, lean_object* v_as_5421_, size_t v_sz_5422_, size_t v_i_5423_, lean_object* v_b_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5420_, v_as_5421_, v_sz_5422_, v_i_5423_, v_b_5424_, v___y_5425_, v___y_5426_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5434_, lean_object* v_as_5435_, lean_object* v_sz_5436_, lean_object* v_i_5437_, lean_object* v_b_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
size_t v_sz_boxed_5447_; size_t v_i_boxed_5448_; lean_object* v_res_5449_; 
v_sz_boxed_5447_ = lean_unbox_usize(v_sz_5436_);
lean_dec(v_sz_5436_);
v_i_boxed_5448_ = lean_unbox_usize(v_i_5437_);
lean_dec(v_i_5437_);
v_res_5449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5434_, v_as_5435_, v_sz_boxed_5447_, v_i_boxed_5448_, v_b_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec_ref(v_as_5435_);
lean_dec_ref(v___y_5434_);
return v_res_5449_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0(void){
_start:
{
uint32_t v___x_5450_; lean_object* v___x_5451_; 
v___x_5450_ = 32;
v___x_5451_ = l_Char_utf8Size(v___x_5450_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5452_, lean_object* v_caps_5453_, lean_object* v_mkItem_5454_, lean_object* v_ctx_5455_, lean_object* v_stx_5456_, uint8_t v_snd_5457_, lean_object* v_x_5458_, lean_object* v_____s_5459_){
_start:
{
lean_object* v_fst_5460_; lean_object* v_snd_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5514_; 
v_fst_5460_ = lean_ctor_get(v_x_5458_, 0);
v_snd_5461_ = lean_ctor_get(v_x_5458_, 1);
v_isSharedCheck_5514_ = !lean_is_exclusive(v_x_5458_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5463_ = v_x_5458_;
v_isShared_5464_ = v_isSharedCheck_5514_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_snd_5461_);
lean_inc(v_fst_5460_);
lean_dec(v_x_5458_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5514_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___y_5466_; uint8_t v___x_5470_; lean_object* v___x_5471_; lean_object* v___y_5473_; lean_object* v___y_5474_; uint8_t v___x_5503_; 
v___x_5470_ = 1;
lean_inc(v_fst_5460_);
v___x_5471_ = l_Lean_Name_toString(v_fst_5460_, v___x_5470_);
v___x_5503_ = l_Lean_String_charactersIn(v_fst_5452_, v___x_5471_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5506_; 
lean_dec_ref(v___x_5471_);
lean_del_object(v___x_5463_);
lean_dec(v_snd_5461_);
lean_dec(v_fst_5460_);
lean_dec_ref(v_ctx_5455_);
lean_dec_ref(v_mkItem_5454_);
v___x_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5506_, 0, v_____s_5459_);
return v___x_5506_;
}
else
{
lean_object* v_textDocument_x3f_5507_; 
v_textDocument_x3f_5507_ = lean_ctor_get(v_caps_5453_, 0);
if (lean_obj_tag(v_textDocument_x3f_5507_) == 0)
{
goto v___jp_5504_;
}
else
{
lean_object* v_val_5508_; lean_object* v_completion_x3f_5509_; 
v_val_5508_ = lean_ctor_get(v_textDocument_x3f_5507_, 0);
v_completion_x3f_5509_ = lean_ctor_get(v_val_5508_, 0);
if (lean_obj_tag(v_completion_x3f_5509_) == 0)
{
goto v___jp_5504_;
}
else
{
lean_object* v_val_5510_; 
v_val_5510_ = lean_ctor_get(v_completion_x3f_5509_, 0);
if (lean_obj_tag(v_val_5510_) == 0)
{
goto v___jp_5504_;
}
else
{
lean_object* v_val_5511_; 
v_val_5511_ = lean_ctor_get(v_val_5510_, 0);
if (lean_obj_tag(v_val_5511_) == 0)
{
goto v___jp_5504_;
}
else
{
lean_object* v_val_5512_; uint8_t v___x_5513_; 
v_val_5512_ = lean_ctor_get(v_val_5511_, 0);
v___x_5513_ = lean_unbox(v_val_5512_);
if (v___x_5513_ == 0)
{
goto v___jp_5504_;
}
else
{
goto v___jp_5492_;
}
}
}
}
}
}
v___jp_5465_:
{
lean_object* v___x_5467_; lean_object* v_items_5468_; lean_object* v___x_5469_; 
v___x_5467_ = lean_apply_3(v_mkItem_5454_, v_fst_5460_, v_snd_5461_, v___y_5466_);
v_items_5468_ = lean_array_push(v_____s_5459_, v___x_5467_);
v___x_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5469_, 0, v_items_5468_);
return v___x_5469_;
}
v___jp_5472_:
{
lean_object* v_toCommandContextInfo_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5489_; 
v_toCommandContextInfo_5475_ = lean_ctor_get(v_ctx_5455_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v_ctx_5455_);
if (v_isSharedCheck_5489_ == 0)
{
lean_object* v_unused_5490_; lean_object* v_unused_5491_; 
v_unused_5490_ = lean_ctor_get(v_ctx_5455_, 2);
lean_dec(v_unused_5490_);
v_unused_5491_ = lean_ctor_get(v_ctx_5455_, 1);
lean_dec(v_unused_5491_);
v___x_5477_ = v_ctx_5455_;
v_isShared_5478_ = v_isSharedCheck_5489_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_toCommandContextInfo_5475_);
lean_dec(v_ctx_5455_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5489_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v_fileMap_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v_range_5483_; 
v_fileMap_5479_ = lean_ctor_get(v_toCommandContextInfo_5475_, 2);
lean_inc_ref_n(v_fileMap_5479_, 2);
lean_dec_ref(v_toCommandContextInfo_5475_);
v___x_5480_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5479_, v___y_5473_);
lean_dec(v___y_5473_);
v___x_5481_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5479_, v___y_5474_);
lean_dec(v___y_5474_);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 1, v___x_5481_);
lean_ctor_set(v___x_5463_, 0, v___x_5480_);
v_range_5483_ = v___x_5463_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v___x_5480_);
lean_ctor_set(v_reuseFailAlloc_5488_, 1, v___x_5481_);
v_range_5483_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5485_; 
lean_inc_ref(v_range_5483_);
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 2, v_range_5483_);
lean_ctor_set(v___x_5477_, 1, v_range_5483_);
lean_ctor_set(v___x_5477_, 0, v___x_5471_);
v___x_5485_ = v___x_5477_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v_range_5483_);
lean_ctor_set(v_reuseFailAlloc_5487_, 2, v_range_5483_);
v___x_5485_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
lean_object* v___x_5486_; 
v___x_5486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5485_);
v___y_5466_ = v___x_5486_;
goto v___jp_5465_;
}
}
}
}
v___jp_5492_:
{
uint8_t v___x_5493_; lean_object* v___x_5494_; 
v___x_5493_ = 0;
v___x_5494_ = l_Lean_Syntax_getRange_x3f(v_stx_5456_, v___x_5493_);
if (lean_obj_tag(v___x_5494_) == 1)
{
lean_object* v_val_5495_; 
v_val_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_val_5495_);
lean_dec_ref_known(v___x_5494_, 1);
if (v_snd_5457_ == 0)
{
lean_object* v_start_5496_; lean_object* v_stop_5497_; 
v_start_5496_ = lean_ctor_get(v_val_5495_, 0);
lean_inc(v_start_5496_);
v_stop_5497_ = lean_ctor_get(v_val_5495_, 1);
lean_inc(v_stop_5497_);
lean_dec(v_val_5495_);
v___y_5473_ = v_start_5496_;
v___y_5474_ = v_stop_5497_;
goto v___jp_5472_;
}
else
{
lean_object* v_start_5498_; lean_object* v_stop_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v_start_5498_ = lean_ctor_get(v_val_5495_, 0);
lean_inc(v_start_5498_);
v_stop_5499_ = lean_ctor_get(v_val_5495_, 1);
lean_inc(v_stop_5499_);
lean_dec(v_val_5495_);
v___x_5500_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5501_ = lean_nat_add(v_stop_5499_, v___x_5500_);
lean_dec(v_stop_5499_);
v___y_5473_ = v_start_5498_;
v___y_5474_ = v___x_5501_;
goto v___jp_5472_;
}
}
else
{
lean_object* v___x_5502_; 
lean_dec(v___x_5494_);
lean_dec_ref(v___x_5471_);
lean_del_object(v___x_5463_);
lean_dec_ref(v_ctx_5455_);
v___x_5502_ = lean_box(0);
v___y_5466_ = v___x_5502_;
goto v___jp_5465_;
}
}
v___jp_5504_:
{
if (v___x_5503_ == 0)
{
goto v___jp_5492_;
}
else
{
lean_object* v___x_5505_; 
lean_dec_ref(v___x_5471_);
lean_del_object(v___x_5463_);
lean_dec_ref(v_ctx_5455_);
v___x_5505_ = lean_box(0);
v___y_5466_ = v___x_5505_;
goto v___jp_5465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5515_, lean_object* v_caps_5516_, lean_object* v_mkItem_5517_, lean_object* v_ctx_5518_, lean_object* v_stx_5519_, lean_object* v_snd_5520_, lean_object* v_x_5521_, lean_object* v_____s_5522_){
_start:
{
uint8_t v_snd_1079__boxed_5523_; lean_object* v_res_5524_; 
v_snd_1079__boxed_5523_ = lean_unbox(v_snd_5520_);
v_res_5524_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5515_, v_caps_5516_, v_mkItem_5517_, v_ctx_5518_, v_stx_5519_, v_snd_1079__boxed_5523_, v_x_5521_, v_____s_5522_);
lean_dec(v_stx_5519_);
lean_dec_ref(v_caps_5516_);
lean_dec_ref(v_fst_5515_);
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5526_, lean_object* v_entries_5527_, lean_object* v_stx_5528_, lean_object* v_caps_5529_, lean_object* v_ctx_5530_, lean_object* v_mkItem_5531_){
_start:
{
lean_object* v_fst_5533_; uint8_t v_snd_5534_; uint8_t v___x_5539_; lean_object* v___x_5540_; 
v___x_5539_ = 0;
v___x_5540_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5528_, v___x_5539_, v___x_5539_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v___x_5541_; 
v___x_5541_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5533_ = v___x_5541_;
v_snd_5534_ = v___x_5539_;
goto v___jp_5532_;
}
else
{
lean_object* v_val_5542_; lean_object* v_str_5543_; lean_object* v_startPos_5544_; lean_object* v_stopPos_5545_; uint8_t v___y_5547_; uint8_t v___x_5549_; 
v_val_5542_ = lean_ctor_get(v___x_5540_, 0);
lean_inc(v_val_5542_);
lean_dec_ref_known(v___x_5540_, 1);
v_str_5543_ = lean_ctor_get(v_val_5542_, 0);
lean_inc_ref(v_str_5543_);
v_startPos_5544_ = lean_ctor_get(v_val_5542_, 1);
lean_inc(v_startPos_5544_);
v_stopPos_5545_ = lean_ctor_get(v_val_5542_, 2);
lean_inc(v_stopPos_5545_);
lean_dec(v_val_5542_);
v___x_5549_ = lean_string_utf8_at_end(v_str_5543_, v_stopPos_5545_);
if (v___x_5549_ == 0)
{
uint32_t v___x_5550_; uint32_t v___x_5551_; uint8_t v___x_5552_; 
v___x_5550_ = lean_string_utf8_get(v_str_5543_, v_stopPos_5545_);
v___x_5551_ = 46;
v___x_5552_ = lean_uint32_dec_eq(v___x_5550_, v___x_5551_);
if (v___x_5552_ == 0)
{
v___y_5547_ = v___x_5552_;
goto v___jp_5546_;
}
else
{
lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5553_ = lean_string_utf8_extract(v_str_5543_, v_startPos_5544_, v_stopPos_5545_);
lean_dec(v_stopPos_5545_);
lean_dec(v_startPos_5544_);
lean_dec_ref(v_str_5543_);
v___x_5554_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5555_ = lean_string_append(v___x_5553_, v___x_5554_);
v_fst_5533_ = v___x_5555_;
v_snd_5534_ = v___x_5552_;
goto v___jp_5532_;
}
}
else
{
v___y_5547_ = v___x_5539_;
goto v___jp_5546_;
}
v___jp_5546_:
{
lean_object* v___x_5548_; 
v___x_5548_ = lean_string_utf8_extract(v_str_5543_, v_startPos_5544_, v_stopPos_5545_);
lean_dec(v_stopPos_5545_);
lean_dec(v_startPos_5544_);
lean_dec_ref(v_str_5543_);
v_fst_5533_ = v___x_5548_;
v_snd_5534_ = v___y_5547_;
goto v___jp_5532_;
}
}
v___jp_5532_:
{
lean_object* v___x_5535_; lean_object* v___f_5536_; lean_object* v_items_5537_; lean_object* v___x_5538_; 
v___x_5535_ = lean_box(v_snd_5534_);
v___f_5536_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5536_, 0, v_fst_5533_);
lean_closure_set(v___f_5536_, 1, v_caps_5529_);
lean_closure_set(v___f_5536_, 2, v_mkItem_5531_);
lean_closure_set(v___f_5536_, 3, v_ctx_5530_);
lean_closure_set(v___f_5536_, 4, v_stx_5528_);
lean_closure_set(v___f_5536_, 5, v___x_5535_);
v_items_5537_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5538_ = lean_apply_4(v_inst_5526_, lean_box(0), v_entries_5527_, v_items_5537_, v___f_5536_);
return v___x_5538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5556_, lean_object* v_00_u03b1_5557_, lean_object* v_inst_5558_, lean_object* v_entries_5559_, lean_object* v_stx_5560_, lean_object* v_caps_5561_, lean_object* v_ctx_5562_, lean_object* v_mkItem_5563_){
_start:
{
lean_object* v___x_5564_; 
v___x_5564_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5558_, v_entries_5559_, v_stx_5560_, v_caps_5561_, v_ctx_5562_, v_mkItem_5563_);
return v___x_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v_options_5570_, lean_object* v_completionInfoPos_5571_, lean_object* v_uri_5572_, lean_object* v_pos_5573_, lean_object* v_name_5574_, lean_object* v_decl_5575_, lean_object* v_textEdit_x3f_5576_){
_start:
{
lean_object* v_defValue_5577_; lean_object* v_descr_5578_; lean_object* v_map_5579_; uint8_t v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___y_5584_; lean_object* v___x_5597_; 
v_defValue_5577_ = lean_ctor_get(v_decl_5575_, 2);
lean_inc_ref(v_defValue_5577_);
v_descr_5578_ = lean_ctor_get(v_decl_5575_, 3);
lean_inc_ref(v_descr_5578_);
lean_dec_ref(v_decl_5575_);
v_map_5579_ = lean_ctor_get(v_options_5570_, 0);
v___x_5580_ = 1;
lean_inc(v_name_5574_);
v___x_5581_ = l_Lean_Name_toString(v_name_5574_, v___x_5580_);
v___x_5582_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5597_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5579_, v_name_5574_);
lean_dec(v_name_5574_);
if (lean_obj_tag(v___x_5597_) == 0)
{
v___y_5584_ = v_defValue_5577_;
goto v___jp_5583_;
}
else
{
if (lean_obj_tag(v___x_5597_) == 0)
{
v___y_5584_ = v_defValue_5577_;
goto v___jp_5583_;
}
else
{
lean_object* v_val_5598_; 
lean_dec_ref(v_defValue_5577_);
v_val_5598_ = lean_ctor_get(v___x_5597_, 0);
lean_inc(v_val_5598_);
lean_dec_ref_known(v___x_5597_, 1);
v___y_5584_ = v_val_5598_;
goto v___jp_5583_;
}
}
v___jp_5583_:
{
lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; 
v___x_5585_ = lean_data_value_to_string(v___y_5584_);
v___x_5586_ = lean_string_append(v___x_5582_, v___x_5585_);
lean_dec_ref(v___x_5585_);
v___x_5587_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5588_ = lean_string_append(v___x_5586_, v___x_5587_);
v___x_5589_ = lean_string_append(v___x_5588_, v_descr_5578_);
lean_dec_ref(v_descr_5578_);
v___x_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5590_, 0, v___x_5589_);
v___x_5591_ = lean_box(0);
v___x_5592_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5593_, 0, v_completionInfoPos_5571_);
v___x_5594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5594_, 0, v_uri_5572_);
lean_ctor_set(v___x_5594_, 1, v_pos_5573_);
lean_ctor_set(v___x_5594_, 2, v___x_5593_);
lean_ctor_set(v___x_5594_, 3, v___x_5591_);
v___x_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5594_);
v___x_5596_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5596_, 0, v___x_5581_);
lean_ctor_set(v___x_5596_, 1, v___x_5590_);
lean_ctor_set(v___x_5596_, 2, v___x_5591_);
lean_ctor_set(v___x_5596_, 3, v___x_5592_);
lean_ctor_set(v___x_5596_, 4, v_textEdit_x3f_5576_);
lean_ctor_set(v___x_5596_, 5, v___x_5591_);
lean_ctor_set(v___x_5596_, 6, v___x_5595_);
lean_ctor_set(v___x_5596_, 7, v___x_5591_);
return v___x_5596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v_options_5599_, lean_object* v_completionInfoPos_5600_, lean_object* v_uri_5601_, lean_object* v_pos_5602_, lean_object* v_name_5603_, lean_object* v_decl_5604_, lean_object* v_textEdit_x3f_5605_){
_start:
{
lean_object* v_res_5606_; 
v_res_5606_ = l_Lean_Server_Completion_optionCompletion___lam__0(v_options_5599_, v_completionInfoPos_5600_, v_uri_5601_, v_pos_5602_, v_name_5603_, v_decl_5604_, v_textEdit_x3f_5605_);
lean_dec_ref(v_options_5599_);
return v_res_5606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5607_, lean_object* v_stx_5608_, lean_object* v_ctx_5609_, uint8_t v_snd_5610_, lean_object* v_fst_5611_, lean_object* v_caps_5612_, lean_object* v_init_5613_, lean_object* v_x_5614_){
_start:
{
if (lean_obj_tag(v_x_5614_) == 0)
{
lean_object* v_k_5615_; lean_object* v_v_5616_; lean_object* v_l_5617_; lean_object* v_r_5618_; lean_object* v___x_5619_; lean_object* v_a_5620_; lean_object* v___y_5622_; uint8_t v___x_5626_; lean_object* v___x_5627_; lean_object* v___y_5629_; lean_object* v___y_5630_; uint8_t v___x_5649_; 
v_k_5615_ = lean_ctor_get(v_x_5614_, 1);
lean_inc_n(v_k_5615_, 2);
v_v_5616_ = lean_ctor_get(v_x_5614_, 2);
lean_inc(v_v_5616_);
v_l_5617_ = lean_ctor_get(v_x_5614_, 3);
lean_inc(v_l_5617_);
v_r_5618_ = lean_ctor_get(v_x_5614_, 4);
lean_inc(v_r_5618_);
lean_dec_ref_known(v_x_5614_, 5);
lean_inc_ref(v_ctx_5609_);
lean_inc_ref(v_mkItem_5607_);
v___x_5619_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5607_, v_stx_5608_, v_ctx_5609_, v_snd_5610_, v_fst_5611_, v_caps_5612_, v_init_5613_, v_l_5617_);
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_a_5620_);
v___x_5626_ = 1;
v___x_5627_ = l_Lean_Name_toString(v_k_5615_, v___x_5626_);
v___x_5649_ = l_Lean_String_charactersIn(v_fst_5611_, v___x_5627_);
if (v___x_5649_ == 0)
{
lean_object* v_a_5652_; 
lean_dec_ref(v___x_5627_);
lean_dec(v_a_5620_);
lean_dec(v_v_5616_);
lean_dec(v_k_5615_);
v_a_5652_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_a_5652_);
lean_dec_ref(v___x_5619_);
v_init_5613_ = v_a_5652_;
v_x_5614_ = v_r_5618_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5654_; 
lean_dec_ref(v___x_5619_);
v_textDocument_x3f_5654_ = lean_ctor_get(v_caps_5612_, 0);
if (lean_obj_tag(v_textDocument_x3f_5654_) == 0)
{
goto v___jp_5650_;
}
else
{
lean_object* v_val_5655_; lean_object* v_completion_x3f_5656_; 
v_val_5655_ = lean_ctor_get(v_textDocument_x3f_5654_, 0);
v_completion_x3f_5656_ = lean_ctor_get(v_val_5655_, 0);
if (lean_obj_tag(v_completion_x3f_5656_) == 0)
{
goto v___jp_5650_;
}
else
{
lean_object* v_val_5657_; 
v_val_5657_ = lean_ctor_get(v_completion_x3f_5656_, 0);
if (lean_obj_tag(v_val_5657_) == 0)
{
goto v___jp_5650_;
}
else
{
lean_object* v_val_5658_; 
v_val_5658_ = lean_ctor_get(v_val_5657_, 0);
if (lean_obj_tag(v_val_5658_) == 0)
{
goto v___jp_5650_;
}
else
{
lean_object* v_val_5659_; uint8_t v___x_5660_; 
v_val_5659_ = lean_ctor_get(v_val_5658_, 0);
v___x_5660_ = lean_unbox(v_val_5659_);
if (v___x_5660_ == 0)
{
goto v___jp_5650_;
}
else
{
goto v___jp_5638_;
}
}
}
}
}
}
v___jp_5621_:
{
lean_object* v___x_5623_; lean_object* v_items_5624_; 
lean_inc_ref(v_mkItem_5607_);
v___x_5623_ = lean_apply_3(v_mkItem_5607_, v_k_5615_, v_v_5616_, v___y_5622_);
v_items_5624_ = lean_array_push(v_a_5620_, v___x_5623_);
v_init_5613_ = v_items_5624_;
v_x_5614_ = v_r_5618_;
goto _start;
}
v___jp_5628_:
{
lean_object* v_toCommandContextInfo_5631_; lean_object* v_fileMap_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v_range_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v_toCommandContextInfo_5631_ = lean_ctor_get(v_ctx_5609_, 0);
v_fileMap_5632_ = lean_ctor_get(v_toCommandContextInfo_5631_, 2);
lean_inc_ref_n(v_fileMap_5632_, 2);
v___x_5633_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5632_, v___y_5629_);
lean_dec(v___y_5629_);
v___x_5634_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5632_, v___y_5630_);
lean_dec(v___y_5630_);
v_range_5635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5635_, 0, v___x_5633_);
lean_ctor_set(v_range_5635_, 1, v___x_5634_);
lean_inc_ref(v_range_5635_);
v___x_5636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5627_);
lean_ctor_set(v___x_5636_, 1, v_range_5635_);
lean_ctor_set(v___x_5636_, 2, v_range_5635_);
v___x_5637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
v___y_5622_ = v___x_5637_;
goto v___jp_5621_;
}
v___jp_5638_:
{
uint8_t v___x_5639_; lean_object* v___x_5640_; 
v___x_5639_ = 0;
v___x_5640_ = l_Lean_Syntax_getRange_x3f(v_stx_5608_, v___x_5639_);
if (lean_obj_tag(v___x_5640_) == 1)
{
lean_object* v_val_5641_; 
v_val_5641_ = lean_ctor_get(v___x_5640_, 0);
lean_inc(v_val_5641_);
lean_dec_ref_known(v___x_5640_, 1);
if (v_snd_5610_ == 0)
{
lean_object* v_start_5642_; lean_object* v_stop_5643_; 
v_start_5642_ = lean_ctor_get(v_val_5641_, 0);
lean_inc(v_start_5642_);
v_stop_5643_ = lean_ctor_get(v_val_5641_, 1);
lean_inc(v_stop_5643_);
lean_dec(v_val_5641_);
v___y_5629_ = v_start_5642_;
v___y_5630_ = v_stop_5643_;
goto v___jp_5628_;
}
else
{
lean_object* v_start_5644_; lean_object* v_stop_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; 
v_start_5644_ = lean_ctor_get(v_val_5641_, 0);
lean_inc(v_start_5644_);
v_stop_5645_ = lean_ctor_get(v_val_5641_, 1);
lean_inc(v_stop_5645_);
lean_dec(v_val_5641_);
v___x_5646_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5647_ = lean_nat_add(v_stop_5645_, v___x_5646_);
lean_dec(v_stop_5645_);
v___y_5629_ = v_start_5644_;
v___y_5630_ = v___x_5647_;
goto v___jp_5628_;
}
}
else
{
lean_object* v___x_5648_; 
lean_dec(v___x_5640_);
lean_dec_ref(v___x_5627_);
v___x_5648_ = lean_box(0);
v___y_5622_ = v___x_5648_;
goto v___jp_5621_;
}
}
v___jp_5650_:
{
if (v___x_5649_ == 0)
{
goto v___jp_5638_;
}
else
{
lean_object* v___x_5651_; 
lean_dec_ref(v___x_5627_);
v___x_5651_ = lean_box(0);
v___y_5622_ = v___x_5651_;
goto v___jp_5621_;
}
}
}
else
{
lean_object* v___x_5661_; 
lean_dec_ref(v_ctx_5609_);
lean_dec_ref(v_mkItem_5607_);
v___x_5661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5661_, 0, v_init_5613_);
return v___x_5661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5662_, lean_object* v_stx_5663_, lean_object* v_ctx_5664_, lean_object* v_snd_5665_, lean_object* v_fst_5666_, lean_object* v_caps_5667_, lean_object* v_init_5668_, lean_object* v_x_5669_){
_start:
{
uint8_t v_snd_1415__boxed_5670_; lean_object* v_res_5671_; 
v_snd_1415__boxed_5670_ = lean_unbox(v_snd_5665_);
v_res_5671_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5662_, v_stx_5663_, v_ctx_5664_, v_snd_1415__boxed_5670_, v_fst_5666_, v_caps_5667_, v_init_5668_, v_x_5669_);
lean_dec_ref(v_caps_5667_);
lean_dec_ref(v_fst_5666_);
lean_dec(v_stx_5663_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5672_, lean_object* v_stx_5673_, lean_object* v_caps_5674_, lean_object* v_ctx_5675_, lean_object* v_mkItem_5676_){
_start:
{
lean_object* v_fst_5678_; uint8_t v_snd_5679_; uint8_t v___x_5683_; lean_object* v___x_5684_; 
v___x_5683_ = 0;
v___x_5684_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5673_, v___x_5683_, v___x_5683_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v___x_5685_; 
v___x_5685_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5678_ = v___x_5685_;
v_snd_5679_ = v___x_5683_;
goto v___jp_5677_;
}
else
{
lean_object* v_val_5686_; lean_object* v_str_5687_; lean_object* v_startPos_5688_; lean_object* v_stopPos_5689_; uint8_t v___y_5691_; uint8_t v___x_5693_; 
v_val_5686_ = lean_ctor_get(v___x_5684_, 0);
lean_inc(v_val_5686_);
lean_dec_ref_known(v___x_5684_, 1);
v_str_5687_ = lean_ctor_get(v_val_5686_, 0);
lean_inc_ref(v_str_5687_);
v_startPos_5688_ = lean_ctor_get(v_val_5686_, 1);
lean_inc(v_startPos_5688_);
v_stopPos_5689_ = lean_ctor_get(v_val_5686_, 2);
lean_inc(v_stopPos_5689_);
lean_dec(v_val_5686_);
v___x_5693_ = lean_string_utf8_at_end(v_str_5687_, v_stopPos_5689_);
if (v___x_5693_ == 0)
{
uint32_t v___x_5694_; uint32_t v___x_5695_; uint8_t v___x_5696_; 
v___x_5694_ = lean_string_utf8_get(v_str_5687_, v_stopPos_5689_);
v___x_5695_ = 46;
v___x_5696_ = lean_uint32_dec_eq(v___x_5694_, v___x_5695_);
if (v___x_5696_ == 0)
{
v___y_5691_ = v___x_5696_;
goto v___jp_5690_;
}
else
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5697_ = lean_string_utf8_extract(v_str_5687_, v_startPos_5688_, v_stopPos_5689_);
lean_dec(v_stopPos_5689_);
lean_dec(v_startPos_5688_);
lean_dec_ref(v_str_5687_);
v___x_5698_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5699_ = lean_string_append(v___x_5697_, v___x_5698_);
v_fst_5678_ = v___x_5699_;
v_snd_5679_ = v___x_5696_;
goto v___jp_5677_;
}
}
else
{
v___y_5691_ = v___x_5683_;
goto v___jp_5690_;
}
v___jp_5690_:
{
lean_object* v___x_5692_; 
v___x_5692_ = lean_string_utf8_extract(v_str_5687_, v_startPos_5688_, v_stopPos_5689_);
lean_dec(v_stopPos_5689_);
lean_dec(v_startPos_5688_);
lean_dec_ref(v_str_5687_);
v_fst_5678_ = v___x_5692_;
v_snd_5679_ = v___y_5691_;
goto v___jp_5677_;
}
}
v___jp_5677_:
{
lean_object* v_items_5680_; lean_object* v___x_5681_; lean_object* v_a_5682_; 
v_items_5680_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5681_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5676_, v_stx_5673_, v_ctx_5675_, v_snd_5679_, v_fst_5678_, v_caps_5674_, v_items_5680_, v_entries_5672_);
lean_dec_ref(v_fst_5678_);
v_a_5682_ = lean_ctor_get(v___x_5681_, 0);
lean_inc(v_a_5682_);
lean_dec_ref(v___x_5681_);
return v_a_5682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object* v_entries_5700_, lean_object* v_stx_5701_, lean_object* v_caps_5702_, lean_object* v_ctx_5703_, lean_object* v_mkItem_5704_){
_start:
{
lean_object* v_res_5705_; 
v_res_5705_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_entries_5700_, v_stx_5701_, v_caps_5702_, v_ctx_5703_, v_mkItem_5704_);
lean_dec_ref(v_caps_5702_);
lean_dec(v_stx_5701_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object* v_completionInfoPos_5706_, lean_object* v_uri_5707_, lean_object* v_pos_5708_, lean_object* v_stx_5709_, lean_object* v_caps_5710_, lean_object* v_ctx_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_5717_) == 0)
{
lean_object* v_a_5718_; lean_object* v___x_5720_; uint8_t v_isShared_5721_; uint8_t v_isSharedCheck_5730_; 
v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5720_ = v___x_5717_;
v_isShared_5721_ = v_isSharedCheck_5730_;
goto v_resetjp_5719_;
}
else
{
lean_inc(v_a_5718_);
lean_dec(v___x_5717_);
v___x_5720_ = lean_box(0);
v_isShared_5721_ = v_isSharedCheck_5730_;
goto v_resetjp_5719_;
}
v_resetjp_5719_:
{
lean_object* v_options_5722_; lean_object* v___f_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5728_; 
v_options_5722_ = lean_ctor_get(v___y_5714_, 2);
lean_inc_ref(v_options_5722_);
lean_dec_ref(v___y_5714_);
v___f_5723_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5723_, 0, v_options_5722_);
lean_closure_set(v___f_5723_, 1, v_completionInfoPos_5706_);
lean_closure_set(v___f_5723_, 2, v_uri_5707_);
lean_closure_set(v___f_5723_, 3, v_pos_5708_);
v___x_5724_ = lean_unsigned_to_nat(1u);
v___x_5725_ = l_Lean_Syntax_getArg(v_stx_5709_, v___x_5724_);
v___x_5726_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_a_5718_, v___x_5725_, v_caps_5710_, v_ctx_5711_, v___f_5723_);
lean_dec(v___x_5725_);
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 0, v___x_5726_);
v___x_5728_ = v___x_5720_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v___x_5726_);
v___x_5728_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
return v___x_5728_;
}
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5743_; 
lean_dec_ref(v_ctx_5711_);
lean_dec_ref(v_pos_5708_);
lean_dec_ref(v_uri_5707_);
lean_dec(v_completionInfoPos_5706_);
v_a_5731_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5743_ == 0)
{
v___x_5733_ = v___x_5717_;
v_isShared_5734_ = v_isSharedCheck_5743_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5717_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5743_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v_ref_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5741_; 
v_ref_5735_ = lean_ctor_get(v___y_5714_, 5);
lean_inc(v_ref_5735_);
lean_dec_ref(v___y_5714_);
v___x_5736_ = lean_io_error_to_string(v_a_5731_);
v___x_5737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
v___x_5738_ = l_Lean_MessageData_ofFormat(v___x_5737_);
v___x_5739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5739_, 0, v_ref_5735_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
if (v_isShared_5734_ == 0)
{
lean_ctor_set(v___x_5733_, 0, v___x_5739_);
v___x_5741_ = v___x_5733_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v___x_5739_);
v___x_5741_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
return v___x_5741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object* v_completionInfoPos_5744_, lean_object* v_uri_5745_, lean_object* v_pos_5746_, lean_object* v_stx_5747_, lean_object* v_caps_5748_, lean_object* v_ctx_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5744_, v_uri_5745_, v_pos_5746_, v_stx_5747_, v_caps_5748_, v_ctx_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
lean_dec(v___y_5753_);
lean_dec(v___y_5751_);
lean_dec_ref(v___y_5750_);
lean_dec_ref(v_caps_5748_);
lean_dec(v_stx_5747_);
return v_res_5755_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__0(void){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5756_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1(void){
_start:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5757_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__0, &l_Lean_Server_Completion_optionCompletion___closed__0_once, _init_l_Lean_Server_Completion_optionCompletion___closed__0);
v___x_5758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
return v___x_5758_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2(void){
_start:
{
lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; 
v___x_5759_ = lean_unsigned_to_nat(32u);
v___x_5760_ = lean_mk_empty_array_with_capacity(v___x_5759_);
v___x_5761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5760_);
return v___x_5761_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3(void){
_start:
{
size_t v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; 
v___x_5762_ = ((size_t)5ULL);
v___x_5763_ = lean_unsigned_to_nat(0u);
v___x_5764_ = lean_unsigned_to_nat(32u);
v___x_5765_ = lean_mk_empty_array_with_capacity(v___x_5764_);
v___x_5766_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__2, &l_Lean_Server_Completion_optionCompletion___closed__2_once, _init_l_Lean_Server_Completion_optionCompletion___closed__2);
v___x_5767_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set(v___x_5767_, 1, v___x_5765_);
lean_ctor_set(v___x_5767_, 2, v___x_5763_);
lean_ctor_set(v___x_5767_, 3, v___x_5763_);
lean_ctor_set_usize(v___x_5767_, 4, v___x_5762_);
return v___x_5767_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4(void){
_start:
{
lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; 
v___x_5768_ = lean_box(1);
v___x_5769_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__3, &l_Lean_Server_Completion_optionCompletion___closed__3_once, _init_l_Lean_Server_Completion_optionCompletion___closed__3);
v___x_5770_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__1, &l_Lean_Server_Completion_optionCompletion___closed__1_once, _init_l_Lean_Server_Completion_optionCompletion___closed__1);
v___x_5771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5771_, 0, v___x_5770_);
lean_ctor_set(v___x_5771_, 1, v___x_5769_);
lean_ctor_set(v___x_5771_, 2, v___x_5768_);
return v___x_5771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* v_uri_5772_, lean_object* v_pos_5773_, lean_object* v_completionInfoPos_5774_, lean_object* v_ctx_5775_, lean_object* v_stx_5776_, lean_object* v_caps_5777_){
_start:
{
lean_object* v___f_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; 
lean_inc_ref(v_ctx_5775_);
v___f_5779_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__1___boxed), 11, 6);
lean_closure_set(v___f_5779_, 0, v_completionInfoPos_5774_);
lean_closure_set(v___f_5779_, 1, v_uri_5772_);
lean_closure_set(v___f_5779_, 2, v_pos_5773_);
lean_closure_set(v___f_5779_, 3, v_stx_5776_);
lean_closure_set(v___f_5779_, 4, v_caps_5777_);
lean_closure_set(v___f_5779_, 5, v_ctx_5775_);
v___x_5780_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5781_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5775_, v___x_5780_, v___f_5779_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* v_uri_5782_, lean_object* v_pos_5783_, lean_object* v_completionInfoPos_5784_, lean_object* v_ctx_5785_, lean_object* v_stx_5786_, lean_object* v_caps_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l_Lean_Server_Completion_optionCompletion(v_uri_5782_, v_pos_5783_, v_completionInfoPos_5784_, v_ctx_5785_, v_stx_5786_, v_caps_5787_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object* v_completionInfoPos_5799_, lean_object* v_uri_5800_, lean_object* v_pos_5801_, lean_object* v_name_5802_, lean_object* v_explan_5803_, lean_object* v_textEdit_x3f_5804_){
_start:
{
lean_object* v_metadata_5805_; lean_object* v_removedVersion_x3f_5806_; uint8_t v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; uint8_t v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
v_metadata_5805_ = lean_ctor_get(v_explan_5803_, 1);
v_removedVersion_x3f_5806_ = lean_ctor_get(v_metadata_5805_, 2);
v___x_5807_ = 1;
v___x_5808_ = l_Lean_Name_toString(v_name_5802_, v___x_5807_);
v___x_5809_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1));
v___x_5810_ = 1;
v___x_5811_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_5803_);
v___x_5812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5812_, 0, v___x_5811_);
lean_ctor_set_uint8(v___x_5812_, sizeof(void*)*1, v___x_5810_);
v___x_5813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5813_, 0, v___x_5812_);
v___x_5814_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5815_ = lean_box(0);
v___x_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5816_, 0, v_completionInfoPos_5799_);
v___x_5817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5817_, 0, v_uri_5800_);
lean_ctor_set(v___x_5817_, 1, v_pos_5801_);
lean_ctor_set(v___x_5817_, 2, v___x_5816_);
lean_ctor_set(v___x_5817_, 3, v___x_5815_);
v___x_5818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5817_);
if (lean_obj_tag(v_removedVersion_x3f_5806_) == 0)
{
lean_object* v___x_5819_; 
v___x_5819_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5819_, 0, v___x_5808_);
lean_ctor_set(v___x_5819_, 1, v___x_5809_);
lean_ctor_set(v___x_5819_, 2, v___x_5813_);
lean_ctor_set(v___x_5819_, 3, v___x_5814_);
lean_ctor_set(v___x_5819_, 4, v_textEdit_x3f_5804_);
lean_ctor_set(v___x_5819_, 5, v___x_5815_);
lean_ctor_set(v___x_5819_, 6, v___x_5818_);
lean_ctor_set(v___x_5819_, 7, v___x_5815_);
return v___x_5819_;
}
else
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3));
v___x_5821_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5808_);
lean_ctor_set(v___x_5821_, 1, v___x_5809_);
lean_ctor_set(v___x_5821_, 2, v___x_5813_);
lean_ctor_set(v___x_5821_, 3, v___x_5814_);
lean_ctor_set(v___x_5821_, 4, v_textEdit_x3f_5804_);
lean_ctor_set(v___x_5821_, 5, v___x_5815_);
lean_ctor_set(v___x_5821_, 6, v___x_5818_);
lean_ctor_set(v___x_5821_, 7, v___x_5820_);
return v___x_5821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object* v_completionInfoPos_5822_, lean_object* v_uri_5823_, lean_object* v_pos_5824_, lean_object* v_name_5825_, lean_object* v_explan_5826_, lean_object* v_textEdit_x3f_5827_){
_start:
{
lean_object* v_res_5828_; 
v_res_5828_ = l_Lean_Server_Completion_errorNameCompletion___lam__0(v_completionInfoPos_5822_, v_uri_5823_, v_pos_5824_, v_name_5825_, v_explan_5826_, v_textEdit_x3f_5827_);
lean_dec_ref(v_explan_5826_);
return v_res_5828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object* v_init_5829_, lean_object* v_x_5830_){
_start:
{
if (lean_obj_tag(v_x_5830_) == 0)
{
lean_object* v_k_5831_; lean_object* v_v_5832_; lean_object* v_l_5833_; lean_object* v_r_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
v_k_5831_ = lean_ctor_get(v_x_5830_, 1);
v_v_5832_ = lean_ctor_get(v_x_5830_, 2);
v_l_5833_ = lean_ctor_get(v_x_5830_, 3);
v_r_5834_ = lean_ctor_get(v_x_5830_, 4);
v___x_5835_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5829_, v_l_5833_);
lean_inc(v_v_5832_);
lean_inc(v_k_5831_);
v___x_5836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5836_, 0, v_k_5831_);
lean_ctor_set(v___x_5836_, 1, v_v_5832_);
v___x_5837_ = lean_array_push(v___x_5835_, v___x_5836_);
v_init_5829_ = v___x_5837_;
v_x_5830_ = v_r_5834_;
goto _start;
}
else
{
return v_init_5829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5839_, lean_object* v_x_5840_){
_start:
{
lean_object* v_res_5841_; 
v_res_5841_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5839_, v_x_5840_);
lean_dec(v_x_5840_);
return v_res_5841_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_5842_, lean_object* v_e_5843_, lean_object* v_e_x27_5844_){
_start:
{
lean_object* v_fst_5845_; lean_object* v_fst_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; uint8_t v___x_5849_; 
v_fst_5845_ = lean_ctor_get(v_e_5843_, 0);
lean_inc(v_fst_5845_);
lean_dec_ref(v_e_5843_);
v_fst_5846_ = lean_ctor_get(v_e_x27_5844_, 0);
lean_inc(v_fst_5846_);
lean_dec_ref(v_e_x27_5844_);
v___x_5847_ = l_Lean_Name_toString(v_fst_5845_, v___x_5842_);
v___x_5848_ = l_Lean_Name_toString(v_fst_5846_, v___x_5842_);
v___x_5849_ = lean_string_dec_lt(v___x_5847_, v___x_5848_);
lean_dec_ref(v___x_5848_);
lean_dec_ref(v___x_5847_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_5850_, lean_object* v_e_5851_, lean_object* v_e_x27_5852_){
_start:
{
uint8_t v___x_1569__boxed_5853_; uint8_t v_res_5854_; lean_object* v_r_5855_; 
v___x_1569__boxed_5853_ = lean_unbox(v___x_5850_);
v_res_5854_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1569__boxed_5853_, v_e_5851_, v_e_x27_5852_);
v_r_5855_ = lean_box(v_res_5854_);
return v_r_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object* v_hi_5856_, lean_object* v_pivot_5857_, lean_object* v_as_5858_, lean_object* v_i_5859_, lean_object* v_k_5860_){
_start:
{
uint8_t v___x_5861_; 
v___x_5861_ = lean_nat_dec_lt(v_k_5860_, v_hi_5856_);
if (v___x_5861_ == 0)
{
lean_object* v___x_5862_; lean_object* v___x_5863_; 
lean_dec(v_k_5860_);
lean_dec_ref(v_pivot_5857_);
v___x_5862_ = lean_array_fswap(v_as_5858_, v_i_5859_, v_hi_5856_);
v___x_5863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5863_, 0, v_i_5859_);
lean_ctor_set(v___x_5863_, 1, v___x_5862_);
return v___x_5863_;
}
else
{
lean_object* v___x_5864_; lean_object* v_fst_5865_; lean_object* v_fst_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; uint8_t v___x_5869_; 
v___x_5864_ = lean_array_fget_borrowed(v_as_5858_, v_k_5860_);
v_fst_5865_ = lean_ctor_get(v___x_5864_, 0);
v_fst_5866_ = lean_ctor_get(v_pivot_5857_, 0);
lean_inc(v_fst_5865_);
v___x_5867_ = l_Lean_Name_toString(v_fst_5865_, v___x_5861_);
lean_inc(v_fst_5866_);
v___x_5868_ = l_Lean_Name_toString(v_fst_5866_, v___x_5861_);
v___x_5869_ = lean_string_dec_lt(v___x_5867_, v___x_5868_);
lean_dec_ref(v___x_5868_);
lean_dec_ref(v___x_5867_);
if (v___x_5869_ == 0)
{
lean_object* v___x_5870_; lean_object* v___x_5871_; 
v___x_5870_ = lean_unsigned_to_nat(1u);
v___x_5871_ = lean_nat_add(v_k_5860_, v___x_5870_);
lean_dec(v_k_5860_);
v_k_5860_ = v___x_5871_;
goto _start;
}
else
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___x_5873_ = lean_array_fswap(v_as_5858_, v_i_5859_, v_k_5860_);
v___x_5874_ = lean_unsigned_to_nat(1u);
v___x_5875_ = lean_nat_add(v_i_5859_, v___x_5874_);
lean_dec(v_i_5859_);
v___x_5876_ = lean_nat_add(v_k_5860_, v___x_5874_);
lean_dec(v_k_5860_);
v_as_5858_ = v___x_5873_;
v_i_5859_ = v___x_5875_;
v_k_5860_ = v___x_5876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_hi_5878_, lean_object* v_pivot_5879_, lean_object* v_as_5880_, lean_object* v_i_5881_, lean_object* v_k_5882_){
_start:
{
lean_object* v_res_5883_; 
v_res_5883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5878_, v_pivot_5879_, v_as_5880_, v_i_5881_, v_k_5882_);
lean_dec(v_hi_5878_);
return v_res_5883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_n_5884_, lean_object* v_as_5885_, lean_object* v_lo_5886_, lean_object* v_hi_5887_){
_start:
{
lean_object* v___y_5889_; uint8_t v___x_5899_; 
v___x_5899_ = lean_nat_dec_lt(v_lo_5886_, v_hi_5887_);
if (v___x_5899_ == 0)
{
lean_dec(v_lo_5886_);
return v_as_5885_;
}
else
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v_mid_5902_; lean_object* v___y_5904_; lean_object* v___y_5910_; lean_object* v___x_5915_; lean_object* v___x_5916_; uint8_t v___x_5917_; 
v___x_5900_ = lean_nat_add(v_lo_5886_, v_hi_5887_);
v___x_5901_ = lean_unsigned_to_nat(1u);
v_mid_5902_ = lean_nat_shiftr(v___x_5900_, v___x_5901_);
lean_dec(v___x_5900_);
v___x_5915_ = lean_array_fget_borrowed(v_as_5885_, v_mid_5902_);
v___x_5916_ = lean_array_fget_borrowed(v_as_5885_, v_lo_5886_);
lean_inc(v___x_5916_);
lean_inc(v___x_5915_);
v___x_5917_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5899_, v___x_5915_, v___x_5916_);
if (v___x_5917_ == 0)
{
v___y_5910_ = v_as_5885_;
goto v___jp_5909_;
}
else
{
lean_object* v___x_5918_; 
v___x_5918_ = lean_array_fswap(v_as_5885_, v_lo_5886_, v_mid_5902_);
v___y_5910_ = v___x_5918_;
goto v___jp_5909_;
}
v___jp_5903_:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; 
v___x_5905_ = lean_array_fget_borrowed(v___y_5904_, v_mid_5902_);
v___x_5906_ = lean_array_fget_borrowed(v___y_5904_, v_hi_5887_);
lean_inc(v___x_5906_);
lean_inc(v___x_5905_);
v___x_5907_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5899_, v___x_5905_, v___x_5906_);
if (v___x_5907_ == 0)
{
lean_dec(v_mid_5902_);
v___y_5889_ = v___y_5904_;
goto v___jp_5888_;
}
else
{
lean_object* v___x_5908_; 
v___x_5908_ = lean_array_fswap(v___y_5904_, v_mid_5902_, v_hi_5887_);
lean_dec(v_mid_5902_);
v___y_5889_ = v___x_5908_;
goto v___jp_5888_;
}
}
v___jp_5909_:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; uint8_t v___x_5913_; 
v___x_5911_ = lean_array_fget_borrowed(v___y_5910_, v_hi_5887_);
v___x_5912_ = lean_array_fget_borrowed(v___y_5910_, v_lo_5886_);
lean_inc(v___x_5912_);
lean_inc(v___x_5911_);
v___x_5913_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5899_, v___x_5911_, v___x_5912_);
if (v___x_5913_ == 0)
{
v___y_5904_ = v___y_5910_;
goto v___jp_5903_;
}
else
{
lean_object* v___x_5914_; 
v___x_5914_ = lean_array_fswap(v___y_5910_, v_lo_5886_, v_hi_5887_);
v___y_5904_ = v___x_5914_;
goto v___jp_5903_;
}
}
}
v___jp_5888_:
{
lean_object* v_pivot_5890_; lean_object* v___x_5891_; lean_object* v_fst_5892_; lean_object* v_snd_5893_; uint8_t v___x_5894_; 
v_pivot_5890_ = lean_array_fget(v___y_5889_, v_hi_5887_);
lean_inc_n(v_lo_5886_, 2);
v___x_5891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5887_, v_pivot_5890_, v___y_5889_, v_lo_5886_, v_lo_5886_);
v_fst_5892_ = lean_ctor_get(v___x_5891_, 0);
lean_inc(v_fst_5892_);
v_snd_5893_ = lean_ctor_get(v___x_5891_, 1);
lean_inc(v_snd_5893_);
lean_dec_ref(v___x_5891_);
v___x_5894_ = lean_nat_dec_le(v_hi_5887_, v_fst_5892_);
if (v___x_5894_ == 0)
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5884_, v_snd_5893_, v_lo_5886_, v_fst_5892_);
v___x_5896_ = lean_unsigned_to_nat(1u);
v___x_5897_ = lean_nat_add(v_fst_5892_, v___x_5896_);
lean_dec(v_fst_5892_);
v_as_5885_ = v___x_5895_;
v_lo_5886_ = v___x_5897_;
goto _start;
}
else
{
lean_dec(v_fst_5892_);
lean_dec(v_lo_5886_);
return v_snd_5893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_n_5919_, lean_object* v_as_5920_, lean_object* v_lo_5921_, lean_object* v_hi_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5919_, v_as_5920_, v_lo_5921_, v_hi_5922_);
lean_dec(v_hi_5922_);
lean_dec(v_n_5919_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_5926_){
_start:
{
lean_object* v___x_5928_; lean_object* v_env_5929_; lean_object* v___x_5930_; lean_object* v_toEnvExtension_5931_; lean_object* v_asyncMode_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___y_5941_; lean_object* v___y_5942_; uint8_t v___x_5945_; 
v___x_5928_ = lean_st_ref_get(v___y_5926_);
v_env_5929_ = lean_ctor_get(v___x_5928_, 0);
lean_inc_ref(v_env_5929_);
lean_dec(v___x_5928_);
v___x_5930_ = l_Lean_errorExplanationExt;
v_toEnvExtension_5931_ = lean_ctor_get(v___x_5930_, 0);
v_asyncMode_5932_ = lean_ctor_get(v_toEnvExtension_5931_, 2);
v___x_5933_ = lean_box(1);
v___x_5934_ = lean_box(0);
v___x_5935_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5933_, v___x_5930_, v_env_5929_, v_asyncMode_5932_, v___x_5934_);
v___x_5936_ = lean_unsigned_to_nat(0u);
v___x_5937_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_5938_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_5937_, v___x_5935_);
lean_dec(v___x_5935_);
v___x_5939_ = lean_array_get_size(v___x_5938_);
v___x_5945_ = lean_nat_dec_eq(v___x_5939_, v___x_5936_);
if (v___x_5945_ == 0)
{
lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___y_5949_; uint8_t v___x_5951_; 
v___x_5946_ = lean_unsigned_to_nat(1u);
v___x_5947_ = lean_nat_sub(v___x_5939_, v___x_5946_);
v___x_5951_ = lean_nat_dec_le(v___x_5936_, v___x_5947_);
if (v___x_5951_ == 0)
{
lean_inc(v___x_5947_);
v___y_5949_ = v___x_5947_;
goto v___jp_5948_;
}
else
{
v___y_5949_ = v___x_5936_;
goto v___jp_5948_;
}
v___jp_5948_:
{
uint8_t v___x_5950_; 
v___x_5950_ = lean_nat_dec_le(v___y_5949_, v___x_5947_);
if (v___x_5950_ == 0)
{
lean_dec(v___x_5947_);
lean_inc(v___y_5949_);
v___y_5941_ = v___y_5949_;
v___y_5942_ = v___y_5949_;
goto v___jp_5940_;
}
else
{
v___y_5941_ = v___y_5949_;
v___y_5942_ = v___x_5947_;
goto v___jp_5940_;
}
}
}
else
{
lean_object* v___x_5952_; 
v___x_5952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5938_);
return v___x_5952_;
}
v___jp_5940_:
{
lean_object* v___x_5943_; lean_object* v___x_5944_; 
v___x_5943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_5939_, v___x_5938_, v___y_5941_, v___y_5942_);
lean_dec(v___y_5942_);
v___x_5944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
return v___x_5944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_5953_);
lean_dec(v___y_5953_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_5956_, lean_object* v_stx_5957_, lean_object* v_ctx_5958_, uint8_t v_snd_5959_, lean_object* v_fst_5960_, lean_object* v_caps_5961_, lean_object* v_as_5962_, size_t v_sz_5963_, size_t v_i_5964_, lean_object* v_b_5965_){
_start:
{
lean_object* v_a_5967_; uint8_t v___x_5971_; 
v___x_5971_ = lean_usize_dec_lt(v_i_5964_, v_sz_5963_);
if (v___x_5971_ == 0)
{
lean_dec_ref(v_ctx_5958_);
lean_dec_ref(v_mkItem_5956_);
return v_b_5965_;
}
else
{
lean_object* v_a_5972_; lean_object* v_fst_5973_; lean_object* v_snd_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_6016_; 
v_a_5972_ = lean_array_uget(v_as_5962_, v_i_5964_);
v_fst_5973_ = lean_ctor_get(v_a_5972_, 0);
v_snd_5974_ = lean_ctor_get(v_a_5972_, 1);
v_isSharedCheck_6016_ = !lean_is_exclusive(v_a_5972_);
if (v_isSharedCheck_6016_ == 0)
{
v___x_5976_ = v_a_5972_;
v_isShared_5977_ = v_isSharedCheck_6016_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_snd_5974_);
lean_inc(v_fst_5973_);
lean_dec(v_a_5972_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_6016_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___y_5979_; lean_object* v___x_5982_; lean_object* v___y_5984_; lean_object* v___y_5985_; uint8_t v___x_6006_; 
lean_inc(v_fst_5973_);
v___x_5982_ = l_Lean_Name_toString(v_fst_5973_, v___x_5971_);
v___x_6006_ = l_Lean_String_charactersIn(v_fst_5960_, v___x_5982_);
if (v___x_6006_ == 0)
{
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5976_);
lean_dec(v_snd_5974_);
lean_dec(v_fst_5973_);
v_a_5967_ = v_b_5965_;
goto v___jp_5966_;
}
else
{
lean_object* v_textDocument_x3f_6009_; 
v_textDocument_x3f_6009_ = lean_ctor_get(v_caps_5961_, 0);
if (lean_obj_tag(v_textDocument_x3f_6009_) == 0)
{
goto v___jp_6007_;
}
else
{
lean_object* v_val_6010_; lean_object* v_completion_x3f_6011_; 
v_val_6010_ = lean_ctor_get(v_textDocument_x3f_6009_, 0);
v_completion_x3f_6011_ = lean_ctor_get(v_val_6010_, 0);
if (lean_obj_tag(v_completion_x3f_6011_) == 0)
{
goto v___jp_6007_;
}
else
{
lean_object* v_val_6012_; 
v_val_6012_ = lean_ctor_get(v_completion_x3f_6011_, 0);
if (lean_obj_tag(v_val_6012_) == 0)
{
goto v___jp_6007_;
}
else
{
lean_object* v_val_6013_; 
v_val_6013_ = lean_ctor_get(v_val_6012_, 0);
if (lean_obj_tag(v_val_6013_) == 0)
{
goto v___jp_6007_;
}
else
{
lean_object* v_val_6014_; uint8_t v___x_6015_; 
v_val_6014_ = lean_ctor_get(v_val_6013_, 0);
v___x_6015_ = lean_unbox(v_val_6014_);
if (v___x_6015_ == 0)
{
goto v___jp_6007_;
}
else
{
goto v___jp_5995_;
}
}
}
}
}
}
v___jp_5978_:
{
lean_object* v___x_5980_; lean_object* v_items_5981_; 
lean_inc_ref(v_mkItem_5956_);
v___x_5980_ = lean_apply_3(v_mkItem_5956_, v_fst_5973_, v_snd_5974_, v___y_5979_);
v_items_5981_ = lean_array_push(v_b_5965_, v___x_5980_);
v_a_5967_ = v_items_5981_;
goto v___jp_5966_;
}
v___jp_5983_:
{
lean_object* v_toCommandContextInfo_5986_; lean_object* v_fileMap_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v_range_5991_; 
v_toCommandContextInfo_5986_ = lean_ctor_get(v_ctx_5958_, 0);
v_fileMap_5987_ = lean_ctor_get(v_toCommandContextInfo_5986_, 2);
lean_inc_ref_n(v_fileMap_5987_, 2);
v___x_5988_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5987_, v___y_5984_);
lean_dec(v___y_5984_);
v___x_5989_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5987_, v___y_5985_);
lean_dec(v___y_5985_);
if (v_isShared_5977_ == 0)
{
lean_ctor_set(v___x_5976_, 1, v___x_5989_);
lean_ctor_set(v___x_5976_, 0, v___x_5988_);
v_range_5991_ = v___x_5976_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5994_; 
v_reuseFailAlloc_5994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5994_, 0, v___x_5988_);
lean_ctor_set(v_reuseFailAlloc_5994_, 1, v___x_5989_);
v_range_5991_ = v_reuseFailAlloc_5994_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; 
lean_inc_ref(v_range_5991_);
v___x_5992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5982_);
lean_ctor_set(v___x_5992_, 1, v_range_5991_);
lean_ctor_set(v___x_5992_, 2, v_range_5991_);
v___x_5993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
v___y_5979_ = v___x_5993_;
goto v___jp_5978_;
}
}
v___jp_5995_:
{
uint8_t v___x_5996_; lean_object* v___x_5997_; 
v___x_5996_ = 0;
v___x_5997_ = l_Lean_Syntax_getRange_x3f(v_stx_5957_, v___x_5996_);
if (lean_obj_tag(v___x_5997_) == 1)
{
lean_object* v_val_5998_; 
v_val_5998_ = lean_ctor_get(v___x_5997_, 0);
lean_inc(v_val_5998_);
lean_dec_ref_known(v___x_5997_, 1);
if (v_snd_5959_ == 0)
{
lean_object* v_start_5999_; lean_object* v_stop_6000_; 
v_start_5999_ = lean_ctor_get(v_val_5998_, 0);
lean_inc(v_start_5999_);
v_stop_6000_ = lean_ctor_get(v_val_5998_, 1);
lean_inc(v_stop_6000_);
lean_dec(v_val_5998_);
v___y_5984_ = v_start_5999_;
v___y_5985_ = v_stop_6000_;
goto v___jp_5983_;
}
else
{
lean_object* v_start_6001_; lean_object* v_stop_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; 
v_start_6001_ = lean_ctor_get(v_val_5998_, 0);
lean_inc(v_start_6001_);
v_stop_6002_ = lean_ctor_get(v_val_5998_, 1);
lean_inc(v_stop_6002_);
lean_dec(v_val_5998_);
v___x_6003_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_6004_ = lean_nat_add(v_stop_6002_, v___x_6003_);
lean_dec(v_stop_6002_);
v___y_5984_ = v_start_6001_;
v___y_5985_ = v___x_6004_;
goto v___jp_5983_;
}
}
else
{
lean_object* v___x_6005_; 
lean_dec(v___x_5997_);
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5976_);
v___x_6005_ = lean_box(0);
v___y_5979_ = v___x_6005_;
goto v___jp_5978_;
}
}
v___jp_6007_:
{
if (v___x_6006_ == 0)
{
goto v___jp_5995_;
}
else
{
lean_object* v___x_6008_; 
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5976_);
v___x_6008_ = lean_box(0);
v___y_5979_ = v___x_6008_;
goto v___jp_5978_;
}
}
}
}
v___jp_5966_:
{
size_t v___x_5968_; size_t v___x_5969_; 
v___x_5968_ = ((size_t)1ULL);
v___x_5969_ = lean_usize_add(v_i_5964_, v___x_5968_);
v_i_5964_ = v___x_5969_;
v_b_5965_ = v_a_5967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_6017_, lean_object* v_stx_6018_, lean_object* v_ctx_6019_, lean_object* v_snd_6020_, lean_object* v_fst_6021_, lean_object* v_caps_6022_, lean_object* v_as_6023_, lean_object* v_sz_6024_, lean_object* v_i_6025_, lean_object* v_b_6026_){
_start:
{
uint8_t v_snd_1724__boxed_6027_; size_t v_sz_boxed_6028_; size_t v_i_boxed_6029_; lean_object* v_res_6030_; 
v_snd_1724__boxed_6027_ = lean_unbox(v_snd_6020_);
v_sz_boxed_6028_ = lean_unbox_usize(v_sz_6024_);
lean_dec(v_sz_6024_);
v_i_boxed_6029_ = lean_unbox_usize(v_i_6025_);
lean_dec(v_i_6025_);
v_res_6030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6017_, v_stx_6018_, v_ctx_6019_, v_snd_1724__boxed_6027_, v_fst_6021_, v_caps_6022_, v_as_6023_, v_sz_boxed_6028_, v_i_boxed_6029_, v_b_6026_);
lean_dec_ref(v_as_6023_);
lean_dec_ref(v_caps_6022_);
lean_dec_ref(v_fst_6021_);
lean_dec(v_stx_6018_);
return v_res_6030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_6031_, lean_object* v_stx_6032_, lean_object* v_caps_6033_, lean_object* v_ctx_6034_, lean_object* v_mkItem_6035_){
_start:
{
lean_object* v_fst_6037_; uint8_t v_snd_6038_; uint8_t v___x_6043_; lean_object* v___x_6044_; 
v___x_6043_ = 0;
v___x_6044_ = l_Lean_Syntax_getSubstring_x3f(v_stx_6032_, v___x_6043_, v___x_6043_);
if (lean_obj_tag(v___x_6044_) == 0)
{
lean_object* v___x_6045_; 
v___x_6045_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_6037_ = v___x_6045_;
v_snd_6038_ = v___x_6043_;
goto v___jp_6036_;
}
else
{
lean_object* v_val_6046_; lean_object* v_str_6047_; lean_object* v_startPos_6048_; lean_object* v_stopPos_6049_; uint8_t v___y_6051_; uint8_t v___x_6053_; 
v_val_6046_ = lean_ctor_get(v___x_6044_, 0);
lean_inc(v_val_6046_);
lean_dec_ref_known(v___x_6044_, 1);
v_str_6047_ = lean_ctor_get(v_val_6046_, 0);
lean_inc_ref(v_str_6047_);
v_startPos_6048_ = lean_ctor_get(v_val_6046_, 1);
lean_inc(v_startPos_6048_);
v_stopPos_6049_ = lean_ctor_get(v_val_6046_, 2);
lean_inc(v_stopPos_6049_);
lean_dec(v_val_6046_);
v___x_6053_ = lean_string_utf8_at_end(v_str_6047_, v_stopPos_6049_);
if (v___x_6053_ == 0)
{
uint32_t v___x_6054_; uint32_t v___x_6055_; uint8_t v___x_6056_; 
v___x_6054_ = lean_string_utf8_get(v_str_6047_, v_stopPos_6049_);
v___x_6055_ = 46;
v___x_6056_ = lean_uint32_dec_eq(v___x_6054_, v___x_6055_);
if (v___x_6056_ == 0)
{
v___y_6051_ = v___x_6056_;
goto v___jp_6050_;
}
else
{
lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; 
v___x_6057_ = lean_string_utf8_extract(v_str_6047_, v_startPos_6048_, v_stopPos_6049_);
lean_dec(v_stopPos_6049_);
lean_dec(v_startPos_6048_);
lean_dec_ref(v_str_6047_);
v___x_6058_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6059_ = lean_string_append(v___x_6057_, v___x_6058_);
v_fst_6037_ = v___x_6059_;
v_snd_6038_ = v___x_6056_;
goto v___jp_6036_;
}
}
else
{
v___y_6051_ = v___x_6043_;
goto v___jp_6050_;
}
v___jp_6050_:
{
lean_object* v___x_6052_; 
v___x_6052_ = lean_string_utf8_extract(v_str_6047_, v_startPos_6048_, v_stopPos_6049_);
lean_dec(v_stopPos_6049_);
lean_dec(v_startPos_6048_);
lean_dec_ref(v_str_6047_);
v_fst_6037_ = v___x_6052_;
v_snd_6038_ = v___y_6051_;
goto v___jp_6036_;
}
}
v___jp_6036_:
{
lean_object* v_items_6039_; size_t v_sz_6040_; size_t v___x_6041_; lean_object* v___x_6042_; 
v_items_6039_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_6040_ = lean_array_size(v_entries_6031_);
v___x_6041_ = ((size_t)0ULL);
v___x_6042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6035_, v_stx_6032_, v_ctx_6034_, v_snd_6038_, v_fst_6037_, v_caps_6033_, v_entries_6031_, v_sz_6040_, v___x_6041_, v_items_6039_);
lean_dec_ref(v_fst_6037_);
return v___x_6042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_6060_, lean_object* v_stx_6061_, lean_object* v_caps_6062_, lean_object* v_ctx_6063_, lean_object* v_mkItem_6064_){
_start:
{
lean_object* v_res_6065_; 
v_res_6065_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_6060_, v_stx_6061_, v_caps_6062_, v_ctx_6063_, v_mkItem_6064_);
lean_dec_ref(v_caps_6062_);
lean_dec(v_stx_6061_);
lean_dec_ref(v_entries_6060_);
return v_res_6065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_6066_, lean_object* v_caps_6067_, lean_object* v_ctx_6068_, lean_object* v___f_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_){
_start:
{
lean_object* v___x_6075_; lean_object* v_a_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6084_; 
v___x_6075_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6073_);
v_a_6076_ = lean_ctor_get(v___x_6075_, 0);
v_isSharedCheck_6084_ = !lean_is_exclusive(v___x_6075_);
if (v_isSharedCheck_6084_ == 0)
{
v___x_6078_ = v___x_6075_;
v_isShared_6079_ = v_isSharedCheck_6084_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_a_6076_);
lean_dec(v___x_6075_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6084_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v___x_6080_; lean_object* v___x_6082_; 
v___x_6080_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_6076_, v_partialId_6066_, v_caps_6067_, v_ctx_6068_, v___f_6069_);
lean_dec(v_a_6076_);
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 0, v___x_6080_);
v___x_6082_ = v___x_6078_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6083_; 
v_reuseFailAlloc_6083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6083_, 0, v___x_6080_);
v___x_6082_ = v_reuseFailAlloc_6083_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
return v___x_6082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_6085_, lean_object* v_caps_6086_, lean_object* v_ctx_6087_, lean_object* v___f_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
lean_object* v_res_6094_; 
v_res_6094_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6085_, v_caps_6086_, v_ctx_6087_, v___f_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec_ref(v_caps_6086_);
lean_dec(v_partialId_6085_);
return v_res_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_6095_, lean_object* v_pos_6096_, lean_object* v_completionInfoPos_6097_, lean_object* v_ctx_6098_, lean_object* v_partialId_6099_, lean_object* v_caps_6100_){
_start:
{
lean_object* v___f_6102_; lean_object* v___f_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___f_6102_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6102_, 0, v_completionInfoPos_6097_);
lean_closure_set(v___f_6102_, 1, v_uri_6095_);
lean_closure_set(v___f_6102_, 2, v_pos_6096_);
lean_inc_ref(v_ctx_6098_);
v___f_6103_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_6103_, 0, v_partialId_6099_);
lean_closure_set(v___f_6103_, 1, v_caps_6100_);
lean_closure_set(v___f_6103_, 2, v_ctx_6098_);
lean_closure_set(v___f_6103_, 3, v___f_6102_);
v___x_6104_ = lean_unsigned_to_nat(32u);
v___x_6105_ = lean_mk_empty_array_with_capacity(v___x_6104_);
lean_dec_ref(v___x_6105_);
v___x_6106_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_6107_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6098_, v___x_6106_, v___f_6103_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_6108_, lean_object* v_pos_6109_, lean_object* v_completionInfoPos_6110_, lean_object* v_ctx_6111_, lean_object* v_partialId_6112_, lean_object* v_caps_6113_, lean_object* v_a_6114_){
_start:
{
lean_object* v_res_6115_; 
v_res_6115_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6108_, v_pos_6109_, v_completionInfoPos_6110_, v_ctx_6111_, v_partialId_6112_, v_caps_6113_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_){
_start:
{
lean_object* v___x_6121_; 
v___x_6121_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6119_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_){
_start:
{
lean_object* v_res_6127_; 
v_res_6127_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
return v_res_6127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6128_, lean_object* v_t_6129_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6128_, v_t_6129_);
return v___x_6130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6131_, lean_object* v_t_6132_){
_start:
{
lean_object* v_res_6133_; 
v_res_6133_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6131_, v_t_6132_);
lean_dec(v_t_6132_);
return v_res_6133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6134_, lean_object* v_as_6135_, lean_object* v_lo_6136_, lean_object* v_hi_6137_, lean_object* v_w_6138_, lean_object* v_hlo_6139_, lean_object* v_hhi_6140_){
_start:
{
lean_object* v___x_6141_; 
v___x_6141_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6134_, v_as_6135_, v_lo_6136_, v_hi_6137_);
return v___x_6141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6142_, lean_object* v_as_6143_, lean_object* v_lo_6144_, lean_object* v_hi_6145_, lean_object* v_w_6146_, lean_object* v_hlo_6147_, lean_object* v_hhi_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6142_, v_as_6143_, v_lo_6144_, v_hi_6145_, v_w_6146_, v_hlo_6147_, v_hhi_6148_);
lean_dec(v_hi_6145_);
lean_dec(v_n_6142_);
return v_res_6149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(lean_object* v_n_6150_, lean_object* v_lo_6151_, lean_object* v_hi_6152_, lean_object* v_hhi_6153_, lean_object* v_pivot_6154_, lean_object* v_as_6155_, lean_object* v_i_6156_, lean_object* v_k_6157_, lean_object* v_ilo_6158_, lean_object* v_ik_6159_, lean_object* v_w_6160_){
_start:
{
lean_object* v___x_6161_; 
v___x_6161_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6152_, v_pivot_6154_, v_as_6155_, v_i_6156_, v_k_6157_);
return v___x_6161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___boxed(lean_object* v_n_6162_, lean_object* v_lo_6163_, lean_object* v_hi_6164_, lean_object* v_hhi_6165_, lean_object* v_pivot_6166_, lean_object* v_as_6167_, lean_object* v_i_6168_, lean_object* v_k_6169_, lean_object* v_ilo_6170_, lean_object* v_ik_6171_, lean_object* v_w_6172_){
_start:
{
lean_object* v_res_6173_; 
v_res_6173_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(v_n_6162_, v_lo_6163_, v_hi_6164_, v_hhi_6165_, v_pivot_6166_, v_as_6167_, v_i_6168_, v_k_6169_, v_ilo_6170_, v_ik_6171_, v_w_6172_);
lean_dec(v_hi_6164_);
lean_dec(v_lo_6163_);
lean_dec(v_n_6162_);
return v_res_6173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6174_, lean_object* v_uri_6175_, lean_object* v_pos_6176_, size_t v_sz_6177_, size_t v_i_6178_, lean_object* v_bs_6179_){
_start:
{
uint8_t v___x_6180_; 
v___x_6180_ = lean_usize_dec_lt(v_i_6178_, v_sz_6177_);
if (v___x_6180_ == 0)
{
lean_dec_ref(v_pos_6176_);
lean_dec_ref(v_uri_6175_);
lean_dec(v_completionInfoPos_6174_);
return v_bs_6179_;
}
else
{
lean_object* v_v_6181_; lean_object* v_userName_6182_; lean_object* v_docString_6183_; lean_object* v___x_6184_; lean_object* v_bs_x27_6185_; lean_object* v___x_6186_; lean_object* v___y_6188_; 
v_v_6181_ = lean_array_uget_borrowed(v_bs_6179_, v_i_6178_);
v_userName_6182_ = lean_ctor_get(v_v_6181_, 1);
lean_inc_ref(v_userName_6182_);
v_docString_6183_ = lean_ctor_get(v_v_6181_, 3);
lean_inc(v_docString_6183_);
v___x_6184_ = lean_unsigned_to_nat(0u);
v_bs_x27_6185_ = lean_array_uset(v_bs_6179_, v_i_6178_, v___x_6184_);
v___x_6186_ = lean_box(0);
if (lean_obj_tag(v_docString_6183_) == 0)
{
v___y_6188_ = v___x_6186_;
goto v___jp_6187_;
}
else
{
lean_object* v_val_6198_; lean_object* v___x_6200_; uint8_t v_isShared_6201_; uint8_t v_isSharedCheck_6207_; 
v_val_6198_ = lean_ctor_get(v_docString_6183_, 0);
v_isSharedCheck_6207_ = !lean_is_exclusive(v_docString_6183_);
if (v_isSharedCheck_6207_ == 0)
{
v___x_6200_ = v_docString_6183_;
v_isShared_6201_ = v_isSharedCheck_6207_;
goto v_resetjp_6199_;
}
else
{
lean_inc(v_val_6198_);
lean_dec(v_docString_6183_);
v___x_6200_ = lean_box(0);
v_isShared_6201_ = v_isSharedCheck_6207_;
goto v_resetjp_6199_;
}
v_resetjp_6199_:
{
uint8_t v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6205_; 
v___x_6202_ = 1;
v___x_6203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6203_, 0, v_val_6198_);
lean_ctor_set_uint8(v___x_6203_, sizeof(void*)*1, v___x_6202_);
if (v_isShared_6201_ == 0)
{
lean_ctor_set(v___x_6200_, 0, v___x_6203_);
v___x_6205_ = v___x_6200_;
goto v_reusejp_6204_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v___x_6203_);
v___x_6205_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6204_;
}
v_reusejp_6204_:
{
v___y_6188_ = v___x_6205_;
goto v___jp_6187_;
}
}
}
v___jp_6187_:
{
lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; size_t v___x_6194_; size_t v___x_6195_; lean_object* v___x_6196_; 
v___x_6189_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6174_);
v___x_6190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6190_, 0, v_completionInfoPos_6174_);
lean_inc_ref(v_pos_6176_);
lean_inc_ref(v_uri_6175_);
v___x_6191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6191_, 0, v_uri_6175_);
lean_ctor_set(v___x_6191_, 1, v_pos_6176_);
lean_ctor_set(v___x_6191_, 2, v___x_6190_);
lean_ctor_set(v___x_6191_, 3, v___x_6186_);
v___x_6192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
v___x_6193_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6193_, 0, v_userName_6182_);
lean_ctor_set(v___x_6193_, 1, v___x_6186_);
lean_ctor_set(v___x_6193_, 2, v___y_6188_);
lean_ctor_set(v___x_6193_, 3, v___x_6189_);
lean_ctor_set(v___x_6193_, 4, v___x_6186_);
lean_ctor_set(v___x_6193_, 5, v___x_6186_);
lean_ctor_set(v___x_6193_, 6, v___x_6192_);
lean_ctor_set(v___x_6193_, 7, v___x_6186_);
v___x_6194_ = ((size_t)1ULL);
v___x_6195_ = lean_usize_add(v_i_6178_, v___x_6194_);
v___x_6196_ = lean_array_uset(v_bs_x27_6185_, v_i_6178_, v___x_6193_);
v_i_6178_ = v___x_6195_;
v_bs_6179_ = v___x_6196_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6208_, lean_object* v_uri_6209_, lean_object* v_pos_6210_, lean_object* v_sz_6211_, lean_object* v_i_6212_, lean_object* v_bs_6213_){
_start:
{
size_t v_sz_boxed_6214_; size_t v_i_boxed_6215_; lean_object* v_res_6216_; 
v_sz_boxed_6214_ = lean_unbox_usize(v_sz_6211_);
lean_dec(v_sz_6211_);
v_i_boxed_6215_ = lean_unbox_usize(v_i_6212_);
lean_dec(v_i_6212_);
v_res_6216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6208_, v_uri_6209_, v_pos_6210_, v_sz_boxed_6214_, v_i_boxed_6215_, v_bs_6213_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6217_, lean_object* v_completionInfoPos_6218_, lean_object* v_uri_6219_, lean_object* v_pos_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6217_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_);
if (lean_obj_tag(v___x_6226_) == 0)
{
lean_object* v_a_6227_; lean_object* v___x_6229_; uint8_t v_isShared_6230_; uint8_t v_isSharedCheck_6237_; 
v_a_6227_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6237_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6237_ == 0)
{
v___x_6229_ = v___x_6226_;
v_isShared_6230_ = v_isSharedCheck_6237_;
goto v_resetjp_6228_;
}
else
{
lean_inc(v_a_6227_);
lean_dec(v___x_6226_);
v___x_6229_ = lean_box(0);
v_isShared_6230_ = v_isSharedCheck_6237_;
goto v_resetjp_6228_;
}
v_resetjp_6228_:
{
size_t v_sz_6231_; size_t v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6235_; 
v_sz_6231_ = lean_array_size(v_a_6227_);
v___x_6232_ = ((size_t)0ULL);
v___x_6233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6218_, v_uri_6219_, v_pos_6220_, v_sz_6231_, v___x_6232_, v_a_6227_);
if (v_isShared_6230_ == 0)
{
lean_ctor_set(v___x_6229_, 0, v___x_6233_);
v___x_6235_ = v___x_6229_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v___x_6233_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
}
else
{
lean_object* v_a_6238_; lean_object* v___x_6240_; uint8_t v_isShared_6241_; uint8_t v_isSharedCheck_6245_; 
lean_dec_ref(v_pos_6220_);
lean_dec_ref(v_uri_6219_);
lean_dec(v_completionInfoPos_6218_);
v_a_6238_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6245_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6245_ == 0)
{
v___x_6240_ = v___x_6226_;
v_isShared_6241_ = v_isSharedCheck_6245_;
goto v_resetjp_6239_;
}
else
{
lean_inc(v_a_6238_);
lean_dec(v___x_6226_);
v___x_6240_ = lean_box(0);
v_isShared_6241_ = v_isSharedCheck_6245_;
goto v_resetjp_6239_;
}
v_resetjp_6239_:
{
lean_object* v___x_6243_; 
if (v_isShared_6241_ == 0)
{
v___x_6243_ = v___x_6240_;
goto v_reusejp_6242_;
}
else
{
lean_object* v_reuseFailAlloc_6244_; 
v_reuseFailAlloc_6244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6244_, 0, v_a_6238_);
v___x_6243_ = v_reuseFailAlloc_6244_;
goto v_reusejp_6242_;
}
v_reusejp_6242_:
{
return v___x_6243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6246_, lean_object* v_completionInfoPos_6247_, lean_object* v_uri_6248_, lean_object* v_pos_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_){
_start:
{
uint8_t v___x_495__boxed_6255_; lean_object* v_res_6256_; 
v___x_495__boxed_6255_ = lean_unbox(v___x_6246_);
v_res_6256_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_495__boxed_6255_, v_completionInfoPos_6247_, v_uri_6248_, v_pos_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6257_, lean_object* v_pos_6258_, lean_object* v_completionInfoPos_6259_, lean_object* v_ctx_6260_){
_start:
{
lean_object* v___x_6262_; uint8_t v___x_6263_; lean_object* v___x_6264_; lean_object* v___f_6265_; lean_object* v___x_6266_; 
v___x_6262_ = l_Lean_LocalContext_empty;
v___x_6263_ = 0;
v___x_6264_ = lean_box(v___x_6263_);
v___f_6265_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6265_, 0, v___x_6264_);
lean_closure_set(v___f_6265_, 1, v_completionInfoPos_6259_);
lean_closure_set(v___f_6265_, 2, v_uri_6257_);
lean_closure_set(v___f_6265_, 3, v_pos_6258_);
v___x_6266_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6260_, v___x_6262_, v___f_6265_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6267_, lean_object* v_pos_6268_, lean_object* v_completionInfoPos_6269_, lean_object* v_ctx_6270_, lean_object* v_a_6271_){
_start:
{
lean_object* v_res_6272_; 
v_res_6272_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6267_, v_pos_6268_, v_completionInfoPos_6269_, v_ctx_6270_);
return v_res_6272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6273_, lean_object* v_b_6274_){
_start:
{
lean_object* v_array_6275_; lean_object* v_start_6276_; lean_object* v_stop_6277_; lean_object* v___x_6279_; uint8_t v_isShared_6280_; uint8_t v_isSharedCheck_6290_; 
v_array_6275_ = lean_ctor_get(v_a_6273_, 0);
v_start_6276_ = lean_ctor_get(v_a_6273_, 1);
v_stop_6277_ = lean_ctor_get(v_a_6273_, 2);
v_isSharedCheck_6290_ = !lean_is_exclusive(v_a_6273_);
if (v_isSharedCheck_6290_ == 0)
{
v___x_6279_ = v_a_6273_;
v_isShared_6280_ = v_isSharedCheck_6290_;
goto v_resetjp_6278_;
}
else
{
lean_inc(v_stop_6277_);
lean_inc(v_start_6276_);
lean_inc(v_array_6275_);
lean_dec(v_a_6273_);
v___x_6279_ = lean_box(0);
v_isShared_6280_ = v_isSharedCheck_6290_;
goto v_resetjp_6278_;
}
v_resetjp_6278_:
{
uint8_t v___x_6281_; 
v___x_6281_ = lean_nat_dec_lt(v_start_6276_, v_stop_6277_);
if (v___x_6281_ == 0)
{
lean_del_object(v___x_6279_);
lean_dec(v_stop_6277_);
lean_dec(v_start_6276_);
lean_dec_ref(v_array_6275_);
return v_b_6274_;
}
else
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6285_; 
v___x_6282_ = lean_unsigned_to_nat(1u);
v___x_6283_ = lean_nat_add(v_start_6276_, v___x_6282_);
lean_inc_ref(v_array_6275_);
if (v_isShared_6280_ == 0)
{
lean_ctor_set(v___x_6279_, 1, v___x_6283_);
v___x_6285_ = v___x_6279_;
goto v_reusejp_6284_;
}
else
{
lean_object* v_reuseFailAlloc_6289_; 
v_reuseFailAlloc_6289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6289_, 0, v_array_6275_);
lean_ctor_set(v_reuseFailAlloc_6289_, 1, v___x_6283_);
lean_ctor_set(v_reuseFailAlloc_6289_, 2, v_stop_6277_);
v___x_6285_ = v_reuseFailAlloc_6289_;
goto v_reusejp_6284_;
}
v_reusejp_6284_:
{
lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6286_ = lean_array_fget(v_array_6275_, v_start_6276_);
lean_dec(v_start_6276_);
lean_dec_ref(v_array_6275_);
v___x_6287_ = lean_array_push(v_b_6274_, v___x_6286_);
v_a_6273_ = v___x_6285_;
v_b_6274_ = v___x_6287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6293_, lean_object* v_idx_6294_){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6295_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6296_ = lean_array_get_size(v_scopeNames_6293_);
v___x_6297_ = l_Array_toSubarray___redArg(v_scopeNames_6293_, v_idx_6294_, v___x_6296_);
v___x_6298_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6299_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6297_, v___x_6298_);
v___x_6300_ = lean_array_to_list(v___x_6299_);
v___x_6301_ = l_String_intercalate(v___x_6295_, v___x_6300_);
return v___x_6301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6302_, lean_object* v_R_6303_, lean_object* v_a_6304_, lean_object* v_b_6305_){
_start:
{
lean_object* v___x_6306_; 
v___x_6306_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6304_, v_b_6305_);
return v___x_6306_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6307_, lean_object* v_next_6308_, lean_object* v_scopeNames_6309_, lean_object* v_idComponents_6310_, lean_object* v_a_6311_, uint8_t v_b_6312_){
_start:
{
uint8_t v___x_6313_; 
v___x_6313_ = lean_nat_dec_lt(v_a_6311_, v_upperBound_6307_);
if (v___x_6313_ == 0)
{
lean_dec(v_a_6311_);
return v_b_6312_;
}
else
{
uint8_t v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; uint8_t v___x_6317_; 
v___x_6314_ = 0;
v___x_6315_ = lean_nat_add(v_next_6308_, v_a_6311_);
v___x_6316_ = lean_array_get_size(v_scopeNames_6309_);
v___x_6317_ = lean_nat_dec_lt(v___x_6315_, v___x_6316_);
if (v___x_6317_ == 0)
{
lean_dec(v___x_6315_);
lean_dec(v_a_6311_);
return v___x_6314_;
}
else
{
lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; uint8_t v___x_6321_; 
v___x_6318_ = lean_array_fget_borrowed(v_scopeNames_6309_, v___x_6315_);
lean_dec(v___x_6315_);
v___x_6319_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6320_ = lean_array_get_borrowed(v___x_6319_, v_idComponents_6310_, v_a_6311_);
v___x_6321_ = lean_string_dec_eq(v___x_6320_, v___x_6318_);
if (v___x_6321_ == 0)
{
lean_dec(v_a_6311_);
return v___x_6314_;
}
else
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = lean_unsigned_to_nat(1u);
v___x_6323_ = lean_nat_add(v_a_6311_, v___x_6322_);
lean_dec(v_a_6311_);
v_a_6311_ = v___x_6323_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6325_, lean_object* v_next_6326_, lean_object* v_scopeNames_6327_, lean_object* v_idComponents_6328_, lean_object* v_a_6329_, lean_object* v_b_6330_){
_start:
{
uint8_t v_b_boxed_6331_; uint8_t v_res_6332_; lean_object* v_r_6333_; 
v_b_boxed_6331_ = lean_unbox(v_b_6330_);
v_res_6332_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6325_, v_next_6326_, v_scopeNames_6327_, v_idComponents_6328_, v_a_6329_, v_b_boxed_6331_);
lean_dec_ref(v_idComponents_6328_);
lean_dec_ref(v_scopeNames_6327_);
lean_dec(v_next_6326_);
lean_dec(v_upperBound_6325_);
v_r_6333_ = lean_box(v_res_6332_);
return v_r_6333_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6334_, lean_object* v_idComponents_6335_, lean_object* v_scopeNames_6336_, lean_object* v_a_6337_, lean_object* v_b_6338_){
_start:
{
lean_object* v_a_6340_; uint8_t v___x_6344_; 
v___x_6344_ = lean_nat_dec_lt(v_a_6337_, v_upperBound_6334_);
if (v___x_6344_ == 0)
{
lean_dec(v_a_6337_);
lean_dec_ref(v_scopeNames_6336_);
return v_b_6338_;
}
else
{
lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; uint8_t v___x_6348_; 
v___x_6345_ = lean_array_get_size(v_idComponents_6335_);
v___x_6346_ = lean_unsigned_to_nat(1u);
v___x_6347_ = lean_nat_sub(v___x_6345_, v___x_6346_);
v___x_6348_ = lean_nat_dec_lt(v___x_6347_, v___x_6345_);
if (v___x_6348_ == 0)
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
lean_dec(v___x_6347_);
lean_inc(v_a_6337_);
lean_inc_ref(v_scopeNames_6336_);
v___x_6349_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6336_, v_a_6337_);
v___x_6350_ = lean_array_push(v_b_6338_, v___x_6349_);
v_a_6340_ = v___x_6350_;
goto v___jp_6339_;
}
else
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; uint8_t v___x_6354_; 
v___x_6351_ = lean_nat_add(v_a_6337_, v___x_6345_);
v___x_6352_ = lean_nat_sub(v___x_6351_, v___x_6346_);
lean_dec(v___x_6351_);
v___x_6353_ = lean_array_get_size(v_scopeNames_6336_);
v___x_6354_ = lean_nat_dec_lt(v___x_6352_, v___x_6353_);
if (v___x_6354_ == 0)
{
lean_dec(v___x_6352_);
lean_dec(v___x_6347_);
v_a_6340_ = v_b_6338_;
goto v___jp_6339_;
}
else
{
lean_object* v___x_6355_; lean_object* v___x_6356_; uint8_t v___x_6357_; 
v___x_6355_ = lean_array_fget_borrowed(v_idComponents_6335_, v___x_6347_);
v___x_6356_ = lean_array_fget_borrowed(v_scopeNames_6336_, v___x_6352_);
v___x_6357_ = l_Lean_String_charactersIn(v___x_6355_, v___x_6356_);
if (v___x_6357_ == 0)
{
lean_dec(v___x_6352_);
lean_dec(v___x_6347_);
v_a_6340_ = v_b_6338_;
goto v___jp_6339_;
}
else
{
lean_object* v___x_6358_; uint8_t v___x_6359_; 
v___x_6358_ = lean_unsigned_to_nat(0u);
v___x_6359_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6347_, v_a_6337_, v_scopeNames_6336_, v_idComponents_6335_, v___x_6358_, v___x_6357_);
lean_dec(v___x_6347_);
if (v___x_6359_ == 0)
{
lean_dec(v___x_6352_);
v_a_6340_ = v_b_6338_;
goto v___jp_6339_;
}
else
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
lean_inc_ref(v_scopeNames_6336_);
v___x_6360_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6336_, v___x_6352_);
v___x_6361_ = lean_array_push(v_b_6338_, v___x_6360_);
v_a_6340_ = v___x_6361_;
goto v___jp_6339_;
}
}
}
}
}
v___jp_6339_:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; 
v___x_6341_ = lean_unsigned_to_nat(1u);
v___x_6342_ = lean_nat_add(v_a_6337_, v___x_6341_);
lean_dec(v_a_6337_);
v_a_6337_ = v___x_6342_;
v_b_6338_ = v_a_6340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6362_, lean_object* v_idComponents_6363_, lean_object* v_scopeNames_6364_, lean_object* v_a_6365_, lean_object* v_b_6366_){
_start:
{
lean_object* v_res_6367_; 
v_res_6367_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6362_, v_idComponents_6363_, v_scopeNames_6364_, v_a_6365_, v_b_6366_);
lean_dec_ref(v_idComponents_6363_);
lean_dec(v_upperBound_6362_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6368_, lean_object* v_scopeNames_6369_){
_start:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v_r_6372_; lean_object* v___x_6373_; 
v___x_6370_ = lean_unsigned_to_nat(0u);
v___x_6371_ = lean_array_get_size(v_scopeNames_6369_);
v_r_6372_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6373_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6371_, v_idComponents_6368_, v_scopeNames_6369_, v___x_6370_, v_r_6372_);
return v___x_6373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6374_, lean_object* v_scopeNames_6375_){
_start:
{
lean_object* v_res_6376_; 
v_res_6376_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6374_, v_scopeNames_6375_);
lean_dec_ref(v_idComponents_6374_);
return v_res_6376_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6377_, lean_object* v_next_6378_, lean_object* v_scopeNames_6379_, lean_object* v_idComponents_6380_, lean_object* v_inst_6381_, lean_object* v_R_6382_, lean_object* v_a_6383_, uint8_t v_b_6384_, lean_object* v_c_6385_){
_start:
{
uint8_t v___x_6386_; 
v___x_6386_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6377_, v_next_6378_, v_scopeNames_6379_, v_idComponents_6380_, v_a_6383_, v_b_6384_);
return v___x_6386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6387_, lean_object* v_next_6388_, lean_object* v_scopeNames_6389_, lean_object* v_idComponents_6390_, lean_object* v_inst_6391_, lean_object* v_R_6392_, lean_object* v_a_6393_, lean_object* v_b_6394_, lean_object* v_c_6395_){
_start:
{
uint8_t v_b_boxed_6396_; uint8_t v_res_6397_; lean_object* v_r_6398_; 
v_b_boxed_6396_ = lean_unbox(v_b_6394_);
v_res_6397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6387_, v_next_6388_, v_scopeNames_6389_, v_idComponents_6390_, v_inst_6391_, v_R_6392_, v_a_6393_, v_b_boxed_6396_, v_c_6395_);
lean_dec_ref(v_idComponents_6390_);
lean_dec_ref(v_scopeNames_6389_);
lean_dec(v_next_6388_);
lean_dec(v_upperBound_6387_);
v_r_6398_ = lean_box(v_res_6397_);
return v_r_6398_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6399_, lean_object* v_idComponents_6400_, lean_object* v_scopeNames_6401_, lean_object* v_inst_6402_, lean_object* v_R_6403_, lean_object* v_a_6404_, lean_object* v_b_6405_, lean_object* v_c_6406_){
_start:
{
lean_object* v___x_6407_; 
v___x_6407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6399_, v_idComponents_6400_, v_scopeNames_6401_, v_a_6404_, v_b_6405_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6408_, lean_object* v_idComponents_6409_, lean_object* v_scopeNames_6410_, lean_object* v_inst_6411_, lean_object* v_R_6412_, lean_object* v_a_6413_, lean_object* v_b_6414_, lean_object* v_c_6415_){
_start:
{
lean_object* v_res_6416_; 
v_res_6416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6408_, v_idComponents_6409_, v_scopeNames_6410_, v_inst_6411_, v_R_6412_, v_a_6413_, v_b_6414_, v_c_6415_);
lean_dec_ref(v_idComponents_6409_);
lean_dec(v_upperBound_6408_);
return v_res_6416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6417_){
_start:
{
lean_object* v___x_6418_; lean_object* v___x_6419_; uint8_t v___x_6420_; 
v___x_6418_ = lean_string_utf8_byte_size(v_x_6417_);
v___x_6419_ = lean_unsigned_to_nat(0u);
v___x_6420_ = lean_nat_dec_eq(v___x_6418_, v___x_6419_);
if (v___x_6420_ == 0)
{
uint8_t v___x_6421_; 
v___x_6421_ = 1;
return v___x_6421_;
}
else
{
uint8_t v___x_6422_; 
v___x_6422_ = 0;
return v___x_6422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6423_){
_start:
{
uint8_t v_res_6424_; lean_object* v_r_6425_; 
v_res_6424_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6423_);
lean_dec_ref(v_x_6423_);
v_r_6425_ = lean_box(v_res_6424_);
return v_r_6425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6426_, size_t v_i_6427_, lean_object* v_bs_6428_){
_start:
{
uint8_t v___x_6429_; 
v___x_6429_ = lean_usize_dec_lt(v_i_6427_, v_sz_6426_);
if (v___x_6429_ == 0)
{
return v_bs_6428_;
}
else
{
lean_object* v_v_6430_; lean_object* v___x_6431_; lean_object* v_bs_x27_6432_; lean_object* v___x_6433_; size_t v___x_6434_; size_t v___x_6435_; lean_object* v___x_6436_; 
v_v_6430_ = lean_array_uget(v_bs_6428_, v_i_6427_);
v___x_6431_ = lean_unsigned_to_nat(0u);
v_bs_x27_6432_ = lean_array_uset(v_bs_6428_, v_i_6427_, v___x_6431_);
v___x_6433_ = l_Lean_Name_toString(v_v_6430_, v___x_6429_);
v___x_6434_ = ((size_t)1ULL);
v___x_6435_ = lean_usize_add(v_i_6427_, v___x_6434_);
v___x_6436_ = lean_array_uset(v_bs_x27_6432_, v_i_6427_, v___x_6433_);
v_i_6427_ = v___x_6435_;
v_bs_6428_ = v___x_6436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6438_, lean_object* v_i_6439_, lean_object* v_bs_6440_){
_start:
{
size_t v_sz_boxed_6441_; size_t v_i_boxed_6442_; lean_object* v_res_6443_; 
v_sz_boxed_6441_ = lean_unbox_usize(v_sz_6438_);
lean_dec(v_sz_6438_);
v_i_boxed_6442_ = lean_unbox_usize(v_i_6439_);
lean_dec(v_i_6439_);
v_res_6443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6441_, v_i_boxed_6442_, v_bs_6440_);
return v_res_6443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6444_, lean_object* v_uri_6445_, lean_object* v_pos_6446_, size_t v_sz_6447_, size_t v_i_6448_, lean_object* v_bs_6449_){
_start:
{
uint8_t v___x_6450_; 
v___x_6450_ = lean_usize_dec_lt(v_i_6448_, v_sz_6447_);
if (v___x_6450_ == 0)
{
lean_dec_ref(v_pos_6446_);
lean_dec_ref(v_uri_6445_);
lean_dec(v_completionInfoPos_6444_);
return v_bs_6449_;
}
else
{
lean_object* v_v_6451_; lean_object* v___x_6452_; lean_object* v_bs_x27_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; size_t v___x_6460_; size_t v___x_6461_; lean_object* v___x_6462_; 
v_v_6451_ = lean_array_uget(v_bs_6449_, v_i_6448_);
v___x_6452_ = lean_unsigned_to_nat(0u);
v_bs_x27_6453_ = lean_array_uset(v_bs_6449_, v_i_6448_, v___x_6452_);
v___x_6454_ = lean_box(0);
v___x_6455_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6444_);
v___x_6456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6456_, 0, v_completionInfoPos_6444_);
lean_inc_ref(v_pos_6446_);
lean_inc_ref(v_uri_6445_);
v___x_6457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6457_, 0, v_uri_6445_);
lean_ctor_set(v___x_6457_, 1, v_pos_6446_);
lean_ctor_set(v___x_6457_, 2, v___x_6456_);
lean_ctor_set(v___x_6457_, 3, v___x_6454_);
v___x_6458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6458_, 0, v___x_6457_);
v___x_6459_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6459_, 0, v_v_6451_);
lean_ctor_set(v___x_6459_, 1, v___x_6454_);
lean_ctor_set(v___x_6459_, 2, v___x_6454_);
lean_ctor_set(v___x_6459_, 3, v___x_6455_);
lean_ctor_set(v___x_6459_, 4, v___x_6454_);
lean_ctor_set(v___x_6459_, 5, v___x_6454_);
lean_ctor_set(v___x_6459_, 6, v___x_6458_);
lean_ctor_set(v___x_6459_, 7, v___x_6454_);
v___x_6460_ = ((size_t)1ULL);
v___x_6461_ = lean_usize_add(v_i_6448_, v___x_6460_);
v___x_6462_ = lean_array_uset(v_bs_x27_6453_, v_i_6448_, v___x_6459_);
v_i_6448_ = v___x_6461_;
v_bs_6449_ = v___x_6462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6464_, lean_object* v_uri_6465_, lean_object* v_pos_6466_, lean_object* v_sz_6467_, lean_object* v_i_6468_, lean_object* v_bs_6469_){
_start:
{
size_t v_sz_boxed_6470_; size_t v_i_boxed_6471_; lean_object* v_res_6472_; 
v_sz_boxed_6470_ = lean_unbox_usize(v_sz_6467_);
lean_dec(v_sz_6467_);
v_i_boxed_6471_ = lean_unbox_usize(v_i_6468_);
lean_dec(v_i_6468_);
v_res_6472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6464_, v_uri_6465_, v_pos_6466_, v_sz_boxed_6470_, v_i_boxed_6471_, v_bs_6469_);
return v_res_6472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6474_, lean_object* v_pos_6475_, lean_object* v_completionInfoPos_6476_, lean_object* v_id_x3f_6477_, uint8_t v_danglingDot_6478_, lean_object* v_scopeNames_6479_){
_start:
{
lean_object* v___f_6481_; lean_object* v_idComponents_6483_; lean_object* v___y_6494_; 
v___f_6481_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6477_) == 0)
{
lean_object* v___x_6497_; 
v___x_6497_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6494_ = v___x_6497_;
goto v___jp_6493_;
}
else
{
lean_object* v_val_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; size_t v_sz_6501_; size_t v___x_6502_; lean_object* v___x_6503_; 
v_val_6498_ = lean_ctor_get(v_id_x3f_6477_, 0);
lean_inc(v_val_6498_);
lean_dec_ref_known(v_id_x3f_6477_, 1);
v___x_6499_ = l_Lean_Name_components(v_val_6498_);
v___x_6500_ = lean_array_mk(v___x_6499_);
v_sz_6501_ = lean_array_size(v___x_6500_);
v___x_6502_ = ((size_t)0ULL);
v___x_6503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6501_, v___x_6502_, v___x_6500_);
v___y_6494_ = v___x_6503_;
goto v___jp_6493_;
}
v___jp_6482_:
{
lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v_scopeNames_6487_; lean_object* v_candidates_6488_; size_t v_sz_6489_; size_t v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; 
v___x_6484_ = lean_array_mk(v_scopeNames_6479_);
v___x_6485_ = lean_array_pop(v___x_6484_);
v___x_6486_ = l_Array_takeWhile___redArg(v___f_6481_, v___x_6485_);
lean_dec_ref(v___x_6485_);
v_scopeNames_6487_ = l_Array_reverse___redArg(v___x_6486_);
v_candidates_6488_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6483_, v_scopeNames_6487_);
lean_dec_ref(v_idComponents_6483_);
v_sz_6489_ = lean_array_size(v_candidates_6488_);
v___x_6490_ = ((size_t)0ULL);
v___x_6491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6476_, v_uri_6474_, v_pos_6475_, v_sz_6489_, v___x_6490_, v_candidates_6488_);
v___x_6492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6492_, 0, v___x_6491_);
return v___x_6492_;
}
v___jp_6493_:
{
if (v_danglingDot_6478_ == 0)
{
v_idComponents_6483_ = v___y_6494_;
goto v___jp_6482_;
}
else
{
lean_object* v___x_6495_; lean_object* v_idComponents_6496_; 
v___x_6495_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6496_ = lean_array_push(v___y_6494_, v___x_6495_);
v_idComponents_6483_ = v_idComponents_6496_;
goto v___jp_6482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6504_, lean_object* v_pos_6505_, lean_object* v_completionInfoPos_6506_, lean_object* v_id_x3f_6507_, lean_object* v_danglingDot_6508_, lean_object* v_scopeNames_6509_, lean_object* v_a_6510_){
_start:
{
uint8_t v_danglingDot_boxed_6511_; lean_object* v_res_6512_; 
v_danglingDot_boxed_6511_ = lean_unbox(v_danglingDot_6508_);
v_res_6512_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6504_, v_pos_6505_, v_completionInfoPos_6506_, v_id_x3f_6507_, v_danglingDot_boxed_6511_, v_scopeNames_6509_);
return v_res_6512_;
}
}
lean_object* runtime_initialize_Lean_Data_FuzzyMatching(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_EligibleHeaderDecls(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
