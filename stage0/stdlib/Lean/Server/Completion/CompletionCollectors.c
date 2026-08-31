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
size_t lean_usize_of_nat(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_433_; lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_493_; 
v___x_433_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_427_, v_a_428_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_493_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_493_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_493_;
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
lean_object* v_val_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_488_; 
v_val_438_ = lean_ctor_get(v_a_434_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_488_ == 0)
{
v___x_440_ = v_a_434_;
v_isShared_441_ = v_isSharedCheck_488_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_val_438_);
lean_dec(v_a_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_488_;
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
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = l_Lean_Name_replacePrefix(v___x_448_, v_id_425_, v___x_447_);
v___x_480_ = l_Lean_Name_isAtomic(v___x_479_);
if (v___x_480_ == 0)
{
lean_dec(v___x_479_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = l_Lean_Name_isAnonymous(v___x_479_);
if (v___x_481_ == 0)
{
if (v___x_478_ == 0)
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
else
{
lean_dec(v___x_479_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_430_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_dec(v_a_434_);
v___x_489_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_489_);
v___x_491_ = v___x_436_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg___boxed(lean_object* v_ns_494_, lean_object* v_id_495_, lean_object* v_danglingDot_496_, lean_object* v_declName_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
uint8_t v_danglingDot_boxed_500_; lean_object* v_res_501_; 
v_danglingDot_boxed_500_ = lean_unbox(v_danglingDot_496_);
v_res_501_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_494_, v_id_495_, v_danglingDot_boxed_500_, v_declName_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec(v_id_495_);
lean_dec(v_ns_494_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object* v_ns_502_, lean_object* v_id_503_, uint8_t v_danglingDot_504_, lean_object* v_declName_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_502_, v_id_503_, v_danglingDot_504_, v_declName_505_, v_a_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* v_ns_512_, lean_object* v_id_513_, lean_object* v_danglingDot_514_, lean_object* v_declName_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
uint8_t v_danglingDot_boxed_521_; lean_object* v_res_522_; 
v_danglingDot_boxed_521_ = lean_unbox(v_danglingDot_514_);
v_res_522_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(v_ns_512_, v_id_513_, v_danglingDot_boxed_521_, v_declName_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_id_513_);
lean_dec(v_ns_512_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0(lean_object* v___y_523_, lean_object* v_toPure_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_a_525_);
lean_ctor_set(v___x_526_, 1, v___y_523_);
v___x_527_ = lean_apply_2(v_toPure_524_, lean_box(0), v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1(lean_object* v_f_528_, lean_object* v_decl_529_, lean_object* v_ci_530_, lean_object* v_toPure_531_, lean_object* v_toBind_532_, lean_object* v_____r_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___f_536_; lean_object* v___x_537_; 
v___x_535_ = lean_apply_2(v_f_528_, v_decl_529_, v_ci_530_);
v___f_536_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_536_, 0, v___y_534_);
lean_closure_set(v___f_536_, 1, v_toPure_531_);
v___x_537_ = lean_apply_4(v_toBind_532_, lean_box(0), lean_box(0), v___x_535_, v___f_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2(lean_object* v___f_538_, lean_object* v_____x_539_){
_start:
{
lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_542_; 
v_fst_540_ = lean_ctor_get(v_____x_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v_____x_539_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v_____x_539_);
v___x_542_ = lean_apply_2(v___f_538_, v_fst_540_, v_snd_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(lean_object* v_toPure_546_, lean_object* v_toBind_547_, lean_object* v___f_548_, lean_object* v_____x_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___closed__0));
v___x_551_ = lean_apply_2(v_toPure_546_, lean_box(0), v___x_550_);
v___x_552_ = lean_apply_4(v_toBind_547_, lean_box(0), lean_box(0), v___x_551_, v___f_548_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed(lean_object* v_toPure_553_, lean_object* v_toBind_554_, lean_object* v___f_555_, lean_object* v_____x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3(v_toPure_553_, v_toBind_554_, v___f_555_, v_____x_556_);
lean_dec_ref(v_____x_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4(lean_object* v_snd_558_, lean_object* v_toPure_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_a_560_);
lean_ctor_set(v___x_561_, 1, v_snd_558_);
v___x_562_ = lean_apply_2(v_toPure_559_, lean_box(0), v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5(lean_object* v___f_563_, lean_object* v_toPure_564_, lean_object* v_toBind_565_, lean_object* v_inst_566_, lean_object* v___f_567_, lean_object* v_____x_568_){
_start:
{
lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_fst_569_ = lean_ctor_get(v_____x_568_, 0);
lean_inc(v_fst_569_);
v_snd_570_ = lean_ctor_get(v_____x_568_, 1);
lean_inc(v_snd_570_);
lean_dec_ref(v_____x_568_);
v___x_571_ = lean_unsigned_to_nat(10000u);
v___x_572_ = lean_nat_dec_le(v___x_571_, v_fst_569_);
lean_dec(v_fst_569_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___f_567_);
lean_dec(v_inst_566_);
lean_dec(v_toBind_565_);
lean_dec(v_toPure_564_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_apply_2(v___f_563_, v___x_573_, v_snd_570_);
return v___x_574_;
}
else
{
lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___f_563_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_575_, 0, v_snd_570_);
lean_closure_set(v___f_575_, 1, v_toPure_564_);
lean_inc(v_toBind_565_);
v___x_576_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v_inst_566_, v___f_575_);
v___x_577_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_576_, v___f_567_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6(lean_object* v_toPure_578_, lean_object* v_toBind_579_, lean_object* v___f_580_, lean_object* v_____x_581_){
_start:
{
lean_object* v_snd_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v_snd_582_ = lean_ctor_get(v_____x_581_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_____x_581_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_____x_581_, 0);
lean_dec(v_unused_592_);
v___x_584_ = v_____x_581_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_snd_582_);
lean_dec(v_____x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
lean_inc(v_snd_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_snd_582_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_snd_582_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_snd_582_);
v___x_587_ = v_reuseFailAlloc_590_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_apply_2(v_toPure_578_, lean_box(0), v___x_587_);
v___x_589_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_588_, v___f_580_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(lean_object* v_f_593_, lean_object* v_toPure_594_, lean_object* v_toBind_595_, lean_object* v_inst_596_, lean_object* v_decl_597_, lean_object* v_ci_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc_n(v_toBind_595_, 4);
lean_inc_n(v_toPure_594_, 4);
v___f_600_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__1), 7, 5);
lean_closure_set(v___f_600_, 0, v_f_593_);
lean_closure_set(v___f_600_, 1, v_decl_597_);
lean_closure_set(v___f_600_, 2, v_ci_598_);
lean_closure_set(v___f_600_, 3, v_toPure_594_);
lean_closure_set(v___f_600_, 4, v_toBind_595_);
lean_inc_ref(v___f_600_);
v___f_601_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_601_, 0, v___f_600_);
v___f_602_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_602_, 0, v_toPure_594_);
lean_closure_set(v___f_602_, 1, v_toBind_595_);
lean_closure_set(v___f_602_, 2, v___f_601_);
v___f_603_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_603_, 0, v___f_600_);
lean_closure_set(v___f_603_, 1, v_toPure_594_);
lean_closure_set(v___f_603_, 2, v_toBind_595_);
lean_closure_set(v___f_603_, 3, v_inst_596_);
lean_closure_set(v___f_603_, 4, v___f_602_);
v___f_604_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__6), 4, 3);
lean_closure_set(v___f_604_, 0, v_toPure_594_);
lean_closure_set(v___f_604_, 1, v_toBind_595_);
lean_closure_set(v___f_604_, 2, v___f_603_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v___y_599_, v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_apply_2(v_toPure_594_, lean_box(0), v___x_608_);
v___x_610_ = lean_apply_4(v_toBind_595_, lean_box(0), lean_box(0), v___x_609_, v___f_604_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed(lean_object* v_f_611_, lean_object* v_toPure_612_, lean_object* v_toBind_613_, lean_object* v_inst_614_, lean_object* v_decl_615_, lean_object* v_ci_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7(v_f_611_, v_toPure_612_, v_toBind_613_, v_inst_614_, v_decl_615_, v_ci_616_, v___y_617_);
lean_dec(v___y_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(lean_object* v_toPure_619_, lean_object* v_____x_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(0);
v___x_622_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed(lean_object* v_toPure_623_, lean_object* v_____x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8(v_toPure_623_, v_____x_624_);
lean_dec_ref(v_____x_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_f_630_){
_start:
{
lean_object* v_toApplicative_631_; lean_object* v_toBind_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_getEnv_643_; lean_object* v_modifyEnv_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_662_; 
v_toApplicative_631_ = lean_ctor_get(v_inst_626_, 0);
lean_inc_ref(v_toApplicative_631_);
v_toBind_632_ = lean_ctor_get(v_inst_626_, 1);
lean_inc(v_toBind_632_);
lean_inc_ref_n(v_inst_626_, 7);
v___f_633_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_633_, 0, v_inst_626_);
v___f_634_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_634_, 0, v_inst_626_);
v___f_635_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_635_, 0, v_inst_626_);
v___f_636_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_636_, 0, v_inst_626_);
v___x_637_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_637_, 0, lean_box(0));
lean_closure_set(v___x_637_, 1, lean_box(0));
lean_closure_set(v___x_637_, 2, v_inst_626_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___f_633_);
v___x_639_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_639_, 0, lean_box(0));
lean_closure_set(v___x_639_, 1, lean_box(0));
lean_closure_set(v___x_639_, 2, v_inst_626_);
v___x_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_ctor_set(v___x_640_, 2, v___f_634_);
lean_ctor_set(v___x_640_, 3, v___f_635_);
lean_ctor_set(v___x_640_, 4, v___f_636_);
v___x_641_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_641_, 0, lean_box(0));
lean_closure_set(v___x_641_, 1, lean_box(0));
lean_closure_set(v___x_641_, 2, v_inst_626_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v_getEnv_643_ = lean_ctor_get(v_inst_627_, 0);
v_modifyEnv_644_ = lean_ctor_get(v_inst_627_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_inst_627_);
if (v_isSharedCheck_662_ == 0)
{
v___x_646_ = v_inst_627_;
v_isShared_647_ = v_isSharedCheck_662_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_modifyEnv_644_);
lean_inc(v_getEnv_643_);
lean_dec(v_inst_627_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_662_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
lean_inc_ref(v_inst_626_);
v___x_648_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_648_, 0, lean_box(0));
lean_closure_set(v___x_648_, 1, lean_box(0));
lean_closure_set(v___x_648_, 2, v_inst_626_);
lean_inc_ref(v___x_648_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_649_, 0, v_modifyEnv_644_);
lean_closure_set(v___f_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, lean_box(0));
lean_closure_set(v___x_650_, 2, v_inst_626_);
lean_closure_set(v___x_650_, 3, lean_box(0));
lean_closure_set(v___x_650_, 4, v_getEnv_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___f_649_);
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___f_649_);
v___x_652_ = v_reuseFailAlloc_661_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v_toPure_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___x_447__overap_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_toPure_653_ = lean_ctor_get(v_toApplicative_631_, 1);
lean_inc_n(v_toPure_653_, 2);
lean_dec_ref(v_toApplicative_631_);
lean_inc(v_toBind_632_);
v___f_654_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_654_, 0, v_f_630_);
lean_closure_set(v___f_654_, 1, v_toPure_653_);
lean_closure_set(v___f_654_, 2, v_toBind_632_);
lean_closure_set(v___f_654_, 3, v_inst_629_);
v___f_655_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_655_, 0, v_inst_628_);
lean_closure_set(v___f_655_, 1, v___x_648_);
v___f_656_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_656_, 0, v_toPure_653_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_447__overap_658_ = l_Lean_Server_Completion_forEligibleDeclsM___redArg(v___x_642_, v___x_652_, v___f_655_, v___f_654_);
v___x_659_ = lean_apply_1(v___x_447__overap_658_, v___x_657_);
v___x_660_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_659_, v___f_656_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM(lean_object* v_m_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_f_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___redArg(v_inst_664_, v_inst_665_, v_inst_666_, v_inst_667_, v_f_668_);
return v___x_669_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object* v_id_670_, lean_object* v_declName_671_, uint8_t v_danglingDot_672_){
_start:
{
if (v_danglingDot_672_ == 0)
{
if (lean_obj_tag(v_id_670_) == 1)
{
lean_object* v_pre_673_; 
v_pre_673_ = lean_ctor_get(v_id_670_, 0);
if (lean_obj_tag(v_pre_673_) == 0)
{
if (lean_obj_tag(v_declName_671_) == 1)
{
lean_object* v_pre_674_; 
v_pre_674_ = lean_ctor_get(v_declName_671_, 0);
if (lean_obj_tag(v_pre_674_) == 0)
{
lean_object* v_str_675_; lean_object* v_str_676_; uint8_t v___x_677_; 
v_str_675_ = lean_ctor_get(v_id_670_, 1);
v_str_676_ = lean_ctor_get(v_declName_671_, 1);
v___x_677_ = l_Lean_String_charactersIn(v_str_675_, v_str_676_);
return v___x_677_;
}
else
{
return v_danglingDot_672_;
}
}
else
{
return v_danglingDot_672_;
}
}
else
{
return v_danglingDot_672_;
}
}
else
{
return v_danglingDot_672_;
}
}
else
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object* v_id_679_, lean_object* v_declName_680_, lean_object* v_danglingDot_681_){
_start:
{
uint8_t v_danglingDot_boxed_682_; uint8_t v_res_683_; lean_object* v_r_684_; 
v_danglingDot_boxed_682_ = lean_unbox(v_danglingDot_681_);
v_res_683_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_679_, v_declName_680_, v_danglingDot_boxed_682_);
lean_dec(v_declName_680_);
lean_dec(v_id_679_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(lean_object* v_msg_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0___closed__0));
v___x_690_ = lean_panic_fn_borrowed(v___x_689_, v_msg_688_);
return v___x_690_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2));
v___x_695_ = lean_unsigned_to_nat(26u);
v___x_696_ = lean_unsigned_to_nat(177u);
v___x_697_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1));
v___x_698_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__0));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object* v_newLen_700_, lean_object* v_id_701_){
_start:
{
switch(lean_obj_tag(v_id_701_))
{
case 0:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_newLen_700_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_id_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
return v___x_703_;
}
case 1:
{
lean_object* v_pre_704_; lean_object* v_str_705_; lean_object* v___x_706_; lean_object* v_snd_707_; lean_object* v___y_709_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_pre_704_ = lean_ctor_get(v_id_701_, 0);
v_str_705_ = lean_ctor_get(v_id_701_, 1);
lean_inc(v_pre_704_);
lean_inc(v_newLen_700_);
v___x_706_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_700_, v_pre_704_);
v_snd_707_ = lean_ctor_get(v___x_706_, 1);
lean_inc(v_snd_707_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_snd_707_, v___x_721_);
v___x_723_ = lean_nat_dec_le(v_newLen_700_, v___x_722_);
lean_dec(v___x_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; 
lean_dec_ref(v___x_706_);
v___x_724_ = l_Lean_Name_isAnonymous(v_pre_704_);
if (v___x_724_ == 0)
{
v___y_709_ = v___x_721_;
goto v___jp_708_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___y_709_ = v___x_725_;
goto v___jp_708_;
}
}
else
{
lean_dec(v_snd_707_);
lean_dec_ref_known(v_id_701_, 2);
lean_dec(v_newLen_700_);
return v___x_706_;
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_len_x27_712_; uint8_t v___x_713_; 
v___x_710_ = lean_nat_add(v_snd_707_, v___y_709_);
v___x_711_ = lean_string_length(v_str_705_);
v_len_x27_712_ = lean_nat_add(v___x_710_, v___x_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_nat_dec_le(v_len_x27_712_, v_newLen_700_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_inc_ref(v_str_705_);
lean_inc(v_pre_704_);
lean_dec(v_len_x27_712_);
lean_dec_ref_known(v_id_701_, 2);
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_nat_sub(v_newLen_700_, v___y_709_);
v___x_716_ = lean_nat_sub(v___x_715_, v_snd_707_);
lean_dec(v_snd_707_);
lean_dec(v___x_715_);
v___x_717_ = lean_string_utf8_extract(v_str_705_, v___x_714_, v___x_716_);
lean_dec(v___x_716_);
lean_dec_ref(v_str_705_);
v___x_718_ = l_Lean_Name_str___override(v_pre_704_, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_newLen_700_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v_snd_707_);
lean_dec(v_newLen_700_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_id_701_);
lean_ctor_set(v___x_720_, 1, v_len_x27_712_);
return v___x_720_;
}
}
}
default: 
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref_known(v_id_701_, 2);
lean_dec(v_newLen_700_);
v___x_726_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3);
v___x_727_ = l_panic___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go_spec__0(v___x_726_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object* v_id_728_, lean_object* v_newLen_729_){
_start:
{
lean_object* v___x_730_; lean_object* v_fst_731_; 
v___x_730_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(v_newLen_729_, v_id_728_);
v_fst_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_fst_731_);
lean_dec_ref(v___x_730_);
return v_fst_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(lean_object* v_matchUsingNamespace_732_, lean_object* v_ns_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
if (lean_obj_tag(v_ns_733_) == 1)
{
lean_object* v_pre_743_; lean_object* v___x_744_; 
v_pre_743_ = lean_ctor_get(v_ns_733_, 0);
lean_inc(v_pre_743_);
lean_inc_ref(v_matchUsingNamespace_732_);
lean_inc(v_a_741_);
lean_inc_ref(v_a_740_);
lean_inc(v_a_739_);
lean_inc_ref(v_a_738_);
lean_inc_ref(v_a_737_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
v___x_744_ = lean_apply_10(v_matchUsingNamespace_732_, v_ns_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, lean_box(0));
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
if (lean_obj_tag(v_a_745_) == 0)
{
lean_dec_ref_known(v_a_745_, 1);
lean_dec(v_pre_743_);
lean_dec_ref(v_matchUsingNamespace_732_);
return v___x_744_;
}
else
{
lean_object* v_a_746_; lean_object* v_snd_747_; 
lean_dec_ref_known(v___x_744_, 1);
v_a_746_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v_a_745_, 1);
v_snd_747_ = lean_ctor_get(v_a_746_, 1);
lean_inc(v_snd_747_);
lean_dec(v_a_746_);
v_ns_733_ = v_pre_743_;
v_a_734_ = v_snd_747_;
goto _start;
}
}
else
{
lean_dec(v_pre_743_);
lean_dec_ref(v_matchUsingNamespace_732_);
return v___x_744_;
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v_ns_733_);
lean_dec_ref(v_matchUsingNamespace_732_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_a_734_);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces___boxed(lean_object* v_matchUsingNamespace_753_, lean_object* v_ns_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_753_, v_ns_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(lean_object* v_id_765_, uint8_t v_danglingDot_766_, lean_object* v_declName_767_, lean_object* v_ns_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_800_; 
v___x_778_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_768_, v_id_765_, v_danglingDot_766_, v_declName_767_, v___y_776_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_800_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_800_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_800_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
if (lean_obj_tag(v_a_779_) == 1)
{
lean_object* v_val_783_; lean_object* v___x_784_; lean_object* v___y_786_; 
v_val_783_ = lean_ctor_get(v_a_779_, 0);
v___x_784_ = lean_box(0);
if (lean_obj_tag(v___y_769_) == 0)
{
v___y_786_ = v_a_779_;
goto v___jp_785_;
}
else
{
lean_object* v_val_792_; uint8_t v___x_793_; 
v_val_792_ = lean_ctor_get(v___y_769_, 0);
v___x_793_ = l_Lean_Name_isSuffixOf(v_val_783_, v_val_792_);
if (v___x_793_ == 0)
{
lean_dec_ref_known(v_a_779_, 1);
v___y_786_ = v___y_769_;
goto v___jp_785_;
}
else
{
lean_dec_ref_known(v___y_769_, 1);
v___y_786_ = v_a_779_;
goto v___jp_785_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_784_);
lean_ctor_set(v___x_787_, 1, v___y_786_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_788_);
v___x_790_ = v___x_781_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v_a_779_);
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___y_769_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_796_);
v___x_798_ = v___x_781_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed(lean_object* v_id_801_, lean_object* v_danglingDot_802_, lean_object* v_declName_803_, lean_object* v_ns_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v_danglingDot_boxed_814_; lean_object* v_res_815_; 
v_danglingDot_boxed_814_ = lean_unbox(v_danglingDot_802_);
v_res_815_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_801_, v_danglingDot_boxed_814_, v_declName_803_, v_ns_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v_ns_804_);
lean_dec(v_id_801_);
return v_res_815_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; uint8_t v___x_821_; 
v_head_819_ = lean_ctor_get(v_x_817_, 0);
v_tail_820_ = lean_ctor_get(v_x_817_, 1);
v___x_821_ = lean_name_eq(v_a_816_, v_head_819_);
if (v___x_821_ == 0)
{
v_x_817_ = v_tail_820_;
goto _start;
}
else
{
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0___boxed(lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_a_823_, v_x_824_);
lean_dec(v_x_824_);
lean_dec(v_a_823_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(lean_object* v_declName_827_, lean_object* v_id_828_, uint8_t v_danglingDot_829_, lean_object* v_as_x27_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
if (lean_obj_tag(v_as_x27_830_) == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_declName_827_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_b_831_);
lean_ctor_set(v___x_835_, 1, v___y_832_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v_head_838_; lean_object* v_tail_839_; lean_object* v___x_840_; 
v_head_838_ = lean_ctor_get(v_as_x27_830_, 0);
v_tail_839_ = lean_ctor_get(v_as_x27_830_, 1);
v___x_840_ = lean_box(0);
if (lean_obj_tag(v_head_838_) == 0)
{
lean_object* v_ns_841_; lean_object* v_except_842_; uint8_t v___x_843_; 
v_ns_841_ = lean_ctor_get(v_head_838_, 0);
v_except_842_ = lean_ctor_get(v_head_838_, 1);
v___x_843_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_827_, v_except_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v_a_845_; 
lean_inc(v_declName_827_);
v___x_844_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_841_, v_id_828_, v_danglingDot_829_, v_declName_827_, v___y_833_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_844_);
if (lean_obj_tag(v_a_845_) == 1)
{
if (lean_obj_tag(v___y_832_) == 0)
{
v_as_x27_830_ = v_tail_839_;
v_b_831_ = v___x_840_;
v___y_832_ = v_a_845_;
goto _start;
}
else
{
lean_object* v_val_847_; lean_object* v_val_848_; uint8_t v___x_849_; 
v_val_847_ = lean_ctor_get(v_a_845_, 0);
v_val_848_ = lean_ctor_get(v___y_832_, 0);
v___x_849_ = l_Lean_Name_isSuffixOf(v_val_847_, v_val_848_);
if (v___x_849_ == 0)
{
lean_dec_ref_known(v_a_845_, 1);
v_as_x27_830_ = v_tail_839_;
v_b_831_ = v___x_840_;
goto _start;
}
else
{
lean_dec_ref_known(v___y_832_, 1);
v_as_x27_830_ = v_tail_839_;
v_b_831_ = v___x_840_;
v___y_832_ = v_a_845_;
goto _start;
}
}
}
else
{
lean_dec(v_a_845_);
v_as_x27_830_ = v_tail_839_;
v_b_831_ = v___x_840_;
goto _start;
}
}
else
{
v_as_x27_830_ = v_tail_839_;
v_b_831_ = v___x_840_;
goto _start;
}
}
else
{
v_as_x27_830_ = v_tail_839_;
v_b_831_ = v___x_840_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_declName_855_, lean_object* v_id_856_, lean_object* v_danglingDot_857_, lean_object* v_as_x27_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
uint8_t v_danglingDot_boxed_863_; lean_object* v_res_864_; 
v_danglingDot_boxed_863_ = lean_unbox(v_danglingDot_857_);
v_res_864_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_855_, v_id_856_, v_danglingDot_boxed_863_, v_as_x27_858_, v_b_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec(v_as_x27_858_);
lean_dec(v_id_856_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(lean_object* v_declName_865_, lean_object* v_id_866_, uint8_t v_danglingDot_867_, lean_object* v_as_868_, lean_object* v_as_x27_869_, lean_object* v_b_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
if (lean_obj_tag(v_as_x27_869_) == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v_declName_865_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_b_870_);
lean_ctor_set(v___x_880_, 1, v___y_871_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; lean_object* v___x_885_; 
v_head_883_ = lean_ctor_get(v_as_x27_869_, 0);
v_tail_884_ = lean_ctor_get(v_as_x27_869_, 1);
v___x_885_ = lean_box(0);
if (lean_obj_tag(v_head_883_) == 0)
{
lean_object* v_ns_886_; lean_object* v_except_887_; uint8_t v___x_888_; 
v_ns_886_ = lean_ctor_get(v_head_883_, 0);
v_except_887_ = lean_ctor_get(v_head_883_, 1);
v___x_888_ = l_List_elem___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__0(v_declName_865_, v_except_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v_a_890_; 
lean_inc(v_declName_865_);
v___x_889_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v_ns_886_, v_id_866_, v_danglingDot_867_, v_declName_865_, v___y_878_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
if (lean_obj_tag(v_a_890_) == 1)
{
if (lean_obj_tag(v___y_871_) == 0)
{
lean_object* v___x_891_; 
v___x_891_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_865_, v_id_866_, v_danglingDot_867_, v_tail_884_, v___x_885_, v_a_890_, v___y_878_);
return v___x_891_;
}
else
{
lean_object* v_val_892_; lean_object* v_val_893_; uint8_t v___x_894_; 
v_val_892_ = lean_ctor_get(v_a_890_, 0);
v_val_893_ = lean_ctor_get(v___y_871_, 0);
v___x_894_ = l_Lean_Name_isSuffixOf(v_val_892_, v_val_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec_ref_known(v_a_890_, 1);
v___x_895_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_865_, v_id_866_, v_danglingDot_867_, v_tail_884_, v___x_885_, v___y_871_, v___y_878_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
lean_dec_ref_known(v___y_871_, 1);
v___x_896_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_865_, v_id_866_, v_danglingDot_867_, v_tail_884_, v___x_885_, v_a_890_, v___y_878_);
return v___x_896_;
}
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v_a_890_);
v___x_897_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_865_, v_id_866_, v_danglingDot_867_, v_tail_884_, v___x_885_, v___y_871_, v___y_878_);
return v___x_897_;
}
}
else
{
lean_object* v___x_898_; 
v___x_898_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_865_, v_id_866_, v_danglingDot_867_, v_tail_884_, v___x_885_, v___y_871_, v___y_878_);
return v___x_898_;
}
}
else
{
lean_object* v___x_899_; 
v___x_899_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_865_, v_id_866_, v_danglingDot_867_, v_tail_884_, v___x_885_, v___y_871_, v___y_878_);
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg___boxed(lean_object* v_declName_900_, lean_object* v_id_901_, lean_object* v_danglingDot_902_, lean_object* v_as_903_, lean_object* v_as_x27_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
uint8_t v_danglingDot_boxed_915_; lean_object* v_res_916_; 
v_danglingDot_boxed_915_ = lean_unbox(v_danglingDot_902_);
v_res_916_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_900_, v_id_901_, v_danglingDot_boxed_915_, v_as_903_, v_as_x27_904_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v_as_x27_904_);
lean_dec(v_as_903_);
lean_dec(v_id_901_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(lean_object* v_ctx_917_, lean_object* v_declName_918_, lean_object* v_id_919_, uint8_t v_danglingDot_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___y_930_; lean_object* v_toCommandContextInfo_967_; lean_object* v_currNamespace_968_; lean_object* v_openDecls_969_; lean_object* v___x_970_; lean_object* v_matchUsingNamespace_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_toCommandContextInfo_967_ = lean_ctor_get(v_ctx_917_, 0);
lean_inc_ref(v_toCommandContextInfo_967_);
lean_dec_ref(v_ctx_917_);
v_currNamespace_968_ = lean_ctor_get(v_toCommandContextInfo_967_, 5);
lean_inc(v_currNamespace_968_);
v_openDecls_969_ = lean_ctor_get(v_toCommandContextInfo_967_, 6);
lean_inc(v_openDecls_969_);
lean_dec_ref(v_toCommandContextInfo_967_);
v___x_970_ = lean_box(v_danglingDot_920_);
lean_inc(v_declName_918_);
lean_inc(v_id_919_);
v_matchUsingNamespace_971_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v_matchUsingNamespace_971_, 0, v_id_919_);
lean_closure_set(v_matchUsingNamespace_971_, 1, v___x_970_);
lean_closure_set(v_matchUsingNamespace_971_, 2, v_declName_918_);
v___x_972_ = lean_box(0);
v___x_973_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_visitNamespaces(v_matchUsingNamespace_971_, v_currNamespace_968_, v___x_972_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
if (lean_obj_tag(v_a_974_) == 0)
{
lean_dec_ref_known(v_a_974_, 1);
lean_dec(v_openDecls_969_);
lean_dec(v_id_919_);
lean_dec(v_declName_918_);
v___y_930_ = v___x_973_;
goto v___jp_929_;
}
else
{
lean_object* v_a_975_; lean_object* v_snd_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec_ref_known(v___x_973_, 1);
v_a_975_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v_a_974_, 1);
v_snd_976_ = lean_ctor_get(v_a_975_, 1);
lean_inc(v_snd_976_);
lean_dec(v_a_975_);
v___x_977_ = lean_box(0);
lean_inc(v_declName_918_);
v___x_978_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_918_, v_id_919_, v_danglingDot_920_, v_openDecls_969_, v_openDecls_969_, v___x_977_, v_snd_976_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_openDecls_969_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v_snd_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v_a_980_ = lean_ctor_get(v_a_979_, 0);
lean_inc(v_a_980_);
lean_dec(v_a_979_);
v_snd_981_ = lean_ctor_get(v_a_980_, 1);
lean_inc(v_snd_981_);
lean_dec(v_a_980_);
v___x_982_ = lean_box(0);
v___x_983_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___lam__0(v_id_919_, v_danglingDot_920_, v_declName_918_, v___x_982_, v_snd_981_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_id_919_);
v___y_930_ = v___x_983_;
goto v___jp_929_;
}
else
{
lean_dec(v_id_919_);
lean_dec(v_declName_918_);
v___y_930_ = v___x_978_;
goto v___jp_929_;
}
}
}
else
{
lean_dec(v_openDecls_969_);
lean_dec(v_id_919_);
lean_dec(v_declName_918_);
v___y_930_ = v___x_973_;
goto v___jp_929_;
}
v___jp_929_:
{
if (lean_obj_tag(v___y_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_958_; 
v_a_931_ = lean_ctor_get(v___y_930_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___y_930_);
if (v_isSharedCheck_958_ == 0)
{
v___x_933_ = v___y_930_;
v_isShared_934_ = v_isSharedCheck_958_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___y_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_958_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
v_a_935_ = lean_ctor_get(v_a_931_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_945_ == 0)
{
v___x_937_ = v_a_931_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v_a_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_940_);
v___x_942_ = v___x_933_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v_a_931_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_957_ == 0)
{
v___x_948_ = v_a_931_;
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v_a_931_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_snd_950_; lean_object* v___x_952_; 
v_snd_950_ = lean_ctor_get(v_a_946_, 1);
lean_inc(v_snd_950_);
lean_dec(v_a_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_snd_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_snd_950_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_952_);
v___x_954_ = v___x_933_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___y_930_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___y_930_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___y_930_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___y_930_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f___boxed(lean_object* v_ctx_984_, lean_object* v_declName_985_, lean_object* v_id_986_, lean_object* v_danglingDot_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
uint8_t v_danglingDot_boxed_996_; lean_object* v_res_997_; 
v_danglingDot_boxed_996_ = lean_unbox(v_danglingDot_987_);
v_res_997_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_984_, v_declName_985_, v_id_986_, v_danglingDot_boxed_996_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(lean_object* v_declName_998_, lean_object* v_id_999_, uint8_t v_danglingDot_1000_, lean_object* v_as_1001_, lean_object* v_as_x27_1002_, lean_object* v_b_1003_, lean_object* v_a_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___redArg(v_declName_998_, v_id_999_, v_danglingDot_1000_, v_as_1001_, v_as_x27_1002_, v_b_1003_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1___boxed(lean_object* v_declName_1015_, lean_object* v_id_1016_, lean_object* v_danglingDot_1017_, lean_object* v_as_1018_, lean_object* v_as_x27_1019_, lean_object* v_b_1020_, lean_object* v_a_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_danglingDot_boxed_1031_; lean_object* v_res_1032_; 
v_danglingDot_boxed_1031_ = lean_unbox(v_danglingDot_1017_);
v_res_1032_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1(v_declName_1015_, v_id_1016_, v_danglingDot_boxed_1031_, v_as_1018_, v_as_x27_1019_, v_b_1020_, v_a_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v_as_x27_1019_);
lean_dec(v_as_1018_);
lean_dec(v_id_1016_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(lean_object* v_declName_1033_, lean_object* v_id_1034_, uint8_t v_danglingDot_1035_, lean_object* v_as_1036_, lean_object* v_as_x27_1037_, lean_object* v_b_1038_, lean_object* v_a_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___redArg(v_declName_1033_, v_id_1034_, v_danglingDot_1035_, v_as_x27_1037_, v_b_1038_, v___y_1040_, v___y_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1___boxed(lean_object* v_declName_1050_, lean_object* v_id_1051_, lean_object* v_danglingDot_1052_, lean_object* v_as_1053_, lean_object* v_as_x27_1054_, lean_object* v_b_1055_, lean_object* v_a_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_danglingDot_boxed_1066_; lean_object* v_res_1067_; 
v_danglingDot_boxed_1066_ = lean_unbox(v_danglingDot_1052_);
v_res_1067_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f_spec__1_spec__1(v_declName_1050_, v_id_1051_, v_danglingDot_boxed_1066_, v_as_1053_, v_as_x27_1054_, v_b_1055_, v_a_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v_as_x27_1054_);
lean_dec(v_as_1053_);
lean_dec(v_id_1051_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(lean_object* v_ctx_1068_, lean_object* v_id_1069_, uint8_t v_danglingDot_1070_, lean_object* v___x_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_it_1083_; lean_object* v_a_1087_; lean_object* v___x_1090_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v_it_1115_; lean_object* v_fst_1116_; lean_object* v_it_1121_; lean_object* v_fst_1122_; 
v___x_1090_ = lean_box(0);
if (lean_obj_tag(v_a_1072_) == 0)
{
lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1192_; 
v_a_1124_ = lean_ctor_get(v_a_1072_, 0);
v_a_1125_ = lean_ctor_get(v_a_1072_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_a_1072_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1127_ = v_a_1072_;
v_isShared_1128_ = v_isSharedCheck_1192_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_inc(v_a_1124_);
lean_dec(v_a_1072_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1192_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_it_1130_; lean_object* v_it_u2082_1135_; 
v_it_u2082_1135_ = lean_ctor_get(v_a_1124_, 1);
lean_inc(v_it_u2082_1135_);
if (lean_obj_tag(v_it_u2082_1135_) == 0)
{
lean_object* v_it_u2081_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1160_; 
v_it_u2081_1136_ = lean_ctor_get(v_a_1124_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_a_1124_, 1);
lean_dec(v_unused_1161_);
v___x_1138_ = v_a_1124_;
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_it_u2081_1136_);
lean_dec(v_a_1124_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_array_1140_; lean_object* v_pos_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1159_; 
v_array_1140_ = lean_ctor_get(v_it_u2081_1136_, 0);
v_pos_1141_ = lean_ctor_get(v_it_u2081_1136_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_it_u2081_1136_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1143_ = v_it_u2081_1136_;
v_isShared_1144_ = v_isSharedCheck_1159_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_pos_1141_);
lean_inc(v_array_1140_);
lean_dec(v_it_u2081_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1159_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_array_1140_);
v___x_1146_ = lean_nat_dec_lt(v_pos_1141_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_del_object(v___x_1143_);
lean_dec(v_pos_1141_);
lean_dec_ref(v_array_1140_);
lean_del_object(v___x_1138_);
lean_del_object(v___x_1127_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1125_);
v_a_1072_ = v___x_1147_;
goto _start;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_add(v_pos_1141_, v___x_1149_);
lean_inc_ref(v_array_1140_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1150_);
v___x_1152_ = v___x_1143_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_array_1140_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_array_fget(v_array_1140_, v_pos_1141_);
lean_dec(v_pos_1141_);
lean_dec_ref(v_array_1140_);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1154_);
lean_ctor_set(v___x_1138_, 0, v___x_1152_);
v___x_1156_ = v___x_1138_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
v_it_1130_ = v___x_1156_;
goto v___jp_1129_;
}
}
}
}
}
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1191_; 
v_val_1162_ = lean_ctor_get(v_it_u2082_1135_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_it_u2082_1135_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1164_ = v_it_u2082_1135_;
v_isShared_1165_ = v_isSharedCheck_1191_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_val_1162_);
lean_dec(v_it_u2082_1135_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1191_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
if (lean_obj_tag(v_val_1162_) == 0)
{
lean_object* v_it_u2081_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_del_object(v___x_1164_);
v_it_u2081_1166_ = lean_ctor_get(v_a_1124_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_a_1124_, 1);
lean_dec(v_unused_1175_);
v___x_1168_ = v_a_1124_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_it_u2081_1166_);
lean_dec(v_a_1124_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_box(0);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_it_u2081_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v_it_1130_ = v___x_1172_;
goto v___jp_1129_;
}
}
}
else
{
lean_object* v_it_u2081_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1189_; 
lean_del_object(v___x_1127_);
v_it_u2081_1176_ = lean_ctor_get(v_a_1124_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_a_1124_, 1);
lean_dec(v_unused_1190_);
v___x_1178_ = v_a_1124_;
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_it_u2081_1176_);
lean_dec(v_a_1124_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_key_1180_; lean_object* v_tail_1181_; lean_object* v___x_1183_; 
v_key_1180_ = lean_ctor_get(v_val_1162_, 0);
lean_inc(v_key_1180_);
v_tail_1181_ = lean_ctor_get(v_val_1162_, 2);
lean_inc(v_tail_1181_);
lean_dec_ref_known(v_val_1162_, 3);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_tail_1181_);
v___x_1183_ = v___x_1164_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_tail_1181_);
v___x_1183_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1183_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_it_u2081_1176_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_a_1125_);
v_it_1115_ = v___x_1186_;
v_fst_1116_ = v_key_1180_;
goto v___jp_1114_;
}
}
}
}
}
}
v___jp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_it_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_it_1130_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_a_1125_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v_a_1072_ = v___x_1132_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1193_; 
v_a_1193_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v_a_1072_, 1);
switch(lean_obj_tag(v_a_1193_))
{
case 0:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v___x_1071_);
lean_dec(v_id_1069_);
lean_dec_ref(v_ctx_1068_);
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_b_1073_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
case 1:
{
lean_object* v_a_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1215_; 
v_a_1196_ = lean_ctor_get(v_a_1193_, 0);
v_a_1197_ = lean_ctor_get(v_a_1193_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1199_ = v_a_1193_;
v_isShared_1200_ = v_isSharedCheck_1215_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
lean_dec(v_a_1193_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1215_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_start_1201_; lean_object* v_stop_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_start_1201_ = lean_ctor_get(v_a_1196_, 1);
v_stop_1202_ = lean_ctor_get(v_a_1196_, 2);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_nat_sub(v_stop_1202_, v_start_1201_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
lean_dec(v___x_1204_);
if (v___x_1205_ == 0)
{
lean_del_object(v___x_1199_);
lean_dec_ref(v_a_1196_);
v_it_1083_ = v_a_1197_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_z_1209_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_1196_);
v___x_1207_ = l_Subarray_drop___redArg(v_a_1196_, v___x_1206_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1207_);
v_z_1209_ = v___x_1199_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_a_1197_);
v_z_1209_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Subarray_get___redArg(v_a_1196_, v___x_1203_);
lean_dec_ref(v_a_1196_);
switch(lean_obj_tag(v___x_1210_))
{
case 0:
{
lean_object* v_key_1211_; 
v_key_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_key_1211_);
lean_dec_ref_known(v___x_1210_, 2);
v_it_1121_ = v_z_1209_;
v_fst_1122_ = v_key_1211_;
goto v___jp_1120_;
}
case 1:
{
lean_object* v_node_1212_; lean_object* v___x_1213_; 
v_node_1212_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_node_1212_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1213_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1212_, v_z_1209_);
v_it_1083_ = v___x_1213_;
goto v___jp_1082_;
}
default: 
{
v_it_1083_ = v_z_1209_;
goto v___jp_1082_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_1216_; lean_object* v_keys_1217_; lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1234_; 
v_vals_1216_ = lean_ctor_get(v_a_1193_, 1);
v_keys_1217_ = lean_ctor_get(v_a_1193_, 0);
v_a_1218_ = lean_ctor_get(v_a_1193_, 2);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1220_ = v_a_1193_;
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_inc(v_vals_1216_);
lean_inc(v_keys_1217_);
lean_dec(v_a_1193_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_start_1222_; lean_object* v_stop_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_start_1222_ = lean_ctor_get(v_vals_1216_, 1);
v_stop_1223_ = lean_ctor_get(v_vals_1216_, 2);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_nat_sub(v_stop_1223_, v_start_1222_);
v___x_1226_ = lean_nat_dec_lt(v___x_1224_, v___x_1225_);
lean_dec(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec_ref(v_keys_1217_);
lean_dec_ref(v_vals_1216_);
v_it_1083_ = v_a_1218_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1227_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_1217_);
v___x_1228_ = l_Subarray_drop___redArg(v_keys_1217_, v___x_1227_);
v___x_1229_ = l_Subarray_drop___redArg(v_vals_1216_, v___x_1227_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1229_);
lean_ctor_set(v___x_1220_, 0, v___x_1228_);
v___x_1231_ = v___x_1220_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_a_1218_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Subarray_get___redArg(v_keys_1217_, v___x_1224_);
lean_dec_ref(v_keys_1217_);
v_it_1121_ = v___x_1231_;
v_fst_1122_ = v___x_1232_;
goto v___jp_1120_;
}
}
}
}
}
}
v___jp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_it_1083_);
v_a_1072_ = v___x_1084_;
goto _start;
}
v___jp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_a_1087_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
v___jp_1091_:
{
if (v___y_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_inc(v_id_1069_);
lean_inc_ref(v_ctx_1068_);
v___x_1095_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_1068_, v___y_1093_, v_id_1069_, v_danglingDot_1070_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
if (lean_obj_tag(v_a_1096_) == 0)
{
lean_object* v_a_1097_; 
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___x_1071_);
lean_dec(v_id_1069_);
lean_dec_ref(v_ctx_1068_);
v_a_1097_ = lean_ctor_get(v_a_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v_a_1096_, 1);
v_a_1087_ = v_a_1097_;
goto v___jp_1086_;
}
else
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v_a_1096_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_a_1096_, 1);
if (lean_obj_tag(v_a_1098_) == 1)
{
lean_object* v_val_1099_; lean_object* v___x_1100_; 
v_val_1099_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v_a_1098_, 1);
v___x_1100_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg(v_val_1099_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
if (lean_obj_tag(v_a_1101_) == 0)
{
lean_object* v_a_1102_; 
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___x_1071_);
lean_dec(v_id_1069_);
lean_dec_ref(v_ctx_1068_);
v_a_1102_ = lean_ctor_get(v_a_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v_a_1101_, 1);
v_a_1087_ = v_a_1102_;
goto v___jp_1086_;
}
else
{
lean_dec_ref_known(v_a_1101_, 1);
v_a_1072_ = v___y_1092_;
v_b_1073_ = v___x_1090_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___x_1071_);
lean_dec(v_id_1069_);
lean_dec_ref(v_ctx_1068_);
return v___x_1100_;
}
}
else
{
lean_dec(v_a_1098_);
v_a_1072_ = v___y_1092_;
v_b_1073_ = v___x_1090_;
goto _start;
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___x_1071_);
lean_dec(v_id_1069_);
lean_dec_ref(v_ctx_1068_);
v_a_1105_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1095_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1095_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_dec(v___y_1093_);
v_a_1072_ = v___y_1092_;
v_b_1073_ = v___x_1090_;
goto _start;
}
}
v___jp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Lean_Name_isInternal(v_fst_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 1;
lean_inc(v_fst_1116_);
lean_inc_ref(v___x_1071_);
v___x_1119_ = l_Lean_Environment_contains(v___x_1071_, v_fst_1116_, v___x_1118_);
v___y_1092_ = v_it_1115_;
v___y_1093_ = v_fst_1116_;
v___y_1094_ = v___x_1119_;
goto v___jp_1091_;
}
else
{
v___y_1092_ = v_it_1115_;
v___y_1093_ = v_fst_1116_;
v___y_1094_ = v___x_1117_;
goto v___jp_1091_;
}
}
v___jp_1120_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_it_1121_);
v_it_1115_ = v___x_1123_;
v_fst_1116_ = v_fst_1122_;
goto v___jp_1114_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg___boxed(lean_object* v_ctx_1235_, lean_object* v_id_1236_, lean_object* v_danglingDot_1237_, lean_object* v___x_1238_, lean_object* v_a_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v_danglingDot_boxed_1249_; lean_object* v_res_1250_; 
v_danglingDot_boxed_1249_ = lean_unbox(v_danglingDot_1237_);
v_res_1250_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1235_, v_id_1236_, v_danglingDot_boxed_1249_, v___x_1238_, v_a_1239_, v_b_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(lean_object* v_ctx_1251_, lean_object* v_id_1252_, uint8_t v_danglingDot_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_env_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1262_ = lean_st_ref_get(v_a_1260_);
v_env_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref_n(v_env_1263_, 2);
lean_dec(v___x_1262_);
v___x_1264_ = l_Lean_Environment_getNamespaces(v_env_1263_);
v___x_1265_ = lean_box(0);
v___x_1266_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1251_, v_id_1252_, v_danglingDot_1253_, v_env_1263_, v___x_1264_, v___x_1265_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
if (lean_obj_tag(v_a_1267_) == 0)
{
lean_dec_ref_known(v_a_1267_, 1);
return v___x_1266_;
}
else
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref_known(v_a_1267_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1276_);
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces___boxed(lean_object* v_ctx_1277_, lean_object* v_id_1278_, lean_object* v_danglingDot_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v_danglingDot_boxed_1288_; lean_object* v_res_1289_; 
v_danglingDot_boxed_1288_ = lean_unbox(v_danglingDot_1279_);
v_res_1289_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_1277_, v_id_1278_, v_danglingDot_boxed_1288_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(lean_object* v_ctx_1290_, lean_object* v_id_1291_, uint8_t v_danglingDot_1292_, lean_object* v___x_1293_, lean_object* v_inst_1294_, lean_object* v_R_1295_, lean_object* v_a_1296_, lean_object* v_b_1297_, lean_object* v_c_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___redArg(v_ctx_1290_, v_id_1291_, v_danglingDot_1292_, v___x_1293_, v_a_1296_, v_b_1297_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0___boxed(lean_object** _args){
lean_object* v_ctx_1308_ = _args[0];
lean_object* v_id_1309_ = _args[1];
lean_object* v_danglingDot_1310_ = _args[2];
lean_object* v___x_1311_ = _args[3];
lean_object* v_inst_1312_ = _args[4];
lean_object* v_R_1313_ = _args[5];
lean_object* v_a_1314_ = _args[6];
lean_object* v_b_1315_ = _args[7];
lean_object* v_c_1316_ = _args[8];
lean_object* v___y_1317_ = _args[9];
lean_object* v___y_1318_ = _args[10];
lean_object* v___y_1319_ = _args[11];
lean_object* v___y_1320_ = _args[12];
lean_object* v___y_1321_ = _args[13];
lean_object* v___y_1322_ = _args[14];
lean_object* v___y_1323_ = _args[15];
lean_object* v___y_1324_ = _args[16];
_start:
{
uint8_t v_danglingDot_boxed_1325_; lean_object* v_res_1326_; 
v_danglingDot_boxed_1325_ = lean_unbox(v_danglingDot_1310_);
v_res_1326_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces_spec__0(v_ctx_1308_, v_id_1309_, v_danglingDot_boxed_1325_, v___x_1311_, v_inst_1312_, v_R_1313_, v_a_1314_, v_b_1315_, v_c_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* v_n_1327_){
_start:
{
if (lean_obj_tag(v_n_1327_) == 2)
{
lean_object* v_i_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_i_1328_ = lean_ctor_get(v_n_1327_, 1);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_nat_dec_eq(v_i_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_inc_ref(v_n_1327_);
return v_n_1327_;
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_isPrivatePrefix(v_n_1327_);
if (v___x_1331_ == 0)
{
lean_inc_ref(v_n_1327_);
return v_n_1327_;
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
}
}
else
{
lean_inc(v_n_1327_);
return v_n_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* v_n_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_1333_);
lean_dec(v_n_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* v_n_u2081_1335_, lean_object* v_n_u2082_1336_){
_start:
{
lean_object* v_n_u2081_1337_; lean_object* v_n_u2082_1338_; 
v_n_u2081_1337_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2081_1335_);
lean_dec(v_n_u2081_1335_);
v_n_u2082_1338_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(v_n_u2082_1336_);
lean_dec(v_n_u2082_1336_);
switch(lean_obj_tag(v_n_u2081_1337_))
{
case 0:
{
if (lean_obj_tag(v_n_u2082_1338_) == 0)
{
uint8_t v___x_1339_; 
v___x_1339_ = 1;
return v___x_1339_;
}
else
{
uint8_t v___x_1340_; 
lean_dec(v_n_u2082_1338_);
v___x_1340_ = 0;
return v___x_1340_;
}
}
case 1:
{
if (lean_obj_tag(v_n_u2082_1338_) == 1)
{
lean_object* v_pre_1341_; lean_object* v_str_1342_; lean_object* v_pre_1343_; lean_object* v_str_1344_; uint8_t v___x_1345_; 
v_pre_1341_ = lean_ctor_get(v_n_u2081_1337_, 0);
lean_inc(v_pre_1341_);
v_str_1342_ = lean_ctor_get(v_n_u2081_1337_, 1);
lean_inc_ref(v_str_1342_);
lean_dec_ref_known(v_n_u2081_1337_, 2);
v_pre_1343_ = lean_ctor_get(v_n_u2082_1338_, 0);
lean_inc(v_pre_1343_);
v_str_1344_ = lean_ctor_get(v_n_u2082_1338_, 1);
lean_inc_ref(v_str_1344_);
lean_dec_ref_known(v_n_u2082_1338_, 2);
v___x_1345_ = lean_string_compare(v_str_1342_, v_str_1344_);
lean_dec_ref(v_str_1344_);
lean_dec_ref(v_str_1342_);
if (v___x_1345_ == 1)
{
v_n_u2081_1335_ = v_pre_1341_;
v_n_u2082_1336_ = v_pre_1343_;
goto _start;
}
else
{
lean_dec(v_pre_1343_);
lean_dec(v_pre_1341_);
return v___x_1345_;
}
}
else
{
uint8_t v___x_1347_; 
lean_dec_ref_known(v_n_u2081_1337_, 2);
lean_dec(v_n_u2082_1338_);
v___x_1347_ = 2;
return v___x_1347_;
}
}
default: 
{
switch(lean_obj_tag(v_n_u2082_1338_))
{
case 0:
{
uint8_t v___x_1348_; 
lean_dec_ref_known(v_n_u2081_1337_, 2);
v___x_1348_ = 2;
return v___x_1348_;
}
case 1:
{
uint8_t v___x_1349_; 
lean_dec_ref_known(v_n_u2082_1338_, 2);
lean_dec_ref_known(v_n_u2081_1337_, 2);
v___x_1349_ = 0;
return v___x_1349_;
}
default: 
{
lean_object* v_pre_1350_; lean_object* v_i_1351_; lean_object* v_pre_1352_; lean_object* v_i_1353_; uint8_t v___x_1354_; 
v_pre_1350_ = lean_ctor_get(v_n_u2081_1337_, 0);
lean_inc(v_pre_1350_);
v_i_1351_ = lean_ctor_get(v_n_u2081_1337_, 1);
lean_inc(v_i_1351_);
lean_dec_ref_known(v_n_u2081_1337_, 2);
v_pre_1352_ = lean_ctor_get(v_n_u2082_1338_, 0);
lean_inc(v_pre_1352_);
v_i_1353_ = lean_ctor_get(v_n_u2082_1338_, 1);
lean_inc(v_i_1353_);
lean_dec_ref_known(v_n_u2082_1338_, 2);
v___x_1354_ = lean_nat_dec_lt(v_i_1351_, v_i_1353_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_nat_dec_eq(v_i_1351_, v_i_1353_);
lean_dec(v_i_1353_);
lean_dec(v_i_1351_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
lean_dec(v_pre_1352_);
lean_dec(v_pre_1350_);
v___x_1356_ = 2;
return v___x_1356_;
}
else
{
v_n_u2081_1335_ = v_pre_1350_;
v_n_u2082_1336_ = v_pre_1352_;
goto _start;
}
}
else
{
uint8_t v___x_1358_; 
lean_dec(v_i_1353_);
lean_dec(v_pre_1352_);
lean_dec(v_i_1351_);
lean_dec(v_pre_1350_);
v___x_1358_ = 0;
return v___x_1358_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* v_n_u2081_1359_, lean_object* v_n_u2082_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_n_u2081_1359_, v_n_u2082_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(lean_object* v_names_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___closed__0));
v___x_1366_ = l_Std_TreeSet_ofArray___redArg(v_names_1364_, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray___boxed(lean_object* v_names_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_names_1367_);
lean_dec_ref(v_names_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(lean_object* v_k_1369_, lean_object* v_t_1370_){
_start:
{
if (lean_obj_tag(v_t_1370_) == 0)
{
lean_object* v_k_1371_; lean_object* v_l_1372_; lean_object* v_r_1373_; uint8_t v___x_1374_; 
v_k_1371_ = lean_ctor_get(v_t_1370_, 1);
lean_inc(v_k_1371_);
v_l_1372_ = lean_ctor_get(v_t_1370_, 3);
lean_inc(v_l_1372_);
v_r_1373_ = lean_ctor_get(v_t_1370_, 4);
lean_inc(v_r_1373_);
lean_dec_ref_known(v_t_1370_, 5);
lean_inc(v_k_1369_);
v___x_1374_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1369_, v_k_1371_);
switch(v___x_1374_)
{
case 0:
{
lean_dec(v_r_1373_);
v_t_1370_ = v_l_1372_;
goto _start;
}
case 1:
{
uint8_t v___x_1376_; 
lean_dec(v_r_1373_);
lean_dec(v_l_1372_);
lean_dec(v_k_1369_);
v___x_1376_ = 1;
return v___x_1376_;
}
default: 
{
lean_dec(v_l_1372_);
v_t_1370_ = v_r_1373_;
goto _start;
}
}
}
else
{
uint8_t v___x_1378_; 
lean_dec(v_k_1369_);
v___x_1378_ = 0;
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg___boxed(lean_object* v_k_1379_, lean_object* v_t_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1379_, v_t_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(lean_object* v_k_1383_, lean_object* v_v_1384_, lean_object* v_t_1385_){
_start:
{
if (lean_obj_tag(v_t_1385_) == 0)
{
lean_object* v_size_1386_; lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v_l_1389_; lean_object* v_r_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1670_; 
v_size_1386_ = lean_ctor_get(v_t_1385_, 0);
v_k_1387_ = lean_ctor_get(v_t_1385_, 1);
v_v_1388_ = lean_ctor_get(v_t_1385_, 2);
v_l_1389_ = lean_ctor_get(v_t_1385_, 3);
v_r_1390_ = lean_ctor_get(v_t_1385_, 4);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_t_1385_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1392_ = v_t_1385_;
v_isShared_1393_ = v_isSharedCheck_1670_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_r_1390_);
lean_inc(v_l_1389_);
lean_inc(v_v_1388_);
lean_inc(v_k_1387_);
lean_inc(v_size_1386_);
lean_dec(v_t_1385_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1670_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
uint8_t v___x_1394_; 
lean_inc(v_k_1387_);
lean_inc(v_k_1383_);
v___x_1394_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(v_k_1383_, v_k_1387_);
switch(v___x_1394_)
{
case 0:
{
lean_object* v_impl_1395_; lean_object* v___x_1396_; 
lean_dec(v_size_1386_);
v_impl_1395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1383_, v_v_1384_, v_l_1389_);
v___x_1396_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1390_) == 0)
{
lean_object* v_size_1397_; lean_object* v_size_1398_; lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_size_1397_ = lean_ctor_get(v_r_1390_, 0);
v_size_1398_ = lean_ctor_get(v_impl_1395_, 0);
lean_inc(v_size_1398_);
v_k_1399_ = lean_ctor_get(v_impl_1395_, 1);
lean_inc(v_k_1399_);
v_v_1400_ = lean_ctor_get(v_impl_1395_, 2);
lean_inc(v_v_1400_);
v_l_1401_ = lean_ctor_get(v_impl_1395_, 3);
lean_inc(v_l_1401_);
v_r_1402_ = lean_ctor_get(v_impl_1395_, 4);
lean_inc(v_r_1402_);
v___x_1403_ = lean_unsigned_to_nat(3u);
v___x_1404_ = lean_nat_mul(v___x_1403_, v_size_1397_);
v___x_1405_ = lean_nat_dec_lt(v___x_1404_, v_size_1398_);
lean_dec(v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_r_1402_);
lean_dec(v_l_1401_);
lean_dec(v_v_1400_);
lean_dec(v_k_1399_);
v___x_1406_ = lean_nat_add(v___x_1396_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1397_);
lean_dec(v___x_1406_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 3, v_impl_1395_);
lean_ctor_set(v___x_1392_, 0, v___x_1407_);
v___x_1409_ = v___x_1392_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_impl_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1390_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v_impl_1395_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1477_ = lean_ctor_get(v_impl_1395_, 4);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_impl_1395_, 3);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_impl_1395_, 2);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_impl_1395_, 1);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_impl_1395_, 0);
lean_dec(v_unused_1481_);
v___x_1412_ = v_impl_1395_;
v_isShared_1413_ = v_isSharedCheck_1476_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v_impl_1395_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1476_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_size_1414_; lean_object* v_size_1415_; lean_object* v_k_1416_; lean_object* v_v_1417_; lean_object* v_l_1418_; lean_object* v_r_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_size_1414_ = lean_ctor_get(v_l_1401_, 0);
v_size_1415_ = lean_ctor_get(v_r_1402_, 0);
v_k_1416_ = lean_ctor_get(v_r_1402_, 1);
v_v_1417_ = lean_ctor_get(v_r_1402_, 2);
v_l_1418_ = lean_ctor_get(v_r_1402_, 3);
v_r_1419_ = lean_ctor_get(v_r_1402_, 4);
v___x_1420_ = lean_unsigned_to_nat(2u);
v___x_1421_ = lean_nat_mul(v___x_1420_, v_size_1414_);
v___x_1422_ = lean_nat_dec_lt(v_size_1415_, v___x_1421_);
lean_dec(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1451_; 
lean_inc(v_r_1419_);
lean_inc(v_l_1418_);
lean_inc(v_v_1417_);
lean_inc(v_k_1416_);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_r_1402_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1452_ = lean_ctor_get(v_r_1402_, 4);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_r_1402_, 3);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1402_, 2);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_r_1402_, 1);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1402_, 0);
lean_dec(v_unused_1456_);
v___x_1424_ = v_r_1402_;
v_isShared_1425_ = v_isSharedCheck_1451_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v_r_1402_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1451_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___x_1439_; lean_object* v___y_1441_; 
v___x_1426_ = lean_nat_add(v___x_1396_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1427_ = lean_nat_add(v___x_1426_, v_size_1397_);
lean_dec(v___x_1426_);
v___x_1439_ = lean_nat_add(v___x_1396_, v_size_1414_);
if (lean_obj_tag(v_l_1418_) == 0)
{
lean_object* v_size_1449_; 
v_size_1449_ = lean_ctor_get(v_l_1418_, 0);
lean_inc(v_size_1449_);
v___y_1441_ = v_size_1449_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___y_1441_ = v___x_1450_;
goto v___jp_1440_;
}
v___jp_1428_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_nat_add(v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec(v___y_1430_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_r_1390_);
lean_ctor_set(v___x_1424_, 3, v_r_1419_);
lean_ctor_set(v___x_1424_, 2, v_v_1388_);
lean_ctor_set(v___x_1424_, 1, v_k_1387_);
lean_ctor_set(v___x_1424_, 0, v___x_1432_);
v___x_1434_ = v___x_1424_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_r_1419_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_r_1390_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1434_);
lean_ctor_set(v___x_1412_, 3, v___y_1429_);
lean_ctor_set(v___x_1412_, 2, v_v_1417_);
lean_ctor_set(v___x_1412_, 1, v_k_1416_);
lean_ctor_set(v___x_1412_, 0, v___x_1427_);
v___x_1436_ = v___x_1412_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1416_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1417_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___y_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
v___jp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_nat_add(v___x_1439_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec(v___x_1439_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1418_);
lean_ctor_set(v___x_1392_, 3, v_l_1401_);
lean_ctor_set(v___x_1392_, 2, v_v_1400_);
lean_ctor_set(v___x_1392_, 1, v_k_1399_);
lean_ctor_set(v___x_1392_, 0, v___x_1442_);
v___x_1444_ = v___x_1392_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_l_1418_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_nat_add(v___x_1396_, v_size_1397_);
if (lean_obj_tag(v_r_1419_) == 0)
{
lean_object* v_size_1446_; 
v_size_1446_ = lean_ctor_get(v_r_1419_, 0);
lean_inc(v_size_1446_);
v___y_1429_ = v___x_1444_;
v___y_1430_ = v___x_1445_;
v___y_1431_ = v_size_1446_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___y_1429_ = v___x_1444_;
v___y_1430_ = v___x_1445_;
v___y_1431_ = v___x_1447_;
goto v___jp_1428_;
}
}
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_del_object(v___x_1392_);
v___x_1457_ = lean_nat_add(v___x_1396_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1397_);
lean_dec(v___x_1457_);
v___x_1459_ = lean_nat_add(v___x_1396_, v_size_1397_);
v___x_1460_ = lean_nat_add(v___x_1459_, v_size_1415_);
lean_dec(v___x_1459_);
lean_inc_ref(v_r_1390_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_r_1390_);
lean_ctor_set(v___x_1412_, 3, v_r_1402_);
lean_ctor_set(v___x_1412_, 2, v_v_1388_);
lean_ctor_set(v___x_1412_, 1, v_k_1387_);
lean_ctor_set(v___x_1412_, 0, v___x_1460_);
v___x_1462_ = v___x_1412_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_r_1402_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_r_1390_);
v___x_1462_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v_r_1390_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; 
v_unused_1470_ = lean_ctor_get(v_r_1390_, 4);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_r_1390_, 3);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_r_1390_, 2);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_r_1390_, 1);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_r_1390_, 0);
lean_dec(v_unused_1474_);
v___x_1464_ = v_r_1390_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v_r_1390_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1462_);
lean_ctor_set(v___x_1464_, 3, v_l_1401_);
lean_ctor_set(v___x_1464_, 2, v_v_1400_);
lean_ctor_set(v___x_1464_, 1, v_k_1399_);
lean_ctor_set(v___x_1464_, 0, v___x_1458_);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___x_1462_);
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
}
}
}
else
{
lean_object* v_l_1482_; 
v_l_1482_ = lean_ctor_get(v_impl_1395_, 3);
lean_inc(v_l_1482_);
if (lean_obj_tag(v_l_1482_) == 0)
{
lean_object* v_r_1483_; lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1496_; 
v_r_1483_ = lean_ctor_get(v_impl_1395_, 4);
v_k_1484_ = lean_ctor_get(v_impl_1395_, 1);
v_v_1485_ = lean_ctor_get(v_impl_1395_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_impl_1395_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1497_ = lean_ctor_get(v_impl_1395_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_impl_1395_, 0);
lean_dec(v_unused_1498_);
v___x_1487_ = v_impl_1395_;
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_r_1483_);
lean_inc(v_v_1485_);
lean_inc(v_k_1484_);
lean_dec(v_impl_1395_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1483_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 3, v_r_1483_);
lean_ctor_set(v___x_1487_, 2, v_v_1388_);
lean_ctor_set(v___x_1487_, 1, v_k_1387_);
lean_ctor_set(v___x_1487_, 0, v___x_1396_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_r_1483_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_r_1483_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1491_);
lean_ctor_set(v___x_1392_, 3, v_l_1482_);
lean_ctor_set(v___x_1392_, 2, v_v_1485_);
lean_ctor_set(v___x_1392_, 1, v_k_1484_);
lean_ctor_set(v___x_1392_, 0, v___x_1489_);
v___x_1493_ = v___x_1392_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_k_1484_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_v_1485_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_r_1499_; 
v_r_1499_ = lean_ctor_get(v_impl_1395_, 4);
lean_inc(v_r_1499_);
if (lean_obj_tag(v_r_1499_) == 0)
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1524_; 
v_k_1500_ = lean_ctor_get(v_impl_1395_, 1);
v_v_1501_ = lean_ctor_get(v_impl_1395_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_impl_1395_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1525_ = lean_ctor_get(v_impl_1395_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_impl_1395_, 3);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_impl_1395_, 0);
lean_dec(v_unused_1527_);
v___x_1503_ = v_impl_1395_;
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
lean_dec(v_impl_1395_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1520_; 
v_k_1505_ = lean_ctor_get(v_r_1499_, 1);
v_v_1506_ = lean_ctor_get(v_r_1499_, 2);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_r_1499_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1521_ = lean_ctor_get(v_r_1499_, 4);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1499_, 3);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1499_, 0);
lean_dec(v_unused_1523_);
v___x_1508_ = v_r_1499_;
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_v_1506_);
lean_inc(v_k_1505_);
lean_dec(v_r_1499_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_unsigned_to_nat(3u);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_l_1482_);
lean_ctor_set(v___x_1508_, 3, v_l_1482_);
lean_ctor_set(v___x_1508_, 2, v_v_1501_);
lean_ctor_set(v___x_1508_, 1, v_k_1500_);
lean_ctor_set(v___x_1508_, 0, v___x_1396_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_l_1482_);
v___x_1512_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_l_1482_);
lean_ctor_set(v___x_1503_, 2, v_v_1388_);
lean_ctor_set(v___x_1503_, 1, v_k_1387_);
lean_ctor_set(v___x_1503_, 0, v___x_1396_);
v___x_1514_ = v___x_1503_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_l_1482_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1514_);
lean_ctor_set(v___x_1392_, 3, v___x_1512_);
lean_ctor_set(v___x_1392_, 2, v_v_1506_);
lean_ctor_set(v___x_1392_, 1, v_k_1505_);
lean_ctor_set(v___x_1392_, 0, v___x_1510_);
v___x_1516_ = v___x_1392_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_unsigned_to_nat(2u);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_r_1499_);
lean_ctor_set(v___x_1392_, 3, v_impl_1395_);
lean_ctor_set(v___x_1392_, 0, v___x_1528_);
v___x_1530_ = v___x_1392_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_impl_1395_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1499_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1533_; 
lean_dec(v_v_1388_);
lean_dec(v_k_1387_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 2, v_v_1384_);
lean_ctor_set(v___x_1392_, 1, v_k_1383_);
v___x_1533_ = v___x_1392_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_size_1386_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_r_1390_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
default: 
{
lean_object* v_impl_1535_; lean_object* v___x_1536_; 
lean_dec(v_size_1386_);
v_impl_1535_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1383_, v_v_1384_, v_r_1390_);
v___x_1536_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1389_) == 0)
{
lean_object* v_size_1537_; lean_object* v_size_1538_; lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v_l_1541_; lean_object* v_r_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v_size_1537_ = lean_ctor_get(v_l_1389_, 0);
v_size_1538_ = lean_ctor_get(v_impl_1535_, 0);
lean_inc(v_size_1538_);
v_k_1539_ = lean_ctor_get(v_impl_1535_, 1);
lean_inc(v_k_1539_);
v_v_1540_ = lean_ctor_get(v_impl_1535_, 2);
lean_inc(v_v_1540_);
v_l_1541_ = lean_ctor_get(v_impl_1535_, 3);
lean_inc(v_l_1541_);
v_r_1542_ = lean_ctor_get(v_impl_1535_, 4);
lean_inc(v_r_1542_);
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = lean_nat_mul(v___x_1543_, v_size_1537_);
v___x_1545_ = lean_nat_dec_lt(v___x_1544_, v_size_1538_);
lean_dec(v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec(v_r_1542_);
lean_dec(v_l_1541_);
lean_dec(v_v_1540_);
lean_dec(v_k_1539_);
v___x_1546_ = lean_nat_add(v___x_1536_, v_size_1537_);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1538_);
lean_dec(v_size_1538_);
lean_dec(v___x_1546_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_impl_1535_);
lean_ctor_set(v___x_1392_, 0, v___x_1547_);
v___x_1549_ = v___x_1392_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_impl_1535_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v_impl_1535_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; 
v_unused_1615_ = lean_ctor_get(v_impl_1535_, 4);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1535_, 3);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1535_, 2);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_impl_1535_, 1);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_impl_1535_, 0);
lean_dec(v_unused_1619_);
v___x_1552_ = v_impl_1535_;
v_isShared_1553_ = v_isSharedCheck_1614_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v_impl_1535_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1614_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_size_1554_; lean_object* v_k_1555_; lean_object* v_v_1556_; lean_object* v_l_1557_; lean_object* v_r_1558_; lean_object* v_size_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_size_1554_ = lean_ctor_get(v_l_1541_, 0);
v_k_1555_ = lean_ctor_get(v_l_1541_, 1);
v_v_1556_ = lean_ctor_get(v_l_1541_, 2);
v_l_1557_ = lean_ctor_get(v_l_1541_, 3);
v_r_1558_ = lean_ctor_get(v_l_1541_, 4);
v_size_1559_ = lean_ctor_get(v_r_1542_, 0);
v___x_1560_ = lean_unsigned_to_nat(2u);
v___x_1561_ = lean_nat_mul(v___x_1560_, v_size_1559_);
v___x_1562_ = lean_nat_dec_lt(v_size_1554_, v___x_1561_);
lean_dec(v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_r_1558_);
lean_inc(v_l_1557_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_l_1541_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1591_ = lean_ctor_get(v_l_1541_, 4);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1541_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1541_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1541_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1541_, 0);
lean_dec(v_unused_1595_);
v___x_1564_ = v_l_1541_;
v_isShared_1565_ = v_isSharedCheck_1590_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v_l_1541_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1590_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1580_; 
v___x_1566_ = lean_nat_add(v___x_1536_, v_size_1537_);
v___x_1567_ = lean_nat_add(v___x_1566_, v_size_1538_);
lean_dec(v_size_1538_);
if (lean_obj_tag(v_l_1557_) == 0)
{
lean_object* v_size_1588_; 
v_size_1588_ = lean_ctor_get(v_l_1557_, 0);
lean_inc(v_size_1588_);
v___y_1580_ = v_size_1588_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___y_1580_ = v___x_1589_;
goto v___jp_1579_;
}
v___jp_1568_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_nat_add(v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec(v___y_1570_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v_r_1542_);
lean_ctor_set(v___x_1564_, 3, v_r_1558_);
lean_ctor_set(v___x_1564_, 2, v_v_1540_);
lean_ctor_set(v___x_1564_, 1, v_k_1539_);
lean_ctor_set(v___x_1564_, 0, v___x_1572_);
v___x_1574_ = v___x_1564_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1542_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v___x_1574_);
lean_ctor_set(v___x_1552_, 3, v___y_1569_);
lean_ctor_set(v___x_1552_, 2, v_v_1556_);
lean_ctor_set(v___x_1552_, 1, v_k_1555_);
lean_ctor_set(v___x_1552_, 0, v___x_1567_);
v___x_1576_ = v___x_1552_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v___y_1569_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
v___jp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_nat_add(v___x_1566_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec(v___x_1566_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1557_);
lean_ctor_set(v___x_1392_, 0, v___x_1581_);
v___x_1583_ = v___x_1392_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_l_1557_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_nat_add(v___x_1536_, v_size_1559_);
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_size_1585_; 
v_size_1585_ = lean_ctor_get(v_r_1558_, 0);
lean_inc(v_size_1585_);
v___y_1569_ = v___x_1583_;
v___y_1570_ = v___x_1584_;
v___y_1571_ = v_size_1585_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___y_1569_ = v___x_1583_;
v___y_1570_ = v___x_1584_;
v___y_1571_ = v___x_1586_;
goto v___jp_1568_;
}
}
}
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
lean_del_object(v___x_1392_);
v___x_1596_ = lean_nat_add(v___x_1536_, v_size_1537_);
v___x_1597_ = lean_nat_add(v___x_1596_, v_size_1538_);
lean_dec(v_size_1538_);
v___x_1598_ = lean_nat_add(v___x_1596_, v_size_1554_);
lean_dec(v___x_1596_);
lean_inc_ref(v_l_1389_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v_l_1541_);
lean_ctor_set(v___x_1552_, 3, v_l_1389_);
lean_ctor_set(v___x_1552_, 2, v_v_1388_);
lean_ctor_set(v___x_1552_, 1, v_k_1387_);
lean_ctor_set(v___x_1552_, 0, v___x_1598_);
v___x_1600_ = v___x_1552_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_l_1541_);
v___x_1600_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v_l_1389_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1608_ = lean_ctor_get(v_l_1389_, 4);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_l_1389_, 3);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_l_1389_, 2);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_l_1389_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_l_1389_, 0);
lean_dec(v_unused_1612_);
v___x_1602_ = v_l_1389_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v_l_1389_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 4, v_r_1542_);
lean_ctor_set(v___x_1602_, 3, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v_v_1540_);
lean_ctor_set(v___x_1602_, 1, v_k_1539_);
lean_ctor_set(v___x_1602_, 0, v___x_1597_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_r_1542_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1620_; 
v_l_1620_ = lean_ctor_get(v_impl_1535_, 3);
lean_inc(v_l_1620_);
if (lean_obj_tag(v_l_1620_) == 0)
{
lean_object* v_r_1621_; lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1646_; 
v_r_1621_ = lean_ctor_get(v_impl_1535_, 4);
v_k_1622_ = lean_ctor_get(v_impl_1535_, 1);
v_v_1623_ = lean_ctor_get(v_impl_1535_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_impl_1535_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1647_ = lean_ctor_get(v_impl_1535_, 3);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1535_, 0);
lean_dec(v_unused_1648_);
v___x_1625_ = v_impl_1535_;
v_isShared_1626_ = v_isSharedCheck_1646_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_r_1621_);
lean_inc(v_v_1623_);
lean_inc(v_k_1622_);
lean_dec(v_impl_1535_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1646_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1642_; 
v_k_1627_ = lean_ctor_get(v_l_1620_, 1);
v_v_1628_ = lean_ctor_get(v_l_1620_, 2);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_l_1620_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1643_ = lean_ctor_get(v_l_1620_, 4);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_l_1620_, 3);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_l_1620_, 0);
lean_dec(v_unused_1645_);
v___x_1630_ = v_l_1620_;
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_v_1628_);
lean_inc(v_k_1627_);
lean_dec(v_l_1620_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1621_, 2);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 4, v_r_1621_);
lean_ctor_set(v___x_1630_, 3, v_r_1621_);
lean_ctor_set(v___x_1630_, 2, v_v_1388_);
lean_ctor_set(v___x_1630_, 1, v_k_1387_);
lean_ctor_set(v___x_1630_, 0, v___x_1536_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_r_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_r_1621_);
v___x_1634_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
lean_inc(v_r_1621_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 3, v_r_1621_);
lean_ctor_set(v___x_1625_, 0, v___x_1536_);
v___x_1636_ = v___x_1625_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_r_1621_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_r_1621_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1636_);
lean_ctor_set(v___x_1392_, 3, v___x_1634_);
lean_ctor_set(v___x_1392_, 2, v_v_1628_);
lean_ctor_set(v___x_1392_, 1, v_k_1627_);
lean_ctor_set(v___x_1392_, 0, v___x_1632_);
v___x_1638_ = v___x_1392_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1636_);
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
else
{
lean_object* v_r_1649_; 
v_r_1649_ = lean_ctor_get(v_impl_1535_, 4);
lean_inc(v_r_1649_);
if (lean_obj_tag(v_r_1649_) == 0)
{
lean_object* v_k_1650_; lean_object* v_v_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1662_; 
v_k_1650_ = lean_ctor_get(v_impl_1535_, 1);
v_v_1651_ = lean_ctor_get(v_impl_1535_, 2);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_impl_1535_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1663_ = lean_ctor_get(v_impl_1535_, 4);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_impl_1535_, 3);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_impl_1535_, 0);
lean_dec(v_unused_1665_);
v___x_1653_ = v_impl_1535_;
v_isShared_1654_ = v_isSharedCheck_1662_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_v_1651_);
lean_inc(v_k_1650_);
lean_dec(v_impl_1535_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1662_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_unsigned_to_nat(3u);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v_l_1620_);
lean_ctor_set(v___x_1653_, 2, v_v_1388_);
lean_ctor_set(v___x_1653_, 1, v_k_1387_);
lean_ctor_set(v___x_1653_, 0, v___x_1536_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1620_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1620_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_r_1649_);
lean_ctor_set(v___x_1392_, 3, v___x_1657_);
lean_ctor_set(v___x_1392_, 2, v_v_1651_);
lean_ctor_set(v___x_1392_, 1, v_k_1650_);
lean_ctor_set(v___x_1392_, 0, v___x_1655_);
v___x_1659_ = v___x_1392_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1650_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1651_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1649_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(2u);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_impl_1535_);
lean_ctor_set(v___x_1392_, 3, v_r_1649_);
lean_ctor_set(v___x_1392_, 0, v___x_1666_);
v___x_1668_ = v___x_1392_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_r_1649_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_impl_1535_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
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
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_k_1383_);
lean_ctor_set(v___x_1672_, 2, v_v_1384_);
lean_ctor_set(v___x_1672_, 3, v_t_1385_);
lean_ctor_set(v___x_1672_, 4, v_t_1385_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(lean_object* v_as_1673_, size_t v_sz_1674_, size_t v_i_1675_, lean_object* v_b_1676_){
_start:
{
lean_object* v___y_1679_; uint8_t v___x_1683_; 
v___x_1683_ = lean_usize_dec_lt(v_i_1675_, v_sz_1674_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_b_1676_);
return v___x_1684_;
}
else
{
lean_object* v_a_1685_; uint8_t v___x_1686_; 
v_a_1685_ = lean_array_uget_borrowed(v_as_1673_, v_i_1675_);
lean_inc(v_b_1676_);
lean_inc(v_a_1685_);
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_a_1685_, v_b_1676_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_box(0);
lean_inc(v_a_1685_);
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_a_1685_, v___x_1687_, v_b_1676_);
v___y_1679_ = v___x_1688_;
goto v___jp_1678_;
}
else
{
v___y_1679_ = v_b_1676_;
goto v___jp_1678_;
}
}
v___jp_1678_:
{
size_t v___x_1680_; size_t v___x_1681_; 
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1675_, v___x_1680_);
v_i_1675_ = v___x_1681_;
v_b_1676_ = v___y_1679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg___boxed(lean_object* v_as_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1689_, v_sz_boxed_1694_, v_i_boxed_1695_, v_b_1692_);
lean_dec_ref(v_as_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(lean_object* v_type_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_type_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v_set_1705_; size_t v_sz_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v_set_1705_ = lean_box(1);
v_sz_1706_ = lean_array_size(v_a_1704_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_a_1704_, v_sz_1706_, v___x_1707_, v_set_1705_);
lean_dec(v_a_1704_);
return v___x_1708_;
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_a_1709_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1703_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1703_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet___boxed(lean_object* v_type_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_type_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(lean_object* v_00_u03b2_1724_, lean_object* v_k_1725_, lean_object* v_t_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_k_1725_, v_t_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___boxed(lean_object* v_00_u03b2_1728_, lean_object* v_k_1729_, lean_object* v_t_1730_){
_start:
{
uint8_t v_res_1731_; lean_object* v_r_1732_; 
v_res_1731_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0(v_00_u03b2_1728_, v_k_1729_, v_t_1730_);
v_r_1732_ = lean_box(v_res_1731_);
return v_r_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1(lean_object* v_00_u03b2_1733_, lean_object* v_k_1734_, lean_object* v_v_1735_, lean_object* v_t_1736_, lean_object* v_hl_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__1___redArg(v_k_1734_, v_v_1735_, v_t_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(lean_object* v_as_1739_, size_t v_sz_1740_, size_t v_i_1741_, lean_object* v_b_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___redArg(v_as_1739_, v_sz_1740_, v_i_1741_, v_b_1742_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2___boxed(lean_object* v_as_1749_, lean_object* v_sz_1750_, lean_object* v_i_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
size_t v_sz_boxed_1758_; size_t v_i_boxed_1759_; lean_object* v_res_1760_; 
v_sz_boxed_1758_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1759_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__2(v_as_1749_, v_sz_boxed_1758_, v_i_boxed_1759_, v_b_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_as_1749_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* v_e_1761_, lean_object* v_declName_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
uint8_t v___y_1769_; uint8_t v___y_1791_; lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Expr_getAppFn(v_e_1761_);
if (lean_obj_tag(v___x_1794_) == 4)
{
lean_object* v_declName_1795_; lean_object* v___x_1796_; 
v_declName_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc_n(v_declName_1795_, 2);
lean_dec_ref_known(v___x_1794_, 2);
v___x_1796_ = l_Lean_privateToUserName_x3f(v_declName_1795_);
if (lean_obj_tag(v___x_1796_) == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_name_eq(v_declName_1795_, v_declName_1762_);
lean_dec(v_declName_1795_);
v___y_1791_ = v___x_1797_;
goto v___jp_1790_;
}
else
{
lean_object* v_val_1798_; uint8_t v___x_1799_; 
lean_dec(v_declName_1795_);
v_val_1798_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1798_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1799_ = lean_name_eq(v_val_1798_, v_declName_1762_);
lean_dec(v_val_1798_);
v___y_1791_ = v___x_1799_;
goto v___jp_1790_;
}
}
else
{
uint8_t v___x_1800_; 
lean_dec_ref(v___x_1794_);
v___x_1800_ = 0;
v___y_1769_ = v___x_1800_;
goto v___jp_1768_;
}
v___jp_1768_:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_e_1761_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1781_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
if (lean_obj_tag(v_a_1771_) == 1)
{
lean_object* v_val_1775_; 
lean_del_object(v___x_1773_);
v_val_1775_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v_a_1771_, 1);
v_e_1761_ = v_val_1775_;
goto _start;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_dec(v_a_1771_);
v___x_1777_ = lean_box(v___y_1769_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1777_);
v___x_1779_ = v___x_1773_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1770_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1770_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
v___jp_1790_:
{
if (v___y_1791_ == 0)
{
v___y_1769_ = v___y_1791_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec_ref(v_e_1761_);
v___x_1792_ = lean_box(v___y_1791_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* v_e_1801_, lean_object* v_declName_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v_e_1801_, v_declName_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_declName_1802_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(lean_object* v_k_1809_, lean_object* v_b_1810_, lean_object* v_c_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
v___x_1817_ = lean_apply_7(v_k_1809_, v_b_1810_, v_c_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, lean_box(0));
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed(lean_object* v_k_1818_, lean_object* v_b_1819_, lean_object* v_c_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0(v_k_1818_, v_b_1819_, v_c_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(lean_object* v_type_1827_, lean_object* v_k_1828_, uint8_t v_cleanupAnnotations_1829_, uint8_t v_whnfType_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___f_1836_; lean_object* v___x_1837_; 
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1836_, 0, v_k_1828_);
v___x_1837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1827_, v___f_1836_, v_cleanupAnnotations_1829_, v_whnfType_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1837_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1837_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___boxed(lean_object* v_type_1854_, lean_object* v_k_1855_, lean_object* v_cleanupAnnotations_1856_, lean_object* v_whnfType_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1863_; uint8_t v_whnfType_boxed_1864_; lean_object* v_res_1865_; 
v_cleanupAnnotations_boxed_1863_ = lean_unbox(v_cleanupAnnotations_1856_);
v_whnfType_boxed_1864_ = lean_unbox(v_whnfType_1857_);
v_res_1865_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1854_, v_k_1855_, v_cleanupAnnotations_boxed_1863_, v_whnfType_boxed_1864_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(lean_object* v_00_u03b1_1866_, lean_object* v_type_1867_, lean_object* v_k_1868_, uint8_t v_cleanupAnnotations_1869_, uint8_t v_whnfType_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v_type_1867_, v_k_1868_, v_cleanupAnnotations_1869_, v_whnfType_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___boxed(lean_object* v_00_u03b1_1877_, lean_object* v_type_1878_, lean_object* v_k_1879_, lean_object* v_cleanupAnnotations_1880_, lean_object* v_whnfType_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1887_; uint8_t v_whnfType_boxed_1888_; lean_object* v_res_1889_; 
v_cleanupAnnotations_boxed_1887_ = lean_unbox(v_cleanupAnnotations_1880_);
v_whnfType_boxed_1888_ = lean_unbox(v_whnfType_1881_);
v_res_1889_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1(v_00_u03b1_1877_, v_type_1878_, v_k_1879_, v_cleanupAnnotations_boxed_1887_, v_whnfType_boxed_1888_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(lean_object* v_typeName_1893_, lean_object* v_as_1894_, size_t v_sz_1895_, size_t v_i_1896_, lean_object* v_b_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_usize_dec_lt(v_i_1896_, v_sz_1895_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_b_1897_);
return v___x_1904_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec_ref(v_b_1897_);
v_a_1905_ = lean_array_uget_borrowed(v_as_1894_, v_i_1896_);
v___x_1906_ = l_Lean_Expr_fvarId_x21(v_a_1905_);
v___x_1907_ = l_Lean_FVarId_getDecl___redArg(v___x_1906_, v___y_1898_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = l_Lean_LocalDecl_type(v_a_1908_);
lean_dec(v_a_1908_);
v___x_1910_ = l_Lean_Expr_consumeMData(v___x_1909_);
lean_dec_ref(v___x_1909_);
v___x_1911_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(v___x_1910_, v_typeName_1893_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1927_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1927_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1927_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_unbox(v_a_1912_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; 
lean_del_object(v___x_1914_);
lean_dec(v_a_1912_);
v___x_1918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_add(v_i_1896_, v___x_1919_);
v_i_1896_ = v___x_1920_;
v_b_1897_ = v___x_1918_;
goto _start;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1912_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1916_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1923_);
v___x_1925_ = v___x_1914_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1911_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1911_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1907_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1907_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___boxed(lean_object* v_typeName_1944_, lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
size_t v_sz_boxed_1954_; size_t v_i_boxed_1955_; lean_object* v_res_1956_; 
v_sz_boxed_1954_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1955_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1944_, v_as_1945_, v_sz_boxed_1954_, v_i_boxed_1955_, v_b_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v_as_1945_);
lean_dec(v_typeName_1944_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(lean_object* v_typeName_1957_, lean_object* v_xs_1958_, lean_object* v_x_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; size_t v_sz_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0___closed__0));
v_sz_1966_ = lean_array_size(v_xs_1958_);
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__0(v_typeName_1957_, v_xs_1958_, v_sz_1966_, v___x_1967_, v___x_1965_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1983_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1983_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1983_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_fst_1973_; 
v_fst_1973_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_fst_1973_);
lean_dec(v_a_1969_);
if (lean_obj_tag(v_fst_1973_) == 0)
{
uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = 0;
v___x_1975_ = lean_box(v___x_1974_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1975_);
v___x_1977_ = v___x_1971_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
lean_object* v_val_1979_; lean_object* v___x_1981_; 
v_val_1979_ = lean_ctor_get(v_fst_1973_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v_fst_1973_, 1);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_val_1979_);
v___x_1981_ = v___x_1971_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_val_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v_a_1984_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1968_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1968_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed(lean_object* v_typeName_1992_, lean_object* v_xs_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0(v_typeName_1992_, v_xs_1993_, v_x_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec_ref(v_x_1994_);
lean_dec_ref(v_xs_1993_);
lean_dec(v_typeName_1992_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* v_typeName_2001_, lean_object* v_info_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___f_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; 
v___f_2008_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2008_, 0, v_typeName_2001_);
v___x_2009_ = l_Lean_ConstantInfo_type(v_info_2002_);
v___x_2010_ = 0;
v___x_2011_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg(v___x_2009_, v___f_2008_, v___x_2010_, v___x_2010_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* v_typeName_2012_, lean_object* v_info_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v_typeName_2012_, v_info_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec_ref(v_info_2013_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(lean_object* v_e_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lean_Expr_hasMVar(v_e_2020_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_e_2020_);
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; lean_object* v_mctx_2026_; lean_object* v___x_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v_cache_2031_; lean_object* v_zetaDeltaFVarIds_2032_; lean_object* v_postponed_2033_; lean_object* v_diag_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2043_; 
v___x_2025_ = lean_st_ref_get(v___y_2021_);
v_mctx_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_ref(v_mctx_2026_);
lean_dec(v___x_2025_);
v___x_2027_ = l_Lean_instantiateMVarsCore(v_mctx_2026_, v_e_2020_);
v_fst_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v___x_2027_, 1);
lean_inc(v_snd_2029_);
lean_dec_ref(v___x_2027_);
v___x_2030_ = lean_st_ref_take(v___y_2021_);
v_cache_2031_ = lean_ctor_get(v___x_2030_, 1);
v_zetaDeltaFVarIds_2032_ = lean_ctor_get(v___x_2030_, 2);
v_postponed_2033_ = lean_ctor_get(v___x_2030_, 3);
v_diag_2034_ = lean_ctor_get(v___x_2030_, 4);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v___x_2030_, 0);
lean_dec(v_unused_2044_);
v___x_2036_ = v___x_2030_;
v_isShared_2037_ = v_isSharedCheck_2043_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_diag_2034_);
lean_inc(v_postponed_2033_);
lean_inc(v_zetaDeltaFVarIds_2032_);
lean_inc(v_cache_2031_);
lean_dec(v___x_2030_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2043_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v_snd_2029_);
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_snd_2029_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_cache_2031_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_zetaDeltaFVarIds_2032_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v_postponed_2033_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v_diag_2034_);
v___x_2039_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_st_ref_put(v___y_2021_, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_fst_2028_);
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg___boxed(lean_object* v_e_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2045_, v___y_2046_);
lean_dec(v___y_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(lean_object* v_e_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_e_2049_, v___y_2051_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___boxed(lean_object* v_e_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0(v_e_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(lean_object* v_type_2063_, lean_object* v_k_2064_, uint8_t v_cleanupAnnotations_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___f_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2071_, 0, v_k_2064_);
v___x_2072_ = 0;
v___x_2073_ = lean_box(0);
v___x_2074_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2072_, v___x_2073_, v_type_2063_, v___f_2071_, v_cleanupAnnotations_2065_, v___x_2072_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2074_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2074_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg___boxed(lean_object* v_type_2091_, lean_object* v_k_2092_, lean_object* v_cleanupAnnotations_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2099_; lean_object* v_res_2100_; 
v_cleanupAnnotations_boxed_2099_ = lean_unbox(v_cleanupAnnotations_2093_);
v_res_2100_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2091_, v_k_2092_, v_cleanupAnnotations_boxed_2099_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(lean_object* v_00_u03b1_2101_, lean_object* v_type_2102_, lean_object* v_k_2103_, uint8_t v_cleanupAnnotations_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_type_2102_, v_k_2103_, v_cleanupAnnotations_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_type_2112_, lean_object* v_k_2113_, lean_object* v_cleanupAnnotations_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2120_; lean_object* v_res_2121_; 
v_cleanupAnnotations_boxed_2120_ = lean_unbox(v_cleanupAnnotations_2114_);
v_res_2121_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1(v_00_u03b1_2111_, v_type_2112_, v_k_2113_, v_cleanupAnnotations_boxed_2120_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed(lean_object* v_typeNameSet_2122_, lean_object* v_x_2123_, lean_object* v_type_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(v_typeNameSet_2122_, v_x_2123_, v_type_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_x_2123_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(lean_object* v_typeNameSet_2131_, lean_object* v_type_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___f_2138_; lean_object* v_a_2140_; lean_object* v___y_2190_; lean_object* v___x_2200_; 
lean_inc(v_typeNameSet_2131_);
v___f_2138_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2138_, 0, v_typeNameSet_2131_);
lean_inc_ref(v_type_2132_);
v___x_2200_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(v_type_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_dec_ref(v_type_2132_);
v___y_2190_ = v___x_2200_;
goto v___jp_2189_;
}
else
{
lean_object* v_a_2201_; uint8_t v___y_2203_; uint8_t v___x_2204_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
v___x_2204_ = l_Lean_Exception_isInterrupt(v_a_2201_);
if (v___x_2204_ == 0)
{
uint8_t v___x_2205_; 
v___x_2205_ = l_Lean_Exception_isRuntime(v_a_2201_);
v___y_2203_ = v___x_2205_;
goto v___jp_2202_;
}
else
{
lean_dec(v_a_2201_);
v___y_2203_ = v___x_2204_;
goto v___jp_2202_;
}
v___jp_2202_:
{
if (v___y_2203_ == 0)
{
lean_dec_ref_known(v___x_2200_, 1);
v_a_2140_ = v_type_2132_;
goto v___jp_2139_;
}
else
{
lean_dec_ref(v_type_2132_);
v___y_2190_ = v___x_2200_;
goto v___jp_2189_;
}
}
}
v___jp_2139_:
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Lean_Expr_isForall(v_a_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_dec_ref(v___f_2138_);
v___x_2142_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__0___redArg(v_a_2140_, v_a_2134_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2178_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2178_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2178_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_Expr_getAppFn(v_a_2143_);
if (lean_obj_tag(v___x_2147_) == 4)
{
lean_object* v_declName_2148_; uint8_t v___x_2149_; 
v_declName_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_declName_2148_);
lean_dec_ref_known(v___x_2147_, 2);
lean_inc(v_typeNameSet_2131_);
v___x_2149_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_declName_2148_, v_typeNameSet_2131_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_del_object(v___x_2145_);
v___x_2150_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(v_a_2143_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2161_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
if (lean_obj_tag(v_a_2151_) == 1)
{
lean_object* v_val_2155_; 
lean_del_object(v___x_2153_);
v_val_2155_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_val_2155_);
lean_dec_ref_known(v_a_2151_, 1);
v_type_2132_ = v_val_2155_;
goto _start;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec(v_a_2151_);
lean_dec(v_typeNameSet_2131_);
v___x_2157_ = lean_box(v___x_2149_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2157_);
v___x_2159_ = v___x_2153_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_typeNameSet_2131_);
v_a_2162_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2150_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2150_);
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
else
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_dec(v_a_2143_);
lean_dec(v_typeNameSet_2131_);
v___x_2170_ = lean_box(v___x_2149_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2170_);
v___x_2172_ = v___x_2145_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_dec_ref(v___x_2147_);
lean_dec(v_a_2143_);
lean_dec(v_typeNameSet_2131_);
v___x_2174_ = lean_box(v___x_2141_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2174_);
v___x_2176_ = v___x_2145_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_typeNameSet_2131_);
v_a_2179_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2142_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2142_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
uint8_t v___x_2187_; lean_object* v___x_2188_; 
lean_dec(v_typeNameSet_2131_);
v___x_2187_ = 0;
v___x_2188_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit_spec__1___redArg(v_a_2140_, v___f_2138_, v___x_2187_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
return v___x_2188_;
}
}
v___jp_2189_:
{
if (lean_obj_tag(v___y_2190_) == 0)
{
lean_object* v_a_2191_; 
v_a_2191_ = lean_ctor_get(v___y_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___y_2190_, 1);
v_a_2140_ = v_a_2191_;
goto v___jp_2139_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v___f_2138_);
lean_dec(v_typeNameSet_2131_);
v_a_2192_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___y_2190_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___y_2190_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___lam__0(lean_object* v_typeNameSet_2206_, lean_object* v_x_2207_, lean_object* v_type_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2206_, v_type_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit___boxed(lean_object* v_typeNameSet_2215_, lean_object* v_type_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2215_, v_type_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* v_typeNameSet_2223_, lean_object* v_info_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = l_Lean_ConstantInfo_type(v_info_2224_);
v___x_2231_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod_visit(v_typeNameSet_2223_, v___x_2230_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* v_typeNameSet_2232_, lean_object* v_info_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v_typeNameSet_2232_, v_info_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_info_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* v_matchAlias_2240_, lean_object* v_addAlias_2241_, lean_object* v_alias_2242_, lean_object* v_declNames_2243_, lean_object* v_ns_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
lean_inc_ref(v_matchAlias_2240_);
lean_inc(v_alias_2242_);
lean_inc(v_ns_2244_);
v___x_2253_ = lean_apply_2(v_matchAlias_2240_, v_ns_2244_, v_alias_2242_);
v___x_2254_ = lean_unbox(v___x_2253_);
if (v___x_2254_ == 0)
{
if (lean_obj_tag(v_ns_2244_) == 1)
{
lean_object* v_pre_2255_; 
v_pre_2255_ = lean_ctor_get(v_ns_2244_, 0);
lean_inc(v_pre_2255_);
lean_dec_ref_known(v_ns_2244_, 2);
v_ns_2244_ = v_pre_2255_;
goto _start;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_dec(v_ns_2244_);
lean_dec(v_declNames_2243_);
lean_dec(v_alias_2242_);
lean_dec_ref(v_addAlias_2241_);
lean_dec_ref(v_matchAlias_2240_);
v___x_2257_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
else
{
lean_object* v___x_2259_; 
lean_dec(v_ns_2244_);
lean_dec_ref(v_matchAlias_2240_);
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc_ref(v_a_2247_);
lean_inc(v_a_2246_);
lean_inc_ref(v_a_2245_);
v___x_2259_ = lean_apply_10(v_addAlias_2241_, v_alias_2242_, v_declNames_2243_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, lean_box(0));
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias___boxed(lean_object* v_matchAlias_2260_, lean_object* v_addAlias_2261_, lean_object* v_alias_2262_, lean_object* v_declNames_2263_, lean_object* v_ns_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v_matchAlias_2260_, v_addAlias_2261_, v_alias_2262_, v_declNames_2263_, v_ns_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(lean_object* v_a_2276_){
_start:
{
uint8_t v___x_2278_; 
v___x_2278_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_2276_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___closed__0));
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg___boxed(lean_object* v_a_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2283_);
lean_dec_ref(v_a_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(lean_object* v_a_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v_a_2286_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___boxed(lean_object* v_a_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1(v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(lean_object* v_ctx_2300_, lean_object* v_id_2301_, uint8_t v_danglingDot_2302_, lean_object* v_declName_2303_, lean_object* v_decl_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
lean_inc(v_declName_2303_);
v___x_2313_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_bestLabelForDecl_x3f(v_ctx_2300_, v_declName_2303_, v_id_2301_, v_danglingDot_2302_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2366_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2366_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2366_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_decl_2304_);
lean_dec(v_declName_2303_);
v_a_2318_ = lean_ctor_get(v_a_2314_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2314_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2320_ = v_a_2314_;
v_isShared_2321_ = v_isSharedCheck_2328_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v_a_2314_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2328_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2323_);
v___x_2325_ = v___x_2316_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2329_; 
v_a_2329_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v_a_2314_, 1);
if (lean_obj_tag(v_a_2329_) == 1)
{
lean_object* v_val_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2361_; 
lean_del_object(v___x_2316_);
v_val_2330_ = lean_ctor_get(v_a_2329_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2332_ = v_a_2329_;
v_isShared_2333_ = v_isSharedCheck_2361_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_val_2330_);
lean_dec(v_a_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2361_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v_kind_2334_; lean_object* v_tags_2335_; lean_object* v___x_2336_; 
v_kind_2334_ = lean_ctor_get(v_decl_2304_, 1);
lean_inc_ref(v_kind_2334_);
v_tags_2335_ = lean_ctor_get(v_decl_2304_, 2);
lean_inc_ref(v_tags_2335_);
lean_dec_ref(v_decl_2304_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2336_ = lean_apply_5(v_kind_2334_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, lean_box(0));
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2338_ = lean_apply_5(v_tags_2335_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, lean_box(0));
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 0);
lean_ctor_set(v___x_2332_, 0, v_declName_2303_);
v___x_2341_ = v___x_2332_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_declName_2303_);
v___x_2341_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
uint8_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_unbox(v_a_2337_);
lean_dec(v_a_2337_);
v___x_2343_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_2330_, v___x_2341_, v___x_2342_, v_a_2339_, v___y_2305_, v___y_2306_);
return v___x_2343_;
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2337_);
lean_del_object(v___x_2332_);
lean_dec(v_val_2330_);
lean_dec(v_declName_2303_);
v_a_2345_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2338_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2338_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_tags_2335_);
lean_del_object(v___x_2332_);
lean_dec(v_val_2330_);
lean_dec(v_declName_2303_);
v_a_2353_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2336_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2336_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec(v_a_2329_);
lean_dec_ref(v_decl_2304_);
lean_dec(v_declName_2303_);
v___x_2362_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2362_);
v___x_2364_ = v___x_2316_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_decl_2304_);
lean_dec(v_declName_2303_);
v_a_2367_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2313_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2313_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed(lean_object* v_ctx_2375_, lean_object* v_id_2376_, lean_object* v_danglingDot_2377_, lean_object* v_declName_2378_, lean_object* v_decl_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_danglingDot_boxed_2388_; lean_object* v_res_2389_; 
v_danglingDot_boxed_2388_ = lean_unbox(v_danglingDot_2377_);
v_res_2389_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0(v_ctx_2375_, v_id_2376_, v_danglingDot_boxed_2388_, v_declName_2378_, v_decl_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
return v_res_2389_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(lean_object* v_id_2390_, uint8_t v_danglingDot_2391_, lean_object* v_ns_2392_, lean_object* v_alias_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = l_Lean_Name_isPrefixOf(v_ns_2392_, v_alias_2393_);
if (v___x_2394_ == 0)
{
lean_dec(v_alias_2393_);
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2395_ = lean_box(0);
v___x_2396_ = l_Lean_Name_replacePrefix(v_alias_2393_, v_ns_2392_, v___x_2395_);
v___x_2397_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_2390_, v___x_2396_, v_danglingDot_2391_);
lean_dec(v___x_2396_);
return v___x_2397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed(lean_object* v_id_2398_, lean_object* v_danglingDot_2399_, lean_object* v_ns_2400_, lean_object* v_alias_2401_){
_start:
{
uint8_t v_danglingDot_boxed_2402_; uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_danglingDot_boxed_2402_ = lean_unbox(v_danglingDot_2399_);
v_res_2403_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1(v_id_2398_, v_danglingDot_boxed_2402_, v_ns_2400_, v_alias_2401_);
lean_dec(v_ns_2400_);
lean_dec(v_id_2398_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(lean_object* v_a_2405_, lean_object* v___x_2406_, lean_object* v_alias_2407_, lean_object* v_as_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
if (lean_obj_tag(v_as_2408_) == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec_ref(v___x_2406_);
v___x_2416_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
else
{
lean_object* v_head_2418_; lean_object* v_tail_2419_; uint8_t v___x_2420_; 
v_head_2418_ = lean_ctor_get(v_as_2408_, 0);
lean_inc_n(v_head_2418_, 2);
v_tail_2419_ = lean_ctor_get(v_as_2408_, 1);
lean_inc(v_tail_2419_);
lean_dec_ref_known(v_as_2408_, 2);
lean_inc_ref(v___x_2406_);
v___x_2420_ = l_Lean_Server_Completion_allowCompletion(v_a_2405_, v___x_2406_, v_head_2418_);
if (v___x_2420_ == 0)
{
lean_dec(v_head_2418_);
v_as_2408_ = v_tail_2419_;
goto _start;
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2422_ = l_Lean_Name_getString_x21(v_alias_2407_);
v___x_2423_ = lean_box(0);
v___x_2424_ = l_Lean_Name_str___override(v___x_2423_, v___x_2422_);
v___x_2425_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_2424_, v_head_2418_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_dec_ref_known(v___x_2425_, 1);
v_as_2408_ = v_tail_2419_;
goto _start;
}
else
{
lean_dec(v_tail_2419_);
lean_dec_ref(v___x_2406_);
return v___x_2425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg___boxed(lean_object* v_a_2427_, lean_object* v___x_2428_, lean_object* v_alias_2429_, lean_object* v_as_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2427_, v___x_2428_, v_alias_2429_, v_as_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v_alias_2429_);
lean_dec_ref(v_a_2427_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(lean_object* v_a_2439_, lean_object* v_env_2440_, lean_object* v_alias_2441_, lean_object* v_declNames_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_2439_, v_env_2440_, v_alias_2441_, v_declNames_2442_, v___y_2443_, v___y_2444_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed(lean_object* v_a_2452_, lean_object* v_env_2453_, lean_object* v_alias_2454_, lean_object* v_declNames_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2(v_a_2452_, v_env_2453_, v_alias_2454_, v_declNames_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_alias_2454_);
lean_dec_ref(v_a_2452_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(lean_object* v___f_2465_, lean_object* v___f_2466_, lean_object* v_currNamespace_2467_, lean_object* v_alias_2468_, lean_object* v_declNames_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(v___f_2465_, v___f_2466_, v_alias_2468_, v_declNames_2469_, v_currNamespace_2467_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed(lean_object* v___f_2479_, lean_object* v___f_2480_, lean_object* v_currNamespace_2481_, lean_object* v_alias_2482_, lean_object* v_declNames_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3(v___f_2479_, v___f_2480_, v_currNamespace_2481_, v_alias_2482_, v_declNames_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(lean_object* v_f_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
if (lean_obj_tag(v_x_2495_) == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec_ref(v_f_2493_);
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_x_2494_);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
else
{
lean_object* v_key_2506_; lean_object* v_value_2507_; lean_object* v_tail_2508_; lean_object* v___x_2509_; 
v_key_2506_ = lean_ctor_get(v_x_2495_, 0);
lean_inc(v_key_2506_);
v_value_2507_ = lean_ctor_get(v_x_2495_, 1);
lean_inc(v_value_2507_);
v_tail_2508_ = lean_ctor_get(v_x_2495_, 2);
lean_inc(v_tail_2508_);
lean_dec_ref_known(v_x_2495_, 3);
lean_inc_ref(v_f_2493_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
lean_inc_ref(v___y_2498_);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
v___x_2509_ = lean_apply_10(v_f_2493_, v_key_2506_, v_value_2507_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, lean_box(0));
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
if (lean_obj_tag(v_a_2510_) == 0)
{
lean_dec_ref_known(v_a_2510_, 1);
lean_dec(v_tail_2508_);
lean_dec_ref(v_f_2493_);
return v___x_2509_;
}
else
{
lean_object* v_a_2511_; 
lean_dec_ref_known(v___x_2509_, 1);
v_a_2511_ = lean_ctor_get(v_a_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v_a_2510_, 1);
v_x_2494_ = v_a_2511_;
v_x_2495_ = v_tail_2508_;
goto _start;
}
}
else
{
lean_dec(v_tail_2508_);
lean_dec_ref(v_f_2493_);
return v___x_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg___boxed(lean_object* v_f_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2513_, v_x_2514_, v_x_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(lean_object* v_f_2525_, lean_object* v_as_2526_, size_t v_i_2527_, size_t v_stop_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
uint8_t v___x_2538_; 
v___x_2538_ = lean_usize_dec_eq(v_i_2527_, v_stop_2528_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_array_uget_borrowed(v_as_2526_, v_i_2527_);
v___x_2540_ = lean_box(0);
lean_inc(v___x_2539_);
lean_inc_ref(v_f_2525_);
v___x_2541_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_2525_, v___x_2540_, v___x_2539_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
if (lean_obj_tag(v_a_2542_) == 0)
{
lean_dec_ref_known(v_a_2542_, 1);
lean_dec_ref(v_f_2525_);
return v___x_2541_;
}
else
{
lean_object* v_a_2543_; size_t v___x_2544_; size_t v___x_2545_; 
lean_dec_ref_known(v___x_2541_, 1);
v_a_2543_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v_a_2542_, 1);
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_add(v_i_2527_, v___x_2544_);
v_i_2527_ = v___x_2545_;
v_b_2529_ = v_a_2543_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_2525_);
return v___x_2541_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec_ref(v_f_2525_);
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_b_2529_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg___boxed(lean_object* v_f_2549_, lean_object* v_as_2550_, lean_object* v_i_2551_, lean_object* v_stop_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
size_t v_i_boxed_2562_; size_t v_stop_boxed_2563_; lean_object* v_res_2564_; 
v_i_boxed_2562_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_stop_boxed_2563_ = lean_unbox_usize(v_stop_2552_);
lean_dec(v_stop_2552_);
v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2549_, v_as_2550_, v_i_boxed_2562_, v_stop_boxed_2563_, v_b_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v_as_2550_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(lean_object* v_f_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; 
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc(v___y_2573_);
lean_inc_ref(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
v___x_2577_ = lean_apply_10(v_f_2565_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, lean_box(0));
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_f_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0(v_f_2578_, v_x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(lean_object* v_f_2591_, lean_object* v_keys_2592_, lean_object* v_vals_2593_, lean_object* v_i_2594_, lean_object* v_acc_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2604_ = lean_array_get_size(v_keys_2592_);
v___x_2605_ = lean_nat_dec_lt(v_i_2594_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_i_2594_);
lean_dec_ref(v_f_2591_);
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_acc_2595_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
else
{
lean_object* v_k_2608_; lean_object* v_v_2609_; lean_object* v___x_2610_; 
v_k_2608_ = lean_array_fget_borrowed(v_keys_2592_, v_i_2594_);
v_v_2609_ = lean_array_fget_borrowed(v_vals_2593_, v_i_2594_);
lean_inc_ref(v_f_2591_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
lean_inc(v_v_2609_);
lean_inc(v_k_2608_);
v___x_2610_ = lean_apply_11(v_f_2591_, v_acc_2595_, v_k_2608_, v_v_2609_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, lean_box(0));
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_dec_ref_known(v_a_2611_, 1);
lean_dec(v_i_2594_);
lean_dec_ref(v_f_2591_);
return v___x_2610_;
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref_known(v___x_2610_, 1);
v_a_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v_a_2611_, 1);
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_add(v_i_2594_, v___x_2613_);
lean_dec(v_i_2594_);
v_i_2594_ = v___x_2614_;
v_acc_2595_ = v_a_2612_;
goto _start;
}
}
else
{
lean_dec(v_i_2594_);
lean_dec_ref(v_f_2591_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg___boxed(lean_object* v_f_2616_, lean_object* v_keys_2617_, lean_object* v_vals_2618_, lean_object* v_i_2619_, lean_object* v_acc_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2616_, v_keys_2617_, v_vals_2618_, v_i_2619_, v_acc_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v_vals_2618_);
lean_dec_ref(v_keys_2617_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(lean_object* v_f_2630_, lean_object* v_as_2631_, size_t v_i_2632_, size_t v_stop_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_a_2644_; lean_object* v___y_2649_; uint8_t v___x_2652_; 
v___x_2652_ = lean_usize_dec_eq(v_i_2632_, v_stop_2633_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_array_uget_borrowed(v_as_2631_, v_i_2632_);
switch(lean_obj_tag(v___x_2653_))
{
case 0:
{
lean_object* v_key_2654_; lean_object* v_val_2655_; lean_object* v___x_2656_; 
v_key_2654_ = lean_ctor_get(v___x_2653_, 0);
v_val_2655_ = lean_ctor_get(v___x_2653_, 1);
lean_inc_ref(v_f_2630_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v_val_2655_);
lean_inc(v_key_2654_);
v___x_2656_ = lean_apply_11(v_f_2630_, v_b_2634_, v_key_2654_, v_val_2655_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, lean_box(0));
v___y_2649_ = v___x_2656_;
goto v___jp_2648_;
}
case 1:
{
lean_object* v_node_2657_; lean_object* v___x_2658_; 
v_node_2657_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_node_2657_);
lean_inc_ref(v_f_2630_);
v___x_2658_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2630_, v_node_2657_, v_b_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
v___y_2649_ = v___x_2658_;
goto v___jp_2648_;
}
default: 
{
v_a_2644_ = v_b_2634_;
goto v___jp_2643_;
}
}
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref(v_f_2630_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_b_2634_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
v___jp_2643_:
{
size_t v___x_2645_; size_t v___x_2646_; 
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2632_, v___x_2645_);
v_i_2632_ = v___x_2646_;
v_b_2634_ = v_a_2644_;
goto _start;
}
v___jp_2648_:
{
if (lean_obj_tag(v___y_2649_) == 0)
{
lean_object* v_a_2650_; 
v_a_2650_ = lean_ctor_get(v___y_2649_, 0);
if (lean_obj_tag(v_a_2650_) == 0)
{
lean_dec_ref(v_f_2630_);
return v___y_2649_;
}
else
{
lean_object* v_a_2651_; 
lean_inc_ref(v_a_2650_);
lean_dec_ref_known(v___y_2649_, 1);
v_a_2651_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v_a_2650_, 1);
v_a_2644_ = v_a_2651_;
goto v___jp_2643_;
}
}
else
{
lean_dec_ref(v_f_2630_);
return v___y_2649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(lean_object* v_f_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
lean_object* v_es_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2686_; 
v_es_2672_ = lean_ctor_get(v_x_2662_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_x_2662_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2674_ = v_x_2662_;
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_es_2672_);
lean_dec(v_x_2662_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_array_get_size(v_es_2672_);
v___x_2678_ = lean_nat_dec_lt(v___x_2676_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref(v_es_2672_);
lean_dec_ref(v_f_2661_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 1);
lean_ctor_set(v___x_2674_, 0, v_x_2663_);
v___x_2680_ = v___x_2674_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_x_2663_);
v___x_2680_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
lean_del_object(v___x_2674_);
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = lean_usize_of_nat(v___x_2677_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2661_, v_es_2672_, v___x_2683_, v___x_2684_, v_x_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec_ref(v_es_2672_);
return v___x_2685_;
}
}
}
else
{
lean_object* v_ks_2687_; lean_object* v_vs_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_ks_2687_ = lean_ctor_get(v_x_2662_, 0);
lean_inc_ref(v_ks_2687_);
v_vs_2688_ = lean_ctor_get(v_x_2662_, 1);
lean_inc_ref(v_vs_2688_);
lean_dec_ref_known(v_x_2662_, 2);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_2661_, v_ks_2687_, v_vs_2688_, v___x_2689_, v_x_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec_ref(v_vs_2688_);
lean_dec_ref(v_ks_2687_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_f_2691_, lean_object* v_x_2692_, lean_object* v_x_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_2691_, v_x_2692_, v_x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg___boxed(lean_object* v_f_2703_, lean_object* v_as_2704_, lean_object* v_i_2705_, lean_object* v_stop_2706_, lean_object* v_b_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
size_t v_i_boxed_2716_; size_t v_stop_boxed_2717_; lean_object* v_res_2718_; 
v_i_boxed_2716_ = lean_unbox_usize(v_i_2705_);
lean_dec(v_i_2705_);
v_stop_boxed_2717_ = lean_unbox_usize(v_stop_2706_);
lean_dec(v_stop_2706_);
v_res_2718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_2703_, v_as_2704_, v_i_boxed_2716_, v_stop_boxed_2717_, v_b_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec_ref(v_as_2704_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(lean_object* v_map_2719_, lean_object* v_f_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___f_2729_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2729_, 0, v_f_2720_);
v___x_2730_ = lean_box(0);
v___x_2731_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v___f_2729_, v_map_2719_, v___x_2730_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg___boxed(lean_object* v_map_2732_, lean_object* v_f_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_2732_, v_f_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(lean_object* v_s_2743_, lean_object* v_f_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_map_u2081_2753_; lean_object* v_map_u2082_2754_; lean_object* v_buckets_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_map_u2081_2753_ = lean_ctor_get(v_s_2743_, 0);
lean_inc_ref(v_map_u2081_2753_);
v_map_u2082_2754_ = lean_ctor_get(v_s_2743_, 1);
lean_inc_ref(v_map_u2082_2754_);
lean_dec_ref(v_s_2743_);
v_buckets_2755_ = lean_ctor_get(v_map_u2081_2753_, 1);
lean_inc_ref(v_buckets_2755_);
lean_dec_ref(v_map_u2081_2753_);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = lean_array_get_size(v_buckets_2755_);
v___x_2758_ = lean_nat_dec_lt(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; 
lean_dec_ref(v_buckets_2755_);
v___x_2759_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2754_, v_f_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v___x_2759_;
}
else
{
lean_object* v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
v___x_2760_ = lean_box(0);
v___x_2761_ = ((size_t)0ULL);
v___x_2762_ = lean_usize_of_nat(v___x_2757_);
lean_inc_ref(v_f_2744_);
v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_2744_, v_buckets_2755_, v___x_2761_, v___x_2762_, v___x_2760_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec_ref(v_buckets_2755_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
if (lean_obj_tag(v_a_2764_) == 0)
{
lean_dec_ref_known(v_a_2764_, 1);
lean_dec_ref(v_map_u2082_2754_);
lean_dec_ref(v_f_2744_);
return v___x_2763_;
}
else
{
lean_object* v___x_2765_; 
lean_dec_ref_known(v_a_2764_, 1);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_u2082_2754_, v_f_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v___x_2765_;
}
}
else
{
lean_dec_ref(v_map_u2082_2754_);
lean_dec_ref(v_f_2744_);
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg___boxed(lean_object* v_s_2766_, lean_object* v_f_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_2766_, v_f_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(lean_object* v_f_2777_, lean_object* v_decl_2778_, lean_object* v_ci_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___y_2790_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_add(v___y_2780_, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(10000u);
v___x_2831_ = lean_nat_dec_le(v___x_2830_, v___x_2829_);
if (v___x_2831_ == 0)
{
v___y_2790_ = v___x_2829_;
goto v___jp_2789_;
}
else
{
lean_object* v___x_2832_; lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v___x_2829_);
v___x_2832_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_2783_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2849_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2849_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
if (lean_obj_tag(v_a_2833_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_ci_2779_);
lean_dec(v_decl_2778_);
lean_dec_ref(v_f_2777_);
v_a_2837_ = lean_ctor_get(v_a_2833_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_a_2833_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2839_ = v_a_2833_;
v_isShared_2840_ = v_isSharedCheck_2847_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v_a_2833_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2847_;
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
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2844_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2842_);
v___x_2844_ = v___x_2835_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v___x_2848_; 
lean_dec_ref_known(v_a_2833_, 1);
lean_del_object(v___x_2835_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v___y_2790_ = v___x_2848_;
goto v___jp_2789_;
}
}
}
v___jp_2789_:
{
lean_object* v___x_2791_; 
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2785_);
lean_inc_ref(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
v___x_2791_ = lean_apply_10(v_f_2777_, v_decl_2778_, v_ci_2779_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, lean_box(0));
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2819_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2819_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2819_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
if (lean_obj_tag(v_a_2792_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v___y_2790_);
v_a_2796_ = lean_ctor_get(v_a_2792_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_a_2792_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2798_ = v_a_2792_;
v_isShared_2799_ = v_isSharedCheck_2806_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v_a_2792_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2806_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2803_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2801_);
v___x_2803_ = v___x_2794_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2818_; 
v_a_2807_ = lean_ctor_get(v_a_2792_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2792_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2809_ = v_a_2792_;
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v_a_2792_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2807_);
lean_ctor_set(v___x_2811_, 1, v___y_2790_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2811_);
v___x_2813_ = v___x_2809_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2813_);
v___x_2815_ = v___x_2794_;
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
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v___y_2790_);
v_a_2820_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2791_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2791_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed(lean_object* v_f_2850_, lean_object* v_decl_2851_, lean_object* v_ci_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0(v_f_2850_, v_decl_2851_, v_ci_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(lean_object* v_f_2863_, lean_object* v_keys_2864_, lean_object* v_vals_2865_, lean_object* v_i_2866_, lean_object* v_acc_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = lean_array_get_size(v_keys_2864_);
v___x_2878_ = lean_nat_dec_lt(v_i_2866_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v_i_2866_);
lean_dec_ref(v_f_2863_);
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v_acc_2867_);
lean_ctor_set(v___x_2879_, 1, v___y_2868_);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
else
{
lean_object* v_k_2882_; lean_object* v_v_2883_; lean_object* v___x_2884_; 
v_k_2882_ = lean_array_fget_borrowed(v_keys_2864_, v_i_2866_);
v_v_2883_ = lean_array_fget_borrowed(v_vals_2865_, v_i_2866_);
lean_inc_ref(v_f_2863_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc_ref(v___y_2871_);
lean_inc(v___y_2870_);
lean_inc_ref(v___y_2869_);
lean_inc(v_v_2883_);
lean_inc(v_k_2882_);
v___x_2884_ = lean_apply_12(v_f_2863_, v_acc_2867_, v_k_2882_, v_v_2883_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, lean_box(0));
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
if (lean_obj_tag(v_a_2885_) == 0)
{
lean_dec_ref_known(v_a_2885_, 1);
lean_dec(v_i_2866_);
lean_dec_ref(v_f_2863_);
return v___x_2884_;
}
else
{
lean_object* v_a_2886_; lean_object* v_fst_2887_; lean_object* v_snd_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec_ref_known(v___x_2884_, 1);
v_a_2886_ = lean_ctor_get(v_a_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v_a_2885_, 1);
v_fst_2887_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_fst_2887_);
v_snd_2888_ = lean_ctor_get(v_a_2886_, 1);
lean_inc(v_snd_2888_);
lean_dec(v_a_2886_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_add(v_i_2866_, v___x_2889_);
lean_dec(v_i_2866_);
v_i_2866_ = v___x_2890_;
v_acc_2867_ = v_fst_2887_;
v___y_2868_ = v_snd_2888_;
goto _start;
}
}
else
{
lean_dec(v_i_2866_);
lean_dec_ref(v_f_2863_);
return v___x_2884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg___boxed(lean_object* v_f_2892_, lean_object* v_keys_2893_, lean_object* v_vals_2894_, lean_object* v_i_2895_, lean_object* v_acc_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2892_, v_keys_2893_, v_vals_2894_, v_i_2895_, v_acc_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_vals_2894_);
lean_dec_ref(v_keys_2893_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(lean_object* v_f_2907_, lean_object* v_as_2908_, size_t v_i_2909_, size_t v_stop_2910_, lean_object* v_b_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v___y_2928_; uint8_t v___x_2933_; 
v___x_2933_ = lean_usize_dec_eq(v_i_2909_, v_stop_2910_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_array_uget_borrowed(v_as_2908_, v_i_2909_);
switch(lean_obj_tag(v___x_2934_))
{
case 0:
{
lean_object* v_key_2935_; lean_object* v_val_2936_; lean_object* v___x_2937_; 
v_key_2935_ = lean_ctor_get(v___x_2934_, 0);
v_val_2936_ = lean_ctor_get(v___x_2934_, 1);
lean_inc_ref(v_f_2907_);
lean_inc(v___y_2919_);
lean_inc_ref(v___y_2918_);
lean_inc(v___y_2917_);
lean_inc_ref(v___y_2916_);
lean_inc_ref(v___y_2915_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
lean_inc(v_val_2936_);
lean_inc(v_key_2935_);
v___x_2937_ = lean_apply_12(v_f_2907_, v_b_2911_, v_key_2935_, v_val_2936_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, lean_box(0));
v___y_2928_ = v___x_2937_;
goto v___jp_2927_;
}
case 1:
{
lean_object* v_node_2938_; lean_object* v___x_2939_; 
v_node_2938_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_node_2938_);
lean_inc_ref(v_f_2907_);
v___x_2939_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_2907_, v_node_2938_, v_b_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
v___y_2928_ = v___x_2939_;
goto v___jp_2927_;
}
default: 
{
v_fst_2922_ = v_b_2911_;
v_snd_2923_ = v___y_2912_;
goto v___jp_2921_;
}
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v_f_2907_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_b_2911_);
lean_ctor_set(v___x_2940_, 1, v___y_2912_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
v___jp_2921_:
{
size_t v___x_2924_; size_t v___x_2925_; 
v___x_2924_ = ((size_t)1ULL);
v___x_2925_ = lean_usize_add(v_i_2909_, v___x_2924_);
v_i_2909_ = v___x_2925_;
v_b_2911_ = v_fst_2922_;
v___y_2912_ = v_snd_2923_;
goto _start;
}
v___jp_2927_:
{
if (lean_obj_tag(v___y_2928_) == 0)
{
lean_object* v_a_2929_; 
v_a_2929_ = lean_ctor_get(v___y_2928_, 0);
if (lean_obj_tag(v_a_2929_) == 0)
{
lean_dec_ref(v_f_2907_);
return v___y_2928_;
}
else
{
lean_object* v_a_2930_; lean_object* v_fst_2931_; lean_object* v_snd_2932_; 
lean_inc_ref(v_a_2929_);
lean_dec_ref_known(v___y_2928_, 1);
v_a_2930_ = lean_ctor_get(v_a_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v_a_2929_, 1);
v_fst_2931_ = lean_ctor_get(v_a_2930_, 0);
lean_inc(v_fst_2931_);
v_snd_2932_ = lean_ctor_get(v_a_2930_, 1);
lean_inc(v_snd_2932_);
lean_dec(v_a_2930_);
v_fst_2922_ = v_fst_2931_;
v_snd_2923_ = v_snd_2932_;
goto v___jp_2921_;
}
}
else
{
lean_dec_ref(v_f_2907_);
return v___y_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(lean_object* v_f_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
lean_object* v_es_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2970_; 
v_es_2955_ = lean_ctor_get(v_x_2944_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2944_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2957_ = v_x_2944_;
v_isShared_2958_ = v_isSharedCheck_2970_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_es_2955_);
lean_dec(v_x_2944_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2970_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_array_get_size(v_es_2955_);
v___x_2961_ = lean_nat_dec_lt(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
lean_dec_ref(v_es_2955_);
lean_dec_ref(v_f_2943_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_x_2945_);
lean_ctor_set(v___x_2962_, 1, v___y_2946_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 1);
lean_ctor_set(v___x_2957_, 0, v___x_2962_);
v___x_2964_ = v___x_2957_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
else
{
size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
lean_del_object(v___x_2957_);
v___x_2967_ = ((size_t)0ULL);
v___x_2968_ = lean_usize_of_nat(v___x_2960_);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2943_, v_es_2955_, v___x_2967_, v___x_2968_, v_x_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec_ref(v_es_2955_);
return v___x_2969_;
}
}
}
else
{
lean_object* v_ks_2971_; lean_object* v_vs_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_ks_2971_ = lean_ctor_get(v_x_2944_, 0);
lean_inc_ref(v_ks_2971_);
v_vs_2972_ = lean_ctor_get(v_x_2944_, 1);
lean_inc_ref(v_vs_2972_);
lean_dec_ref_known(v_x_2944_, 2);
v___x_2973_ = lean_unsigned_to_nat(0u);
v___x_2974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_2943_, v_ks_2971_, v_vs_2972_, v___x_2973_, v_x_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec_ref(v_vs_2972_);
lean_dec_ref(v_ks_2971_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg___boxed(lean_object* v_f_2975_, lean_object* v_x_2976_, lean_object* v_x_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_2975_, v_x_2976_, v_x_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg___boxed(lean_object* v_f_2988_, lean_object* v_as_2989_, lean_object* v_i_2990_, lean_object* v_stop_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
size_t v_i_boxed_3002_; size_t v_stop_boxed_3003_; lean_object* v_res_3004_; 
v_i_boxed_3002_ = lean_unbox_usize(v_i_2990_);
lean_dec(v_i_2990_);
v_stop_boxed_3003_ = lean_unbox_usize(v_stop_2991_);
lean_dec(v_stop_2991_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_2988_, v_as_2989_, v_i_boxed_3002_, v_stop_boxed_3003_, v_b_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v_as_2989_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_f_3005_, lean_object* v_x_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
lean_inc(v___y_3016_);
lean_inc_ref(v___y_3015_);
lean_inc(v___y_3014_);
lean_inc_ref(v___y_3013_);
lean_inc_ref(v___y_3012_);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
v___x_3018_ = lean_apply_11(v_f_3005_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, lean_box(0));
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_f_3019_, lean_object* v_x_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0(v_f_3019_, v_x_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(lean_object* v_map_3033_, lean_object* v_f_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___f_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___f_3044_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3044_, 0, v_f_3034_);
v___x_3045_ = lean_box(0);
v___x_3046_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v___f_3044_, v_map_3033_, v___x_3045_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_map_3047_, lean_object* v_f_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_3047_, v_f_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(lean_object* v_f_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
if (lean_obj_tag(v_x_3061_) == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v_f_3059_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v_x_3060_);
lean_ctor_set(v___x_3071_, 1, v___y_3062_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
else
{
lean_object* v_key_3074_; lean_object* v_value_3075_; lean_object* v_tail_3076_; lean_object* v___x_3077_; 
v_key_3074_ = lean_ctor_get(v_x_3061_, 0);
lean_inc(v_key_3074_);
v_value_3075_ = lean_ctor_get(v_x_3061_, 1);
lean_inc(v_value_3075_);
v_tail_3076_ = lean_ctor_get(v_x_3061_, 2);
lean_inc(v_tail_3076_);
lean_dec_ref_known(v_x_3061_, 3);
lean_inc_ref(v_f_3059_);
lean_inc(v___y_3069_);
lean_inc_ref(v___y_3068_);
lean_inc(v___y_3067_);
lean_inc_ref(v___y_3066_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
v___x_3077_ = lean_apply_11(v_f_3059_, v_key_3074_, v_value_3075_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, lean_box(0));
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
if (lean_obj_tag(v_a_3078_) == 0)
{
lean_dec_ref_known(v_a_3078_, 1);
lean_dec(v_tail_3076_);
lean_dec_ref(v_f_3059_);
return v___x_3077_;
}
else
{
lean_object* v_a_3079_; lean_object* v_fst_3080_; lean_object* v_snd_3081_; 
lean_dec_ref_known(v___x_3077_, 1);
v_a_3079_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v_a_3078_, 1);
v_fst_3080_ = lean_ctor_get(v_a_3079_, 0);
lean_inc(v_fst_3080_);
v_snd_3081_ = lean_ctor_get(v_a_3079_, 1);
lean_inc(v_snd_3081_);
lean_dec(v_a_3079_);
v_x_3060_ = v_fst_3080_;
v_x_3061_ = v_tail_3076_;
v___y_3062_ = v_snd_3081_;
goto _start;
}
}
else
{
lean_dec(v_tail_3076_);
lean_dec_ref(v_f_3059_);
return v___x_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_f_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3083_, v_x_3084_, v_x_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(lean_object* v_f_3096_, lean_object* v_as_3097_, size_t v_i_3098_, size_t v_stop_3099_, lean_object* v_b_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_usize_dec_eq(v_i_3098_, v_stop_3099_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = lean_array_uget_borrowed(v_as_3097_, v_i_3098_);
v___x_3112_ = lean_box(0);
lean_inc(v___x_3111_);
lean_inc_ref(v_f_3096_);
v___x_3113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__2(v_f_3096_, v___x_3112_, v___x_3111_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
if (lean_obj_tag(v_a_3114_) == 0)
{
lean_dec_ref_known(v_a_3114_, 1);
lean_dec_ref(v_f_3096_);
return v___x_3113_;
}
else
{
lean_object* v_a_3115_; lean_object* v_fst_3116_; lean_object* v_snd_3117_; size_t v___x_3118_; size_t v___x_3119_; 
lean_dec_ref_known(v___x_3113_, 1);
v_a_3115_ = lean_ctor_get(v_a_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v_a_3114_, 1);
v_fst_3116_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_fst_3116_);
v_snd_3117_ = lean_ctor_get(v_a_3115_, 1);
lean_inc(v_snd_3117_);
lean_dec(v_a_3115_);
v___x_3118_ = ((size_t)1ULL);
v___x_3119_ = lean_usize_add(v_i_3098_, v___x_3118_);
v_i_3098_ = v___x_3119_;
v_b_3100_ = v_fst_3116_;
v___y_3101_ = v_snd_3117_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_3096_);
return v___x_3113_;
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_f_3096_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v_b_3100_);
lean_ctor_set(v___x_3121_, 1, v___y_3101_);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
return v___x_3123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4___boxed(lean_object* v_f_3124_, lean_object* v_as_3125_, lean_object* v_i_3126_, lean_object* v_stop_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
size_t v_i_boxed_3138_; size_t v_stop_boxed_3139_; lean_object* v_res_3140_; 
v_i_boxed_3138_ = lean_unbox_usize(v_i_3126_);
lean_dec(v_i_3126_);
v_stop_boxed_3139_ = lean_unbox_usize(v_stop_3127_);
lean_dec(v_stop_3127_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3124_, v_as_3125_, v_i_boxed_3138_, v_stop_boxed_3139_, v_b_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v_as_3125_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(lean_object* v_env_3141_, lean_object* v_f_3142_, lean_object* v_name_3143_, lean_object* v_c_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
uint8_t v___x_3154_; 
lean_inc(v_name_3143_);
v___x_3154_ = l_Lean_Meta_allowCompletion(v_env_3141_, v_name_3143_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec_ref(v_c_3144_);
lean_dec(v_name_3143_);
lean_dec_ref(v_f_3142_);
v___x_3155_ = lean_box(0);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___y_3145_);
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_inc_ref(v_c_3144_);
v___x_3159_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionKindForDecl___boxed), 6, 1);
lean_closure_set(v___x_3159_, 0, v_c_3144_);
lean_inc(v_name_3143_);
v___x_3160_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getCompletionTagsForDecl___boxed), 6, 1);
lean_closure_set(v___x_3160_, 0, v_name_3143_);
v___x_3161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3161_, 0, v_c_3144_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
lean_ctor_set(v___x_3161_, 2, v___x_3160_);
lean_inc(v___y_3152_);
lean_inc_ref(v___y_3151_);
lean_inc(v___y_3150_);
lean_inc_ref(v___y_3149_);
lean_inc_ref(v___y_3148_);
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
v___x_3162_ = lean_apply_11(v_f_3142_, v_name_3143_, v___x_3161_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, lean_box(0));
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed(lean_object* v_env_3163_, lean_object* v_f_3164_, lean_object* v_name_3165_, lean_object* v_c_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0(v_env_3163_, v_f_3164_, v_name_3165_, v_c_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(lean_object* v_f_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; lean_object* v_env_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_st_ref_get(v___y_3185_);
v_env_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc_ref_n(v_env_3188_, 2);
lean_dec(v___x_3187_);
v___x_3189_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_3188_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v_buckets_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v_buckets_3191_ = lean_ctor_get(v_a_3190_, 1);
lean_inc_ref(v_buckets_3191_);
lean_dec(v_a_3190_);
lean_inc_ref(v_f_3177_);
lean_inc_ref(v_env_3188_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3192_, 0, v_env_3188_);
lean_closure_set(v___f_3192_, 1, v_f_3177_);
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = lean_array_get_size(v_buckets_3191_);
v___x_3195_ = lean_nat_dec_lt(v___x_3193_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v_map_u2082_3197_; lean_object* v___x_3198_; 
lean_dec_ref(v_buckets_3191_);
lean_dec_ref(v_f_3177_);
v___x_3196_ = l_Lean_Environment_constants(v_env_3188_);
v_map_u2082_3197_ = lean_ctor_get(v___x_3196_, 1);
lean_inc_ref(v_map_u2082_3197_);
lean_dec_ref(v___x_3196_);
v___x_3198_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3197_, v___f_3192_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3198_;
}
else
{
lean_object* v___x_3199_; size_t v___x_3200_; size_t v___x_3201_; lean_object* v___x_3202_; 
v___x_3199_ = lean_box(0);
v___x_3200_ = ((size_t)0ULL);
v___x_3201_ = lean_usize_of_nat(v___x_3194_);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__4(v_f_3177_, v_buckets_3191_, v___x_3200_, v___x_3201_, v___x_3199_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec_ref(v_buckets_3191_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
if (lean_obj_tag(v_a_3203_) == 0)
{
lean_dec_ref_known(v_a_3203_, 1);
lean_dec_ref(v___f_3192_);
lean_dec_ref(v_env_3188_);
return v___x_3202_;
}
else
{
lean_object* v_a_3204_; lean_object* v_snd_3205_; lean_object* v___x_3206_; lean_object* v_map_u2082_3207_; lean_object* v___x_3208_; 
lean_dec_ref_known(v___x_3202_, 1);
v_a_3204_ = lean_ctor_get(v_a_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v_a_3203_, 1);
v_snd_3205_ = lean_ctor_get(v_a_3204_, 1);
lean_inc(v_snd_3205_);
lean_dec(v_a_3204_);
v___x_3206_ = l_Lean_Environment_constants(v_env_3188_);
v_map_u2082_3207_ = lean_ctor_get(v___x_3206_, 1);
lean_inc_ref(v_map_u2082_3207_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_u2082_3207_, v___f_3192_, v_snd_3205_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3208_;
}
}
else
{
lean_dec_ref(v___f_3192_);
lean_dec_ref(v_env_3188_);
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v_env_3188_);
lean_dec(v___y_3178_);
lean_dec_ref(v_f_3177_);
v_a_3209_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3189_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3189_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0___boxed(lean_object* v_f_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v_f_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(lean_object* v_f_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___f_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___f_3237_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3237_, 0, v_f_3228_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = l_Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0(v___f_3237_, v___x_3238_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3259_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3259_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3259_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
if (lean_obj_tag(v_a_3240_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3254_; 
v_a_3244_ = lean_ctor_get(v_a_3240_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3240_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3246_ = v_a_3240_;
v_isShared_3247_ = v_isSharedCheck_3254_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v_a_3240_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3254_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3249_);
v___x_3251_ = v___x_3242_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_dec_ref_known(v_a_3240_, 1);
v___x_3255_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3255_);
v___x_3257_ = v___x_3242_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
v_a_3260_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3239_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3239_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0___boxed(lean_object* v_f_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v_f_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(lean_object* v_id_3280_, uint8_t v_danglingDot_3281_, lean_object* v_as_3282_, size_t v_sz_3283_, size_t v_i_3284_, lean_object* v_b_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_usize_dec_lt(v_i_3284_, v_sz_3283_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_b_3285_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
else
{
lean_object* v_snd_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3345_; 
v_snd_3292_ = lean_ctor_get(v_b_3285_, 1);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_b_3285_);
if (v_isSharedCheck_3345_ == 0)
{
lean_object* v_unused_3346_; 
v_unused_3346_ = lean_ctor_get(v_b_3285_, 0);
lean_dec(v_unused_3346_);
v___x_3294_ = v_b_3285_;
v_isShared_3295_ = v_isSharedCheck_3345_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_snd_3292_);
lean_dec(v_b_3285_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3345_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v_a_3298_; lean_object* v_a_3305_; 
v___x_3296_ = lean_box(0);
v_a_3305_ = lean_array_uget(v_as_3282_, v_i_3284_);
if (lean_obj_tag(v_a_3305_) == 0)
{
v_a_3298_ = v_snd_3292_;
goto v___jp_3297_;
}
else
{
lean_object* v_val_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_snd_3292_);
v_val_3306_ = lean_ctor_get(v_a_3305_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_a_3305_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3308_ = v_a_3305_;
v_isShared_3309_ = v_isSharedCheck_3344_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_val_3306_);
lean_dec(v_a_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3344_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3310_ = lean_box(0);
v___x_3311_ = l_Lean_LocalDecl_userName(v_val_3306_);
v___x_3312_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3280_, v___x_3311_, v_danglingDot_3281_);
if (v___x_3312_ == 0)
{
lean_dec(v___x_3311_);
lean_del_object(v___x_3308_);
lean_dec(v_val_3306_);
v_a_3298_ = v___x_3310_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = l_Lean_LocalDecl_fvarId(v_val_3306_);
lean_dec(v_val_3306_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3313_);
v___x_3315_ = v___x_3308_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = 5;
v___x_3317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3318_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3311_, v___x_3315_, v___x_3316_, v___x_3317_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3334_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3334_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3334_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
if (lean_obj_tag(v_a_3319_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3333_; 
lean_del_object(v___x_3294_);
v_a_3323_ = lean_ctor_get(v_a_3319_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_a_3319_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3325_ = v_a_3319_;
v_isShared_3326_ = v_isSharedCheck_3333_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v_a_3319_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3333_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3330_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3328_);
v___x_3330_ = v___x_3321_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3328_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3319_, 1);
lean_del_object(v___x_3321_);
v_a_3298_ = v___x_3310_;
goto v___jp_3297_;
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_del_object(v___x_3294_);
v_a_3335_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3318_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3318_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
}
v___jp_3297_:
{
lean_object* v___x_3300_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 1, v_a_3298_);
lean_ctor_set(v___x_3294_, 0, v___x_3296_);
v___x_3300_ = v___x_3294_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_a_3298_);
v___x_3300_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
size_t v___x_3301_; size_t v___x_3302_; 
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3284_, v___x_3301_);
v_i_3284_ = v___x_3302_;
v_b_3285_ = v___x_3300_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___boxed(lean_object* v_id_3347_, lean_object* v_danglingDot_3348_, lean_object* v_as_3349_, lean_object* v_sz_3350_, lean_object* v_i_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
uint8_t v_danglingDot_boxed_3356_; size_t v_sz_boxed_3357_; size_t v_i_boxed_3358_; lean_object* v_res_3359_; 
v_danglingDot_boxed_3356_ = lean_unbox(v_danglingDot_3348_);
v_sz_boxed_3357_ = lean_unbox_usize(v_sz_3350_);
lean_dec(v_sz_3350_);
v_i_boxed_3358_ = lean_unbox_usize(v_i_3351_);
lean_dec(v_i_3351_);
v_res_3359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3347_, v_danglingDot_boxed_3356_, v_as_3349_, v_sz_boxed_3357_, v_i_boxed_3358_, v_b_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v_as_3349_);
lean_dec(v_id_3347_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(lean_object* v_id_3360_, uint8_t v_danglingDot_3361_, lean_object* v_as_3362_, size_t v_sz_3363_, size_t v_i_3364_, lean_object* v_b_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_usize_dec_lt(v_i_3364_, v_sz_3363_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_b_3365_);
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
return v___x_3376_;
}
else
{
lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3430_; 
v_snd_3377_ = lean_ctor_get(v_b_3365_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_b_3365_);
if (v_isSharedCheck_3430_ == 0)
{
lean_object* v_unused_3431_; 
v_unused_3431_ = lean_ctor_get(v_b_3365_, 0);
lean_dec(v_unused_3431_);
v___x_3379_ = v_b_3365_;
v_isShared_3380_ = v_isSharedCheck_3430_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_dec(v_b_3365_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3430_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v_a_3383_; lean_object* v_a_3390_; 
v___x_3381_ = lean_box(0);
v_a_3390_ = lean_array_uget(v_as_3362_, v_i_3364_);
if (lean_obj_tag(v_a_3390_) == 0)
{
v_a_3383_ = v_snd_3377_;
goto v___jp_3382_;
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_snd_3377_);
v_val_3391_ = lean_ctor_get(v_a_3390_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3393_ = v_a_3390_;
v_isShared_3394_ = v_isSharedCheck_3429_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_val_3391_);
lean_dec(v_a_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3429_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = lean_box(0);
v___x_3396_ = l_Lean_LocalDecl_userName(v_val_3391_);
v___x_3397_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3360_, v___x_3396_, v_danglingDot_3361_);
if (v___x_3397_ == 0)
{
lean_dec(v___x_3396_);
lean_del_object(v___x_3393_);
lean_dec(v_val_3391_);
v_a_3383_ = v___x_3395_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = l_Lean_LocalDecl_fvarId(v_val_3391_);
lean_dec(v_val_3391_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3398_);
v___x_3400_ = v___x_3393_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = 5;
v___x_3402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3403_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3396_, v___x_3400_, v___x_3401_, v___x_3402_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3419_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3419_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3419_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
if (lean_obj_tag(v_a_3404_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3418_; 
lean_del_object(v___x_3379_);
v_a_3408_ = lean_ctor_get(v_a_3404_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3404_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3410_ = v_a_3404_;
v_isShared_3411_ = v_isSharedCheck_3418_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v_a_3404_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3418_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3413_);
v___x_3415_ = v___x_3406_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3404_, 1);
lean_del_object(v___x_3406_);
v_a_3383_ = v___x_3395_;
goto v___jp_3382_;
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_del_object(v___x_3379_);
v_a_3420_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3403_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3403_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
}
}
v___jp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v_a_3383_);
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3385_ = v___x_3379_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3383_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = ((size_t)1ULL);
v___x_3387_ = lean_usize_add(v_i_3364_, v___x_3386_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_3360_, v_danglingDot_3361_, v_as_3362_, v_sz_3363_, v___x_3387_, v___x_3385_, v___y_3366_, v___y_3367_);
return v___x_3388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17___boxed(lean_object* v_id_3432_, lean_object* v_danglingDot_3433_, lean_object* v_as_3434_, lean_object* v_sz_3435_, lean_object* v_i_3436_, lean_object* v_b_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v_danglingDot_boxed_3446_; size_t v_sz_boxed_3447_; size_t v_i_boxed_3448_; lean_object* v_res_3449_; 
v_danglingDot_boxed_3446_ = lean_unbox(v_danglingDot_3433_);
v_sz_boxed_3447_ = lean_unbox_usize(v_sz_3435_);
lean_dec(v_sz_3435_);
v_i_boxed_3448_ = lean_unbox_usize(v_i_3436_);
lean_dec(v_i_3436_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3432_, v_danglingDot_boxed_3446_, v_as_3434_, v_sz_boxed_3447_, v_i_boxed_3448_, v_b_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec_ref(v_as_3434_);
lean_dec(v_id_3432_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(lean_object* v_init_3450_, lean_object* v_id_3451_, uint8_t v_danglingDot_3452_, lean_object* v_n_3453_, lean_object* v_b_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
if (lean_obj_tag(v_n_3453_) == 0)
{
lean_object* v_cs_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; size_t v_sz_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
v_cs_3463_ = lean_ctor_get(v_n_3453_, 0);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v_b_3454_);
v_sz_3466_ = lean_array_size(v_cs_3463_);
v___x_3467_ = ((size_t)0ULL);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3450_, v_id_3451_, v_danglingDot_3452_, v_cs_3463_, v_sz_3466_, v___x_3467_, v___x_3465_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3505_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3505_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3505_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_a_3469_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3483_; 
v_a_3473_ = lean_ctor_get(v_a_3469_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_a_3469_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3475_ = v_a_3469_;
v_isShared_3476_ = v_isSharedCheck_3483_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v_a_3469_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3483_;
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
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3478_);
v___x_3480_ = v___x_3471_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3504_; 
v_a_3484_ = lean_ctor_get(v_a_3469_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_a_3469_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3486_ = v_a_3469_;
v_isShared_3487_ = v_isSharedCheck_3504_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v_a_3469_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3504_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v_fst_3488_; 
v_fst_3488_ = lean_ctor_get(v_a_3484_, 0);
if (lean_obj_tag(v_fst_3488_) == 0)
{
lean_object* v_snd_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v_snd_3489_ = lean_ctor_get(v_a_3484_, 1);
lean_inc(v_snd_3489_);
lean_dec(v_a_3484_);
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_snd_3489_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3490_);
v___x_3492_ = v___x_3486_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3492_);
v___x_3494_ = v___x_3471_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
else
{
lean_object* v_val_3497_; lean_object* v___x_3499_; 
lean_inc_ref(v_fst_3488_);
lean_dec(v_a_3484_);
v_val_3497_ = lean_ctor_get(v_fst_3488_, 0);
lean_inc(v_val_3497_);
lean_dec_ref_known(v_fst_3488_, 1);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v_val_3497_);
v___x_3499_ = v___x_3486_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_val_3497_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3499_);
v___x_3501_ = v___x_3471_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
v_a_3506_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3468_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3468_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v_vs_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; size_t v_sz_3517_; size_t v___x_3518_; lean_object* v___x_3519_; 
v_vs_3514_ = lean_ctor_get(v_n_3453_, 0);
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
lean_ctor_set(v___x_3516_, 1, v_b_3454_);
v_sz_3517_ = lean_array_size(v_vs_3514_);
v___x_3518_ = ((size_t)0ULL);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17(v_id_3451_, v_danglingDot_3452_, v_vs_3514_, v_sz_3517_, v___x_3518_, v___x_3516_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3556_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3556_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3556_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
if (lean_obj_tag(v_a_3520_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3534_; 
v_a_3524_ = lean_ctor_get(v_a_3520_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3526_ = v_a_3520_;
v_isShared_3527_ = v_isSharedCheck_3534_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v_a_3520_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3534_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3529_);
v___x_3531_ = v___x_3522_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3555_; 
v_a_3535_ = lean_ctor_get(v_a_3520_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3537_ = v_a_3520_;
v_isShared_3538_ = v_isSharedCheck_3555_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v_a_3520_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3555_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v_fst_3539_; 
v_fst_3539_ = lean_ctor_get(v_a_3535_, 0);
if (lean_obj_tag(v_fst_3539_) == 0)
{
lean_object* v_snd_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v_snd_3540_ = lean_ctor_get(v_a_3535_, 1);
lean_inc(v_snd_3540_);
lean_dec(v_a_3535_);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_snd_3540_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3541_);
v___x_3543_ = v___x_3537_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3543_);
v___x_3545_ = v___x_3522_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_val_3548_; lean_object* v___x_3550_; 
lean_inc_ref(v_fst_3539_);
lean_dec(v_a_3535_);
v_val_3548_ = lean_ctor_get(v_fst_3539_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v_fst_3539_, 1);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_val_3548_);
v___x_3550_ = v___x_3537_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_val_3548_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3550_);
v___x_3552_ = v___x_3522_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
v_a_3557_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3519_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3519_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(lean_object* v_init_3565_, lean_object* v_id_3566_, uint8_t v_danglingDot_3567_, lean_object* v_as_3568_, size_t v_sz_3569_, size_t v_i_3570_, lean_object* v_b_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_usize_dec_lt(v_i_3570_, v_sz_3569_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3581_, 0, v_b_3571_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
else
{
lean_object* v_snd_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3636_; 
v_snd_3583_ = lean_ctor_get(v_b_3571_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_b_3571_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v_b_3571_, 0);
lean_dec(v_unused_3637_);
v___x_3585_ = v_b_3571_;
v_isShared_3586_ = v_isSharedCheck_3636_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_snd_3583_);
lean_dec(v_b_3571_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3636_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_a_3587_; lean_object* v___x_3588_; 
v_a_3587_ = lean_array_uget_borrowed(v_as_3568_, v_i_3570_);
lean_inc(v_snd_3583_);
v___x_3588_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3565_, v_id_3566_, v_danglingDot_3567_, v_a_3587_, v_snd_3583_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3627_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3627_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3627_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
if (lean_obj_tag(v_a_3589_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3603_; 
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
v_a_3593_ = lean_ctor_get(v_a_3589_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_a_3589_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3595_ = v_a_3589_;
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v_a_3589_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3598_);
v___x_3600_ = v___x_3591_;
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
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3626_; 
v_a_3604_ = lean_ctor_get(v_a_3589_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_a_3589_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3606_ = v_a_3589_;
v_isShared_3607_ = v_isSharedCheck_3626_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v_a_3589_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3626_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
if (lean_obj_tag(v_a_3604_) == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_a_3604_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3608_);
v___x_3610_ = v___x_3585_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_snd_3583_);
v___x_3610_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3610_);
v___x_3612_ = v___x_3606_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3612_);
v___x_3614_ = v___x_3591_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_del_object(v___x_3606_);
lean_del_object(v___x_3591_);
lean_dec(v_snd_3583_);
v_a_3618_ = lean_ctor_get(v_a_3604_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v_a_3604_, 1);
v___x_3619_ = lean_box(0);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v_a_3618_);
lean_ctor_set(v___x_3585_, 0, v___x_3619_);
v___x_3621_ = v___x_3585_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_a_3618_);
v___x_3621_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
size_t v___x_3622_; size_t v___x_3623_; 
v___x_3622_ = ((size_t)1ULL);
v___x_3623_ = lean_usize_add(v_i_3570_, v___x_3622_);
v_i_3570_ = v___x_3623_;
v_b_3571_ = v___x_3621_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
v_a_3628_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3588_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3588_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16___boxed(lean_object* v_init_3638_, lean_object* v_id_3639_, lean_object* v_danglingDot_3640_, lean_object* v_as_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
uint8_t v_danglingDot_boxed_3653_; size_t v_sz_boxed_3654_; size_t v_i_boxed_3655_; lean_object* v_res_3656_; 
v_danglingDot_boxed_3653_ = lean_unbox(v_danglingDot_3640_);
v_sz_boxed_3654_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3655_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__16(v_init_3638_, v_id_3639_, v_danglingDot_boxed_3653_, v_as_3641_, v_sz_boxed_3654_, v_i_boxed_3655_, v_b_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v_as_3641_);
lean_dec(v_id_3639_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11___boxed(lean_object* v_init_3657_, lean_object* v_id_3658_, lean_object* v_danglingDot_3659_, lean_object* v_n_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_danglingDot_boxed_3670_; lean_object* v_res_3671_; 
v_danglingDot_boxed_3670_ = lean_unbox(v_danglingDot_3659_);
v_res_3671_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3657_, v_id_3658_, v_danglingDot_boxed_3670_, v_n_3660_, v_b_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_n_3660_);
lean_dec(v_id_3658_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(lean_object* v_id_3672_, uint8_t v_danglingDot_3673_, lean_object* v_as_3674_, size_t v_sz_3675_, size_t v_i_3676_, lean_object* v_b_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
uint8_t v___x_3681_; 
v___x_3681_ = lean_usize_dec_lt(v_i_3676_, v_sz_3675_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3682_, 0, v_b_3677_);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
else
{
lean_object* v_snd_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3737_; 
v_snd_3684_ = lean_ctor_get(v_b_3677_, 1);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_b_3677_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; 
v_unused_3738_ = lean_ctor_get(v_b_3677_, 0);
lean_dec(v_unused_3738_);
v___x_3686_ = v_b_3677_;
v_isShared_3687_ = v_isSharedCheck_3737_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_snd_3684_);
lean_dec(v_b_3677_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3737_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v_a_3690_; lean_object* v_a_3697_; 
v___x_3688_ = lean_box(0);
v_a_3697_ = lean_array_uget(v_as_3674_, v_i_3676_);
if (lean_obj_tag(v_a_3697_) == 0)
{
v_a_3690_ = v_snd_3684_;
goto v___jp_3689_;
}
else
{
lean_object* v_val_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v_snd_3684_);
v_val_3698_ = lean_ctor_get(v_a_3697_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_a_3697_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3700_ = v_a_3697_;
v_isShared_3701_ = v_isSharedCheck_3736_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_val_3698_);
lean_dec(v_a_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3736_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3702_ = lean_box(0);
v___x_3703_ = l_Lean_LocalDecl_userName(v_val_3698_);
v___x_3704_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3672_, v___x_3703_, v_danglingDot_3673_);
if (v___x_3704_ == 0)
{
lean_dec(v___x_3703_);
lean_del_object(v___x_3700_);
lean_dec(v_val_3698_);
v_a_3690_ = v___x_3702_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3705_ = l_Lean_LocalDecl_fvarId(v_val_3698_);
lean_dec(v_val_3698_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v___x_3705_);
v___x_3707_ = v___x_3700_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
uint8_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = 5;
v___x_3709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3710_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3703_, v___x_3707_, v___x_3708_, v___x_3709_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3726_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3713_ = v___x_3710_;
v_isShared_3714_ = v_isSharedCheck_3726_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3710_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3726_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
if (lean_obj_tag(v_a_3711_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3725_; 
lean_del_object(v___x_3686_);
v_a_3715_ = lean_ctor_get(v_a_3711_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3711_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3717_ = v_a_3711_;
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v_a_3711_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3720_);
v___x_3722_ = v___x_3713_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3711_, 1);
lean_del_object(v___x_3713_);
v_a_3690_ = v___x_3702_;
goto v___jp_3689_;
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3686_);
v_a_3727_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3710_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3710_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
}
v___jp_3689_:
{
lean_object* v___x_3692_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v_a_3690_);
lean_ctor_set(v___x_3686_, 0, v___x_3688_);
v___x_3692_ = v___x_3686_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_a_3690_);
v___x_3692_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
size_t v___x_3693_; size_t v___x_3694_; 
v___x_3693_ = ((size_t)1ULL);
v___x_3694_ = lean_usize_add(v_i_3676_, v___x_3693_);
v_i_3676_ = v___x_3694_;
v_b_3677_ = v___x_3692_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_id_3739_, lean_object* v_danglingDot_3740_, lean_object* v_as_3741_, lean_object* v_sz_3742_, lean_object* v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v_danglingDot_boxed_3748_; size_t v_sz_boxed_3749_; size_t v_i_boxed_3750_; lean_object* v_res_3751_; 
v_danglingDot_boxed_3748_ = lean_unbox(v_danglingDot_3740_);
v_sz_boxed_3749_ = lean_unbox_usize(v_sz_3742_);
lean_dec(v_sz_3742_);
v_i_boxed_3750_ = lean_unbox_usize(v_i_3743_);
lean_dec(v_i_3743_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3739_, v_danglingDot_boxed_3748_, v_as_3741_, v_sz_boxed_3749_, v_i_boxed_3750_, v_b_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec_ref(v_as_3741_);
lean_dec(v_id_3739_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(lean_object* v_id_3752_, uint8_t v_danglingDot_3753_, lean_object* v_as_3754_, size_t v_sz_3755_, size_t v_i_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v___x_3766_; 
v___x_3766_ = lean_usize_dec_lt(v_i_3756_, v_sz_3755_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_b_3757_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
else
{
lean_object* v_snd_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3822_; 
v_snd_3769_ = lean_ctor_get(v_b_3757_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_b_3757_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v_b_3757_, 0);
lean_dec(v_unused_3823_);
v___x_3771_ = v_b_3757_;
v_isShared_3772_ = v_isSharedCheck_3822_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_snd_3769_);
lean_dec(v_b_3757_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3822_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; lean_object* v_a_3775_; lean_object* v_a_3782_; 
v___x_3773_ = lean_box(0);
v_a_3782_ = lean_array_uget(v_as_3754_, v_i_3756_);
if (lean_obj_tag(v_a_3782_) == 0)
{
v_a_3775_ = v_snd_3769_;
goto v___jp_3774_;
}
else
{
lean_object* v_val_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_snd_3769_);
v_val_3783_ = lean_ctor_get(v_a_3782_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3782_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3785_ = v_a_3782_;
v_isShared_3786_ = v_isSharedCheck_3821_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_val_3783_);
lean_dec(v_a_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3821_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = lean_box(0);
v___x_3788_ = l_Lean_LocalDecl_userName(v_val_3783_);
v___x_3789_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3752_, v___x_3788_, v_danglingDot_3753_);
if (v___x_3789_ == 0)
{
lean_dec(v___x_3788_);
lean_del_object(v___x_3785_);
lean_dec(v_val_3783_);
v_a_3775_ = v___x_3787_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = l_Lean_LocalDecl_fvarId(v_val_3783_);
lean_dec(v_val_3783_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3790_);
v___x_3792_ = v___x_3785_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
uint8_t v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = 5;
v___x_3794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_3795_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_3788_, v___x_3792_, v___x_3793_, v___x_3794_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3811_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3811_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3811_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
if (lean_obj_tag(v_a_3796_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3810_; 
lean_del_object(v___x_3771_);
v_a_3800_ = lean_ctor_get(v_a_3796_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_a_3796_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3802_ = v_a_3796_;
v_isShared_3803_ = v_isSharedCheck_3810_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v_a_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3810_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v___x_3805_);
v___x_3807_ = v___x_3798_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3796_, 1);
lean_del_object(v___x_3798_);
v_a_3775_ = v___x_3787_;
goto v___jp_3774_;
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_del_object(v___x_3771_);
v_a_3812_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3795_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3795_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
}
}
v___jp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v_a_3775_);
lean_ctor_set(v___x_3771_, 0, v___x_3773_);
v___x_3777_ = v___x_3771_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_a_3775_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
size_t v___x_3778_; size_t v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = ((size_t)1ULL);
v___x_3779_ = lean_usize_add(v_i_3756_, v___x_3778_);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_3752_, v_danglingDot_3753_, v_as_3754_, v_sz_3755_, v___x_3779_, v___x_3777_, v___y_3758_, v___y_3759_);
return v___x_3780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12___boxed(lean_object* v_id_3824_, lean_object* v_danglingDot_3825_, lean_object* v_as_3826_, lean_object* v_sz_3827_, lean_object* v_i_3828_, lean_object* v_b_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
uint8_t v_danglingDot_boxed_3838_; size_t v_sz_boxed_3839_; size_t v_i_boxed_3840_; lean_object* v_res_3841_; 
v_danglingDot_boxed_3838_ = lean_unbox(v_danglingDot_3825_);
v_sz_boxed_3839_ = lean_unbox_usize(v_sz_3827_);
lean_dec(v_sz_3827_);
v_i_boxed_3840_ = lean_unbox_usize(v_i_3828_);
lean_dec(v_i_3828_);
v_res_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3824_, v_danglingDot_boxed_3838_, v_as_3826_, v_sz_boxed_3839_, v_i_boxed_3840_, v_b_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_as_3826_);
lean_dec(v_id_3824_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(lean_object* v_id_3842_, uint8_t v_danglingDot_3843_, lean_object* v_t_3844_, lean_object* v_init_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_b_3855_; lean_object* v_root_3858_; lean_object* v_tail_3859_; lean_object* v___x_3860_; 
v_root_3858_ = lean_ctor_get(v_t_3844_, 0);
v_tail_3859_ = lean_ctor_get(v_t_3844_, 1);
v___x_3860_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11(v_init_3845_, v_id_3842_, v_danglingDot_3843_, v_root_3858_, v_init_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3922_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3922_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3922_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
if (lean_obj_tag(v_a_3861_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3875_; 
v_a_3865_ = lean_ctor_get(v_a_3861_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_a_3861_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3867_ = v_a_3861_;
v_isShared_3868_ = v_isSharedCheck_3875_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v_a_3861_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3875_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3872_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3870_);
v___x_3872_ = v___x_3863_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v_a_3876_; 
lean_del_object(v___x_3863_);
v_a_3876_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v_a_3861_, 1);
if (lean_obj_tag(v_a_3876_) == 0)
{
lean_object* v_a_3877_; 
v_a_3877_ = lean_ctor_get(v_a_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v_a_3876_, 1);
v_b_3855_ = v_a_3877_;
goto v___jp_3854_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; size_t v_sz_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v_a_3878_ = lean_ctor_get(v_a_3876_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v_a_3876_, 1);
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v_a_3878_);
v_sz_3881_ = lean_array_size(v_tail_3859_);
v___x_3882_ = ((size_t)0ULL);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12(v_id_3842_, v_danglingDot_3843_, v_tail_3859_, v_sz_3881_, v___x_3882_, v___x_3880_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3913_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3913_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3913_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
if (lean_obj_tag(v_a_3884_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3898_; 
v_a_3888_ = lean_ctor_get(v_a_3884_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3890_ = v_a_3884_;
v_isShared_3891_ = v_isSharedCheck_3898_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v_a_3884_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3898_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3895_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3893_);
v___x_3895_ = v___x_3886_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3912_; 
v_a_3899_ = lean_ctor_get(v_a_3884_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3901_ = v_a_3884_;
v_isShared_3902_ = v_isSharedCheck_3912_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v_a_3884_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3912_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_fst_3903_; 
v_fst_3903_ = lean_ctor_get(v_a_3899_, 0);
if (lean_obj_tag(v_fst_3903_) == 0)
{
lean_object* v_snd_3904_; lean_object* v___x_3906_; 
v_snd_3904_ = lean_ctor_get(v_a_3899_, 1);
lean_inc(v_snd_3904_);
lean_dec(v_a_3899_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v_snd_3904_);
v___x_3906_ = v___x_3901_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_snd_3904_);
v___x_3906_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3906_);
v___x_3908_ = v___x_3886_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
else
{
lean_object* v_val_3911_; 
lean_inc_ref(v_fst_3903_);
lean_del_object(v___x_3901_);
lean_dec(v_a_3899_);
lean_del_object(v___x_3886_);
v_val_3911_ = lean_ctor_get(v_fst_3903_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v_fst_3903_, 1);
v_b_3855_ = v_val_3911_;
goto v___jp_3854_;
}
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3883_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3883_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_a_3923_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3860_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3860_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
v___jp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_b_3855_);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6___boxed(lean_object* v_id_3931_, lean_object* v_danglingDot_3932_, lean_object* v_t_3933_, lean_object* v_init_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
uint8_t v_danglingDot_boxed_3943_; lean_object* v_res_3944_; 
v_danglingDot_boxed_3943_ = lean_unbox(v_danglingDot_3932_);
v_res_3944_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_3931_, v_danglingDot_boxed_3943_, v_t_3933_, v_init_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec_ref(v_t_3933_);
lean_dec(v_id_3931_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(lean_object* v_as_3945_, size_t v_sz_3946_, size_t v_i_3947_, lean_object* v_b_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_usize_dec_lt(v_i_3947_, v_sz_3946_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_b_3948_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
return v___x_3954_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_array_uget_borrowed(v_as_3945_, v_i_3947_);
lean_inc(v_a_3955_);
v___x_3956_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg(v_a_3955_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
if (lean_obj_tag(v_a_3957_) == 0)
{
lean_dec_ref_known(v_a_3957_, 1);
return v___x_3956_;
}
else
{
lean_object* v___x_3958_; size_t v___x_3959_; size_t v___x_3960_; 
lean_dec_ref_known(v_a_3957_, 1);
lean_dec_ref_known(v___x_3956_, 1);
v___x_3958_ = lean_box(0);
v___x_3959_ = ((size_t)1ULL);
v___x_3960_ = lean_usize_add(v_i_3947_, v___x_3959_);
v_i_3947_ = v___x_3960_;
v_b_3948_ = v___x_3958_;
goto _start;
}
}
else
{
return v___x_3956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg___boxed(lean_object* v_as_3962_, lean_object* v_sz_3963_, lean_object* v_i_3964_, lean_object* v_b_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
size_t v_sz_boxed_3969_; size_t v_i_boxed_3970_; lean_object* v_res_3971_; 
v_sz_boxed_3969_ = lean_unbox_usize(v_sz_3963_);
lean_dec(v_sz_3963_);
v_i_boxed_3970_ = lean_unbox_usize(v_i_3964_);
lean_dec(v_i_3964_);
v_res_3971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_3962_, v_sz_boxed_3969_, v_i_boxed_3970_, v_b_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec_ref(v_as_3962_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(lean_object* v___x_3972_, lean_object* v_a_3973_, lean_object* v___x_3974_, lean_object* v_ns_3975_, lean_object* v_id_3976_, uint8_t v_danglingDot_3977_, lean_object* v_alias_3978_, lean_object* v_declNames_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v___y_3989_; uint8_t v___x_3993_; 
v___x_3993_ = l_Lean_Name_isPrefixOf(v_ns_3975_, v_alias_3978_);
if (v___x_3993_ == 0)
{
v___y_3989_ = v___x_3993_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v___x_3994_ = lean_box(0);
lean_inc(v_alias_3978_);
v___x_3995_ = l_Lean_Name_replacePrefix(v_alias_3978_, v_ns_3975_, v___x_3994_);
v___x_3996_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_3976_, v___x_3995_, v_danglingDot_3977_);
lean_dec(v___x_3995_);
v___y_3989_ = v___x_3996_;
goto v___jp_3988_;
}
v___jp_3988_:
{
if (v___y_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec(v_declNames_3979_);
lean_dec(v_alias_3978_);
lean_dec_ref(v___x_3974_);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3972_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; 
v___x_3992_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_3973_, v___x_3974_, v_alias_3978_, v_declNames_3979_, v___y_3980_, v___y_3981_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v_alias_3978_);
return v___x_3992_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_3997_, lean_object* v_a_3998_, lean_object* v___x_3999_, lean_object* v_ns_4000_, lean_object* v_id_4001_, lean_object* v_danglingDot_4002_, lean_object* v_alias_4003_, lean_object* v_declNames_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
uint8_t v_danglingDot_boxed_4013_; lean_object* v_res_4014_; 
v_danglingDot_boxed_4013_ = lean_unbox(v_danglingDot_4002_);
v_res_4014_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0(v___x_3997_, v_a_3998_, v___x_3999_, v_ns_4000_, v_id_4001_, v_danglingDot_boxed_4013_, v_alias_4003_, v_declNames_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v_id_4001_);
lean_dec(v_ns_4000_);
lean_dec_ref(v_a_3998_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(lean_object* v_a_4015_, lean_object* v___x_4016_, lean_object* v_id_4017_, uint8_t v_danglingDot_4018_, lean_object* v_as_x27_4019_, lean_object* v_b_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_a_4030_; 
if (lean_obj_tag(v_as_x27_4019_) == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec(v_id_4017_);
lean_dec_ref(v___x_4016_);
lean_dec_ref(v_a_4015_);
v___x_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_b_4020_);
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
else
{
lean_object* v_head_4035_; lean_object* v_tail_4036_; lean_object* v___x_4037_; 
v_head_4035_ = lean_ctor_get(v_as_x27_4019_, 0);
v_tail_4036_ = lean_ctor_get(v_as_x27_4019_, 1);
v___x_4037_ = lean_box(0);
if (lean_obj_tag(v_head_4035_) == 0)
{
lean_object* v_ns_4038_; lean_object* v___x_4039_; lean_object* v___f_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_ns_4038_ = lean_ctor_get(v_head_4035_, 0);
v___x_4039_ = lean_box(v_danglingDot_4018_);
lean_inc(v_id_4017_);
lean_inc(v_ns_4038_);
lean_inc_ref_n(v___x_4016_, 2);
lean_inc_ref(v_a_4015_);
v___f_4040_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4040_, 0, v___x_4037_);
lean_closure_set(v___f_4040_, 1, v_a_4015_);
lean_closure_set(v___f_4040_, 2, v___x_4016_);
lean_closure_set(v___f_4040_, 3, v_ns_4038_);
lean_closure_set(v___f_4040_, 4, v_id_4017_);
lean_closure_set(v___f_4040_, 5, v___x_4039_);
v___x_4041_ = l_Lean_getAliasState(v___x_4016_);
v___x_4042_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4041_, v___f_4040_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
if (lean_obj_tag(v_a_4043_) == 0)
{
lean_object* v_a_4044_; 
lean_dec(v_id_4017_);
lean_dec_ref(v___x_4016_);
lean_dec_ref(v_a_4015_);
v_a_4044_ = lean_ctor_get(v_a_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v_a_4043_, 1);
v_a_4030_ = v_a_4044_;
goto v___jp_4029_;
}
else
{
lean_dec_ref_known(v_a_4043_, 1);
v_as_x27_4019_ = v_tail_4036_;
v_b_4020_ = v___x_4037_;
goto _start;
}
}
else
{
lean_dec(v_id_4017_);
lean_dec_ref(v___x_4016_);
lean_dec_ref(v_a_4015_);
return v___x_4042_;
}
}
else
{
lean_object* v_id_4046_; lean_object* v_declName_4047_; uint8_t v___x_4048_; 
v_id_4046_ = lean_ctor_get(v_head_4035_, 0);
v_declName_4047_ = lean_ctor_get(v_head_4035_, 1);
lean_inc(v_declName_4047_);
lean_inc_ref(v___x_4016_);
v___x_4048_ = l_Lean_Server_Completion_allowCompletion(v_a_4015_, v___x_4016_, v_declName_4047_);
if (v___x_4048_ == 0)
{
v_as_x27_4019_ = v_tail_4036_;
v_b_4020_ = v___x_4037_;
goto _start;
}
else
{
uint8_t v___x_4050_; 
v___x_4050_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4017_, v_id_4046_, v_danglingDot_4018_);
if (v___x_4050_ == 0)
{
v_as_x27_4019_ = v_tail_4036_;
v_b_4020_ = v___x_4037_;
goto _start;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4052_ = l_Lean_Name_getString_x21(v_id_4046_);
v___x_4053_ = lean_box(0);
v___x_4054_ = l_Lean_Name_str___override(v___x_4053_, v___x_4052_);
lean_inc(v_declName_4047_);
v___x_4055_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4054_, v_declName_4047_, v___y_4021_, v___y_4022_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_dec_ref_known(v___x_4055_, 1);
v_as_x27_4019_ = v_tail_4036_;
v_b_4020_ = v___x_4037_;
goto _start;
}
else
{
lean_dec(v_id_4017_);
lean_dec_ref(v___x_4016_);
lean_dec_ref(v_a_4015_);
return v___x_4055_;
}
}
}
}
}
v___jp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v_a_4030_);
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg___boxed(lean_object* v_a_4057_, lean_object* v___x_4058_, lean_object* v_id_4059_, lean_object* v_danglingDot_4060_, lean_object* v_as_x27_4061_, lean_object* v_b_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
uint8_t v_danglingDot_boxed_4071_; lean_object* v_res_4072_; 
v_danglingDot_boxed_4071_ = lean_unbox(v_danglingDot_4060_);
v_res_4072_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4057_, v___x_4058_, v_id_4059_, v_danglingDot_boxed_4071_, v_as_x27_4061_, v_b_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v_as_x27_4061_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(lean_object* v_id_4073_, uint8_t v_danglingDot_4074_, lean_object* v_a_4075_, lean_object* v___x_4076_, lean_object* v_as_4077_, lean_object* v_as_x27_4078_, lean_object* v_b_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_a_4089_; 
if (lean_obj_tag(v_as_x27_4078_) == 0)
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec_ref(v___x_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_id_4073_);
v___x_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4092_, 0, v_b_4079_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
else
{
lean_object* v_head_4094_; lean_object* v_tail_4095_; lean_object* v___x_4096_; 
v_head_4094_ = lean_ctor_get(v_as_x27_4078_, 0);
v_tail_4095_ = lean_ctor_get(v_as_x27_4078_, 1);
v___x_4096_ = lean_box(0);
if (lean_obj_tag(v_head_4094_) == 0)
{
lean_object* v_ns_4097_; lean_object* v___x_4098_; lean_object* v___f_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_ns_4097_ = lean_ctor_get(v_head_4094_, 0);
v___x_4098_ = lean_box(v_danglingDot_4074_);
lean_inc(v_id_4073_);
lean_inc(v_ns_4097_);
lean_inc_ref_n(v___x_4076_, 2);
lean_inc_ref(v_a_4075_);
v___f_4099_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___lam__0___boxed), 16, 6);
lean_closure_set(v___f_4099_, 0, v___x_4096_);
lean_closure_set(v___f_4099_, 1, v_a_4075_);
lean_closure_set(v___f_4099_, 2, v___x_4076_);
lean_closure_set(v___f_4099_, 3, v_ns_4097_);
lean_closure_set(v___f_4099_, 4, v_id_4073_);
lean_closure_set(v___f_4099_, 5, v___x_4098_);
v___x_4100_ = l_Lean_getAliasState(v___x_4076_);
v___x_4101_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4100_, v___f_4099_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
if (lean_obj_tag(v_a_4102_) == 0)
{
lean_object* v_a_4103_; 
lean_dec_ref(v___x_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_id_4073_);
v_a_4103_ = lean_ctor_get(v_a_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v_a_4102_, 1);
v_a_4089_ = v_a_4103_;
goto v___jp_4088_;
}
else
{
lean_object* v___x_4104_; 
lean_dec_ref_known(v_a_4102_, 1);
v___x_4104_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4075_, v___x_4076_, v_id_4073_, v_danglingDot_4074_, v_tail_4095_, v___x_4096_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
return v___x_4104_;
}
}
else
{
lean_dec_ref(v___x_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_id_4073_);
return v___x_4101_;
}
}
else
{
lean_object* v_id_4105_; lean_object* v_declName_4106_; uint8_t v___x_4107_; 
v_id_4105_ = lean_ctor_get(v_head_4094_, 0);
v_declName_4106_ = lean_ctor_get(v_head_4094_, 1);
lean_inc(v_declName_4106_);
lean_inc_ref(v___x_4076_);
v___x_4107_ = l_Lean_Server_Completion_allowCompletion(v_a_4075_, v___x_4076_, v_declName_4106_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; 
v___x_4108_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4075_, v___x_4076_, v_id_4073_, v_danglingDot_4074_, v_tail_4095_, v___x_4096_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
return v___x_4108_;
}
else
{
uint8_t v___x_4109_; 
v___x_4109_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(v_id_4073_, v_id_4105_, v_danglingDot_4074_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; 
v___x_4110_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4075_, v___x_4076_, v_id_4073_, v_danglingDot_4074_, v_tail_4095_, v___x_4096_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
return v___x_4110_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4111_ = l_Lean_Name_getString_x21(v_id_4105_);
v___x_4112_ = lean_box(0);
v___x_4113_ = l_Lean_Name_str___override(v___x_4112_, v___x_4111_);
lean_inc(v_declName_4106_);
v___x_4114_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___redArg(v___x_4113_, v_declName_4106_, v___y_4080_, v___y_4081_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v___x_4115_; 
lean_dec_ref_known(v___x_4114_, 1);
v___x_4115_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4075_, v___x_4076_, v_id_4073_, v_danglingDot_4074_, v_tail_4095_, v___x_4096_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
return v___x_4115_;
}
else
{
lean_dec_ref(v___x_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_id_4073_);
return v___x_4114_;
}
}
}
}
}
v___jp_4088_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v_a_4089_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
return v___x_4091_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg___boxed(lean_object* v_id_4116_, lean_object* v_danglingDot_4117_, lean_object* v_a_4118_, lean_object* v___x_4119_, lean_object* v_as_4120_, lean_object* v_as_x27_4121_, lean_object* v_b_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
uint8_t v_danglingDot_boxed_4131_; lean_object* v_res_4132_; 
v_danglingDot_boxed_4131_ = lean_unbox(v_danglingDot_4117_);
v_res_4132_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4116_, v_danglingDot_boxed_4131_, v_a_4118_, v___x_4119_, v_as_4120_, v_as_x27_4121_, v_b_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v_as_x27_4121_);
lean_dec(v_as_4120_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* v_ctx_4133_, lean_object* v_stx_4134_, lean_object* v_id_4135_, lean_object* v_hoverInfo_4136_, uint8_t v_danglingDot_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; uint8_t v___y_4157_; lean_object* v_id_4198_; uint8_t v_danglingDot_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v_id_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___x_4229_; 
v___x_4229_ = l_Lean_Name_hasMacroScopes(v_id_4135_);
if (v___x_4229_ == 0)
{
v_id_4218_ = v_id_4135_;
v___y_4219_ = v_a_4138_;
v___y_4220_ = v_a_4139_;
v___y_4221_ = v_a_4140_;
v___y_4222_ = v_a_4141_;
v___y_4223_ = v_a_4142_;
v___y_4224_ = v_a_4143_;
v___y_4225_ = v_a_4144_;
goto v___jp_4217_;
}
else
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lean_Syntax_getHeadInfo(v_stx_4134_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_id_4231_; 
lean_dec_ref_known(v___x_4230_, 4);
v_id_4231_ = l_Lean_Name_eraseMacroScopes(v_id_4135_);
lean_dec(v_id_4135_);
v_id_4218_ = v_id_4231_;
v___y_4219_ = v_a_4138_;
v___y_4220_ = v_a_4139_;
v___y_4221_ = v_a_4140_;
v___y_4222_ = v_a_4141_;
v___y_4223_ = v_a_4142_;
v___y_4224_ = v_a_4143_;
v___y_4225_ = v_a_4144_;
goto v___jp_4217_;
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec(v___x_4230_);
lean_dec(v_hoverInfo_4136_);
lean_dec(v_id_4135_);
lean_dec_ref(v_ctx_4133_);
v___x_4232_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
return v___x_4233_;
}
}
v___jp_4146_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_st_ref_get(v___y_4155_);
v___x_4159_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___y_4148_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
if (lean_obj_tag(v_a_4160_) == 0)
{
lean_dec_ref_known(v_a_4160_, 1);
lean_dec(v___x_4158_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4159_;
}
else
{
lean_object* v___x_4161_; lean_object* v_a_4162_; 
lean_dec_ref_known(v_a_4160_, 1);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_Server_CancellableT_checkCancelled___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__1___redArg(v___y_4147_);
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
if (lean_obj_tag(v_a_4162_) == 0)
{
lean_dec_ref_known(v_a_4162_, 1);
lean_dec(v___x_4158_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4161_;
}
else
{
lean_object* v_env_4163_; lean_object* v___x_4164_; 
lean_dec_ref_known(v_a_4162_, 1);
lean_dec_ref(v___x_4161_);
v_env_4163_ = lean_ctor_get(v___x_4158_, 0);
lean_inc_ref_n(v_env_4163_, 2);
lean_dec(v___x_4158_);
v___x_4164_ = l_Lean_Server_Completion_getEligibleHeaderDecls(v_env_4163_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_toCommandContextInfo_4165_; lean_object* v_a_4166_; lean_object* v_currNamespace_4167_; lean_object* v_openDecls_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_toCommandContextInfo_4165_ = lean_ctor_get(v_ctx_4133_, 0);
v_a_4166_ = lean_ctor_get(v___x_4164_, 0);
lean_inc_n(v_a_4166_, 2);
lean_dec_ref_known(v___x_4164_, 1);
v_currNamespace_4167_ = lean_ctor_get(v_toCommandContextInfo_4165_, 5);
v_openDecls_4168_ = lean_ctor_get(v_toCommandContextInfo_4165_, 6);
v___x_4169_ = lean_box(0);
lean_inc_ref(v_env_4163_);
lean_inc(v___y_4154_);
v___x_4170_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v___y_4154_, v___y_4157_, v_a_4166_, v_env_4163_, v_openDecls_4168_, v_openDecls_4168_, v___x_4169_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
if (lean_obj_tag(v_a_4171_) == 0)
{
lean_dec_ref_known(v_a_4171_, 1);
lean_dec(v_a_4166_);
lean_dec_ref(v_env_4163_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4170_;
}
else
{
lean_object* v___f_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec_ref_known(v_a_4171_, 1);
lean_dec_ref_known(v___x_4170_, 1);
lean_inc_ref_n(v_env_4163_, 2);
v___f_4172_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__2___boxed), 12, 2);
lean_closure_set(v___f_4172_, 0, v_a_4166_);
lean_closure_set(v___f_4172_, 1, v_env_4163_);
lean_inc(v_currNamespace_4167_);
v___f_4173_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__3___boxed), 13, 3);
lean_closure_set(v___f_4173_, 0, v___y_4156_);
lean_closure_set(v___f_4173_, 1, v___f_4172_);
lean_closure_set(v___f_4173_, 2, v_currNamespace_4167_);
v___x_4174_ = l_Lean_getAliasState(v_env_4163_);
v___x_4175_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v___x_4174_, v___f_4173_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
if (lean_obj_tag(v_a_4176_) == 0)
{
lean_dec_ref_known(v_a_4176_, 1);
lean_dec_ref(v_env_4163_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4175_;
}
else
{
lean_dec_ref_known(v_a_4176_, 1);
lean_dec_ref_known(v___x_4175_, 1);
if (v___y_4157_ == 0)
{
if (lean_obj_tag(v___y_4154_) == 1)
{
lean_object* v_pre_4177_; 
v_pre_4177_ = lean_ctor_get(v___y_4154_, 0);
if (lean_obj_tag(v_pre_4177_) == 0)
{
lean_object* v_str_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; size_t v_sz_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
v_str_4178_ = lean_ctor_get(v___y_4154_, 1);
v___x_4179_ = l_Lean_Parser_getTokenTable(v_env_4163_);
v___x_4180_ = l_Lean_Data_Trie_findPrefix___redArg(v___x_4179_, v_str_4178_);
lean_dec_ref(v___x_4179_);
v_sz_4181_ = lean_array_size(v___x_4180_);
v___x_4182_ = ((size_t)0ULL);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v___x_4180_, v_sz_4181_, v___x_4182_, v___x_4169_, v___y_4151_, v___y_4153_);
lean_dec_ref(v___x_4180_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
if (lean_obj_tag(v_a_4184_) == 0)
{
lean_dec_ref_known(v_a_4184_, 1);
lean_dec_ref_known(v___y_4154_, 2);
lean_dec_ref(v_ctx_4133_);
return v___x_4183_;
}
else
{
lean_object* v___x_4185_; 
lean_dec_ref_known(v_a_4184_, 1);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4133_, v___y_4154_, v___y_4157_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
return v___x_4185_;
}
}
else
{
lean_dec_ref_known(v___y_4154_, 2);
lean_dec_ref(v_ctx_4133_);
return v___x_4183_;
}
}
else
{
lean_object* v___x_4186_; 
lean_dec_ref(v_env_4163_);
v___x_4186_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4133_, v___y_4154_, v___y_4157_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
return v___x_4186_;
}
}
else
{
lean_object* v___x_4187_; 
lean_dec_ref(v_env_4163_);
v___x_4187_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4133_, v___y_4154_, v___y_4157_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
return v___x_4187_;
}
}
else
{
lean_object* v___x_4188_; 
lean_dec_ref(v_env_4163_);
v___x_4188_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_completeNamespaces(v_ctx_4133_, v___y_4154_, v___y_4157_, v___y_4151_, v___y_4153_, v___y_4147_, v___y_4150_, v___y_4152_, v___y_4149_, v___y_4155_);
return v___x_4188_;
}
}
}
else
{
lean_dec_ref(v_env_4163_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4175_;
}
}
}
else
{
lean_dec(v_a_4166_);
lean_dec_ref(v_env_4163_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4170_;
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v_env_4163_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
v_a_4189_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4164_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4164_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4158_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v_ctx_4133_);
return v___x_4159_;
}
}
v___jp_4197_:
{
lean_object* v___x_4207_; lean_object* v___f_4208_; lean_object* v___x_4209_; lean_object* v___f_4210_; uint8_t v___x_4211_; 
v___x_4207_ = lean_box(v_danglingDot_4199_);
lean_inc_n(v_id_4198_, 2);
lean_inc_ref(v_ctx_4133_);
v___f_4208_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4208_, 0, v_ctx_4133_);
lean_closure_set(v___f_4208_, 1, v_id_4198_);
lean_closure_set(v___f_4208_, 2, v___x_4207_);
v___x_4209_ = lean_box(v_danglingDot_4199_);
v___f_4210_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4210_, 0, v_id_4198_);
lean_closure_set(v___f_4210_, 1, v___x_4209_);
v___x_4211_ = l_Lean_Name_isAtomic(v_id_4198_);
if (v___x_4211_ == 0)
{
v___y_4147_ = v___y_4202_;
v___y_4148_ = v___f_4208_;
v___y_4149_ = v___y_4205_;
v___y_4150_ = v___y_4203_;
v___y_4151_ = v___y_4200_;
v___y_4152_ = v___y_4204_;
v___y_4153_ = v___y_4201_;
v___y_4154_ = v_id_4198_;
v___y_4155_ = v___y_4206_;
v___y_4156_ = v___f_4210_;
v___y_4157_ = v_danglingDot_4199_;
goto v___jp_4146_;
}
else
{
lean_object* v_lctx_4212_; lean_object* v_decls_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_lctx_4212_ = lean_ctor_get(v___y_4203_, 2);
v_decls_4213_ = lean_ctor_get(v_lctx_4212_, 1);
v___x_4214_ = lean_box(0);
v___x_4215_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6(v_id_4198_, v_danglingDot_4199_, v_decls_4213_, v___x_4214_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
if (lean_obj_tag(v_a_4216_) == 0)
{
lean_dec_ref_known(v_a_4216_, 1);
lean_dec_ref(v___f_4210_);
lean_dec_ref(v___f_4208_);
lean_dec(v_id_4198_);
lean_dec_ref(v_ctx_4133_);
return v___x_4215_;
}
else
{
lean_dec_ref_known(v_a_4216_, 1);
lean_dec_ref_known(v___x_4215_, 1);
v___y_4147_ = v___y_4202_;
v___y_4148_ = v___f_4208_;
v___y_4149_ = v___y_4205_;
v___y_4150_ = v___y_4203_;
v___y_4151_ = v___y_4200_;
v___y_4152_ = v___y_4204_;
v___y_4153_ = v___y_4201_;
v___y_4154_ = v_id_4198_;
v___y_4155_ = v___y_4206_;
v___y_4156_ = v___f_4210_;
v___y_4157_ = v_danglingDot_4199_;
goto v___jp_4146_;
}
}
else
{
lean_dec_ref(v___f_4210_);
lean_dec_ref(v___f_4208_);
lean_dec(v_id_4198_);
lean_dec_ref(v_ctx_4133_);
return v___x_4215_;
}
}
}
v___jp_4217_:
{
if (lean_obj_tag(v_hoverInfo_4136_) == 1)
{
lean_object* v_delta_4226_; lean_object* v_id_4227_; uint8_t v_danglingDot_4228_; 
v_delta_4226_ = lean_ctor_get(v_hoverInfo_4136_, 0);
lean_inc(v_delta_4226_);
lean_dec_ref_known(v_hoverInfo_4136_, 1);
v_id_4227_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(v_id_4218_, v_delta_4226_);
v_danglingDot_4228_ = 0;
v_id_4198_ = v_id_4227_;
v_danglingDot_4199_ = v_danglingDot_4228_;
v___y_4200_ = v___y_4219_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4223_;
v___y_4205_ = v___y_4224_;
v___y_4206_ = v___y_4225_;
goto v___jp_4197_;
}
else
{
lean_dec(v_hoverInfo_4136_);
v_id_4198_ = v_id_4218_;
v_danglingDot_4199_ = v_danglingDot_4137_;
v___y_4200_ = v___y_4219_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4223_;
v___y_4205_ = v___y_4224_;
v___y_4206_ = v___y_4225_;
goto v___jp_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* v_ctx_4234_, lean_object* v_stx_4235_, lean_object* v_id_4236_, lean_object* v_hoverInfo_4237_, lean_object* v_danglingDot_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
uint8_t v_danglingDot_boxed_4247_; lean_object* v_res_4248_; 
v_danglingDot_boxed_4247_ = lean_unbox(v_danglingDot_4238_);
v_res_4248_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(v_ctx_4234_, v_stx_4235_, v_id_4236_, v_hoverInfo_4237_, v_danglingDot_boxed_4247_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_stx_4235_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(lean_object* v_a_4249_, lean_object* v___x_4250_, lean_object* v_alias_4251_, lean_object* v_as_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___redArg(v_a_4249_, v___x_4250_, v_alias_4251_, v_as_4252_, v___y_4253_, v___y_4254_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2___boxed(lean_object* v_a_4262_, lean_object* v___x_4263_, lean_object* v_alias_4264_, lean_object* v_as_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_List_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__2(v_a_4262_, v___x_4263_, v_alias_4264_, v_as_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v_alias_4264_);
lean_dec_ref(v_a_4262_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(lean_object* v_00_u03b2_4275_, lean_object* v_s_4276_, lean_object* v_f_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___redArg(v_s_4276_, v_f_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3___boxed(lean_object* v_00_u03b2_4287_, lean_object* v_s_4288_, lean_object* v_f_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3(v_00_u03b2_4287_, v_s_4288_, v_f_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(lean_object* v_id_4299_, uint8_t v_danglingDot_4300_, lean_object* v_a_4301_, lean_object* v___x_4302_, lean_object* v_as_4303_, lean_object* v_as_x27_4304_, lean_object* v_b_4305_, lean_object* v_a_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___redArg(v_id_4299_, v_danglingDot_4300_, v_a_4301_, v___x_4302_, v_as_4303_, v_as_x27_4304_, v_b_4305_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4___boxed(lean_object* v_id_4316_, lean_object* v_danglingDot_4317_, lean_object* v_a_4318_, lean_object* v___x_4319_, lean_object* v_as_4320_, lean_object* v_as_x27_4321_, lean_object* v_b_4322_, lean_object* v_a_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
uint8_t v_danglingDot_boxed_4332_; lean_object* v_res_4333_; 
v_danglingDot_boxed_4332_ = lean_unbox(v_danglingDot_4317_);
v_res_4333_ = l_List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4(v_id_4316_, v_danglingDot_boxed_4332_, v_a_4318_, v___x_4319_, v_as_4320_, v_as_x27_4321_, v_b_4322_, v_a_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v_as_x27_4321_);
lean_dec(v_as_4320_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(lean_object* v_as_4334_, size_t v_sz_4335_, size_t v_i_4336_, lean_object* v_b_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___redArg(v_as_4334_, v_sz_4335_, v_i_4336_, v_b_4337_, v___y_4338_, v___y_4339_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5___boxed(lean_object* v_as_4347_, lean_object* v_sz_4348_, lean_object* v_i_4349_, lean_object* v_b_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
size_t v_sz_boxed_4359_; size_t v_i_boxed_4360_; lean_object* v_res_4361_; 
v_sz_boxed_4359_ = lean_unbox_usize(v_sz_4348_);
lean_dec(v_sz_4348_);
v_i_boxed_4360_ = lean_unbox_usize(v_i_4349_);
lean_dec(v_i_4349_);
v_res_4361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__5(v_as_4347_, v_sz_boxed_4359_, v_i_boxed_4360_, v_b_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec_ref(v_as_4347_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(lean_object* v_00_u03b2_4362_, lean_object* v_f_4363_, lean_object* v_x_4364_, lean_object* v_x_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___redArg(v_f_4363_, v_x_4364_, v_x_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4375_, lean_object* v_f_4376_, lean_object* v_x_4377_, lean_object* v_x_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__4(v_00_u03b2_4375_, v_f_4376_, v_x_4377_, v_x_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(lean_object* v_00_u03b2_4388_, lean_object* v_map_4389_, lean_object* v_f_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___redArg(v_map_4389_, v_f_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4400_, lean_object* v_map_4401_, lean_object* v_f_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5(v_00_u03b2_4400_, v_map_4401_, v_f_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(lean_object* v_00_u03b2_4412_, lean_object* v_f_4413_, lean_object* v_as_4414_, size_t v_i_4415_, size_t v_stop_4416_, lean_object* v_b_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___redArg(v_f_4413_, v_as_4414_, v_i_4415_, v_stop_4416_, v_b_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4427_, lean_object* v_f_4428_, lean_object* v_as_4429_, lean_object* v_i_4430_, lean_object* v_stop_4431_, lean_object* v_b_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_i_boxed_4441_; size_t v_stop_boxed_4442_; lean_object* v_res_4443_; 
v_i_boxed_4441_ = lean_unbox_usize(v_i_4430_);
lean_dec(v_i_4430_);
v_stop_boxed_4442_ = lean_unbox_usize(v_stop_4431_);
lean_dec(v_stop_4431_);
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__6(v_00_u03b2_4427_, v_f_4428_, v_as_4429_, v_i_boxed_4441_, v_stop_boxed_4442_, v_b_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec_ref(v_as_4429_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(lean_object* v_a_4444_, lean_object* v___x_4445_, lean_object* v_id_4446_, uint8_t v_danglingDot_4447_, lean_object* v_as_4448_, lean_object* v_as_x27_4449_, lean_object* v_b_4450_, lean_object* v_a_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___redArg(v_a_4444_, v___x_4445_, v_id_4446_, v_danglingDot_4447_, v_as_x27_4449_, v_b_4450_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8___boxed(lean_object* v_a_4461_, lean_object* v___x_4462_, lean_object* v_id_4463_, lean_object* v_danglingDot_4464_, lean_object* v_as_4465_, lean_object* v_as_x27_4466_, lean_object* v_b_4467_, lean_object* v_a_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v_danglingDot_boxed_4477_; lean_object* v_res_4478_; 
v_danglingDot_boxed_4477_ = lean_unbox(v_danglingDot_4464_);
v_res_4478_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__4_spec__8(v_a_4461_, v___x_4462_, v_id_4463_, v_danglingDot_boxed_4477_, v_as_4465_, v_as_x27_4466_, v_b_4467_, v_a_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v_as_x27_4466_);
lean_dec(v_as_4465_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4479_, lean_object* v_map_4480_, lean_object* v_f_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___redArg(v_map_4480_, v_f_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_4492_, lean_object* v_map_4493_, lean_object* v_f_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3(v_00_u03b2_4492_, v_map_4493_, v_f_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(lean_object* v_map_4505_, lean_object* v_f_4506_, lean_object* v_init_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4506_, v_map_4505_, v_init_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_map_4517_, lean_object* v_f_4518_, lean_object* v_init_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___redArg(v_map_4517_, v_f_4518_, v_init_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_4529_, lean_object* v_00_u03b2_4530_, lean_object* v_map_4531_, lean_object* v_f_4532_, lean_object* v_init_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4532_, v_map_4531_, v_init_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_4543_, lean_object* v_00_u03b2_4544_, lean_object* v_map_4545_, lean_object* v_f_4546_, lean_object* v_init_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9(v_00_u03c3_4543_, v_00_u03b2_4544_, v_map_4545_, v_f_4546_, v_init_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(lean_object* v_id_4557_, uint8_t v_danglingDot_4558_, lean_object* v_as_4559_, size_t v_sz_4560_, size_t v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___redArg(v_id_4557_, v_danglingDot_4558_, v_as_4559_, v_sz_4560_, v_i_4561_, v_b_4562_, v___y_4563_, v___y_4564_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19___boxed(lean_object* v_id_4572_, lean_object* v_danglingDot_4573_, lean_object* v_as_4574_, lean_object* v_sz_4575_, lean_object* v_i_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
uint8_t v_danglingDot_boxed_4586_; size_t v_sz_boxed_4587_; size_t v_i_boxed_4588_; lean_object* v_res_4589_; 
v_danglingDot_boxed_4586_ = lean_unbox(v_danglingDot_4573_);
v_sz_boxed_4587_ = lean_unbox_usize(v_sz_4575_);
lean_dec(v_sz_4575_);
v_i_boxed_4588_ = lean_unbox_usize(v_i_4576_);
lean_dec(v_i_4576_);
v_res_4589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__12_spec__19(v_id_4572_, v_danglingDot_boxed_4586_, v_as_4574_, v_sz_boxed_4587_, v_i_boxed_4588_, v_b_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v_as_4574_);
lean_dec(v_id_4572_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_map_4590_, lean_object* v_f_4591_, lean_object* v_init_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4591_, v_map_4590_, v_init_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_map_4603_, lean_object* v_f_4604_, lean_object* v_init_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___redArg(v_map_4603_, v_f_4604_, v_init_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03c3_4616_, lean_object* v_00_u03b2_4617_, lean_object* v_map_4618_, lean_object* v_f_4619_, lean_object* v_init_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v___x_4630_; 
v___x_4630_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4619_, v_map_4618_, v_init_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_00_u03c3_4631_, lean_object* v_00_u03b2_4632_, lean_object* v_map_4633_, lean_object* v_f_4634_, lean_object* v_init_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9(v_00_u03c3_4631_, v_00_u03b2_4632_, v_map_4633_, v_f_4634_, v_init_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(lean_object* v_00_u03c3_4646_, lean_object* v_00_u03b1_4647_, lean_object* v_00_u03b2_4648_, lean_object* v_f_4649_, lean_object* v_x_4650_, lean_object* v_x_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___redArg(v_f_4649_, v_x_4650_, v_x_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03c3_4661_, lean_object* v_00_u03b1_4662_, lean_object* v_00_u03b2_4663_, lean_object* v_f_4664_, lean_object* v_x_4665_, lean_object* v_x_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14(v_00_u03c3_4661_, v_00_u03b1_4662_, v_00_u03b2_4663_, v_f_4664_, v_x_4665_, v_x_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(lean_object* v_id_4676_, uint8_t v_danglingDot_4677_, lean_object* v_as_4678_, size_t v_sz_4679_, size_t v_i_4680_, lean_object* v_b_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___redArg(v_id_4676_, v_danglingDot_4677_, v_as_4678_, v_sz_4679_, v_i_4680_, v_b_4681_, v___y_4682_, v___y_4683_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20___boxed(lean_object* v_id_4691_, lean_object* v_danglingDot_4692_, lean_object* v_as_4693_, lean_object* v_sz_4694_, lean_object* v_i_4695_, lean_object* v_b_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
uint8_t v_danglingDot_boxed_4705_; size_t v_sz_boxed_4706_; size_t v_i_boxed_4707_; lean_object* v_res_4708_; 
v_danglingDot_boxed_4705_ = lean_unbox(v_danglingDot_4692_);
v_sz_boxed_4706_ = lean_unbox_usize(v_sz_4694_);
lean_dec(v_sz_4694_);
v_i_boxed_4707_ = lean_unbox_usize(v_i_4695_);
lean_dec(v_i_4695_);
v_res_4708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__6_spec__11_spec__17_spec__20(v_id_4691_, v_danglingDot_boxed_4705_, v_as_4693_, v_sz_boxed_4706_, v_i_boxed_4707_, v_b_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec_ref(v_as_4693_);
lean_dec(v_id_4691_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(lean_object* v_00_u03c3_4709_, lean_object* v_00_u03b1_4710_, lean_object* v_00_u03b2_4711_, lean_object* v_f_4712_, lean_object* v_x_4713_, lean_object* v_x_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___redArg(v_f_4712_, v_x_4713_, v_x_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16___boxed(lean_object* v_00_u03c3_4725_, lean_object* v_00_u03b1_4726_, lean_object* v_00_u03b2_4727_, lean_object* v_f_4728_, lean_object* v_x_4729_, lean_object* v_x_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16(v_00_u03c3_4725_, v_00_u03b1_4726_, v_00_u03b2_4727_, v_f_4728_, v_x_4729_, v_x_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(lean_object* v_00_u03b1_4741_, lean_object* v_00_u03b2_4742_, lean_object* v_00_u03c3_4743_, lean_object* v_f_4744_, lean_object* v_as_4745_, size_t v_i_4746_, size_t v_stop_4747_, lean_object* v_b_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___redArg(v_f_4744_, v_as_4745_, v_i_4746_, v_stop_4747_, v_b_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20___boxed(lean_object* v_00_u03b1_4758_, lean_object* v_00_u03b2_4759_, lean_object* v_00_u03c3_4760_, lean_object* v_f_4761_, lean_object* v_as_4762_, lean_object* v_i_4763_, lean_object* v_stop_4764_, lean_object* v_b_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
size_t v_i_boxed_4774_; size_t v_stop_boxed_4775_; lean_object* v_res_4776_; 
v_i_boxed_4774_ = lean_unbox_usize(v_i_4763_);
lean_dec(v_i_4763_);
v_stop_boxed_4775_ = lean_unbox_usize(v_stop_4764_);
lean_dec(v_stop_4764_);
v_res_4776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__20(v_00_u03b1_4758_, v_00_u03b2_4759_, v_00_u03c3_4760_, v_f_4761_, v_as_4762_, v_i_boxed_4774_, v_stop_boxed_4775_, v_b_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec_ref(v_as_4762_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(lean_object* v_00_u03c3_4777_, lean_object* v_00_u03b1_4778_, lean_object* v_00_u03b2_4779_, lean_object* v_f_4780_, lean_object* v_keys_4781_, lean_object* v_vals_4782_, lean_object* v_heq_4783_, lean_object* v_i_4784_, lean_object* v_acc_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___redArg(v_f_4780_, v_keys_4781_, v_vals_4782_, v_i_4784_, v_acc_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21___boxed(lean_object** _args){
lean_object* v_00_u03c3_4795_ = _args[0];
lean_object* v_00_u03b1_4796_ = _args[1];
lean_object* v_00_u03b2_4797_ = _args[2];
lean_object* v_f_4798_ = _args[3];
lean_object* v_keys_4799_ = _args[4];
lean_object* v_vals_4800_ = _args[5];
lean_object* v_heq_4801_ = _args[6];
lean_object* v_i_4802_ = _args[7];
lean_object* v_acc_4803_ = _args[8];
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
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__3_spec__5_spec__9_spec__14_spec__21(v_00_u03c3_4795_, v_00_u03b1_4796_, v_00_u03b2_4797_, v_f_4798_, v_keys_4799_, v_vals_4800_, v_heq_4801_, v_i_4802_, v_acc_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec_ref(v_vals_4800_);
lean_dec_ref(v_keys_4799_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(lean_object* v_00_u03b1_4813_, lean_object* v_00_u03b2_4814_, lean_object* v_00_u03c3_4815_, lean_object* v_f_4816_, lean_object* v_as_4817_, size_t v_i_4818_, size_t v_stop_4819_, lean_object* v_b_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___redArg(v_f_4816_, v_as_4817_, v_i_4818_, v_stop_4819_, v_b_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22___boxed(lean_object** _args){
lean_object* v_00_u03b1_4831_ = _args[0];
lean_object* v_00_u03b2_4832_ = _args[1];
lean_object* v_00_u03c3_4833_ = _args[2];
lean_object* v_f_4834_ = _args[3];
lean_object* v_as_4835_ = _args[4];
lean_object* v_i_4836_ = _args[5];
lean_object* v_stop_4837_ = _args[6];
lean_object* v_b_4838_ = _args[7];
lean_object* v___y_4839_ = _args[8];
lean_object* v___y_4840_ = _args[9];
lean_object* v___y_4841_ = _args[10];
lean_object* v___y_4842_ = _args[11];
lean_object* v___y_4843_ = _args[12];
lean_object* v___y_4844_ = _args[13];
lean_object* v___y_4845_ = _args[14];
lean_object* v___y_4846_ = _args[15];
lean_object* v___y_4847_ = _args[16];
_start:
{
size_t v_i_boxed_4848_; size_t v_stop_boxed_4849_; lean_object* v_res_4850_; 
v_i_boxed_4848_ = lean_unbox_usize(v_i_4836_);
lean_dec(v_i_4836_);
v_stop_boxed_4849_ = lean_unbox_usize(v_stop_4837_);
lean_dec(v_stop_4837_);
v_res_4850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__22(v_00_u03b1_4831_, v_00_u03b2_4832_, v_00_u03c3_4833_, v_f_4834_, v_as_4835_, v_i_boxed_4848_, v_stop_boxed_4849_, v_b_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec_ref(v_as_4835_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(lean_object* v_00_u03c3_4851_, lean_object* v_00_u03b1_4852_, lean_object* v_00_u03b2_4853_, lean_object* v_f_4854_, lean_object* v_keys_4855_, lean_object* v_vals_4856_, lean_object* v_heq_4857_, lean_object* v_i_4858_, lean_object* v_acc_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___redArg(v_f_4854_, v_keys_4855_, v_vals_4856_, v_i_4858_, v_acc_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_00_u03c3_4870_ = _args[0];
lean_object* v_00_u03b1_4871_ = _args[1];
lean_object* v_00_u03b2_4872_ = _args[2];
lean_object* v_f_4873_ = _args[3];
lean_object* v_keys_4874_ = _args[4];
lean_object* v_vals_4875_ = _args[5];
lean_object* v_heq_4876_ = _args[6];
lean_object* v_i_4877_ = _args[7];
lean_object* v_acc_4878_ = _args[8];
lean_object* v___y_4879_ = _args[9];
lean_object* v___y_4880_ = _args[10];
lean_object* v___y_4881_ = _args[11];
lean_object* v___y_4882_ = _args[12];
lean_object* v___y_4883_ = _args[13];
lean_object* v___y_4884_ = _args[14];
lean_object* v___y_4885_ = _args[15];
lean_object* v___y_4886_ = _args[16];
lean_object* v___y_4887_ = _args[17];
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_Completion_forEligibleDeclsM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0_spec__0_spec__3_spec__9_spec__16_spec__23(v_00_u03c3_4870_, v_00_u03b1_4871_, v_00_u03b2_4872_, v_f_4873_, v_keys_4874_, v_vals_4875_, v_heq_4876_, v_i_4877_, v_acc_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec_ref(v___y_4882_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
lean_dec_ref(v_vals_4875_);
lean_dec_ref(v_keys_4874_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* v_uri_4889_, lean_object* v_pos_4890_, lean_object* v_completionInfoPos_4891_, lean_object* v_ctx_4892_, lean_object* v_lctx_4893_, lean_object* v_stx_4894_, lean_object* v_id_4895_, lean_object* v_hoverInfo_4896_, uint8_t v_danglingDot_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4900_ = lean_box(v_danglingDot_4897_);
lean_inc_ref(v_ctx_4892_);
v___x_4901_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 13, 5);
lean_closure_set(v___x_4901_, 0, v_ctx_4892_);
lean_closure_set(v___x_4901_, 1, v_stx_4894_);
lean_closure_set(v___x_4901_, 2, v_id_4895_);
lean_closure_set(v___x_4901_, 3, v_hoverInfo_4896_);
lean_closure_set(v___x_4901_, 4, v___x_4900_);
v___x_4902_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_4889_, v_pos_4890_, v_completionInfoPos_4891_, v_ctx_4892_, v_lctx_4893_, v___x_4901_, v_a_4898_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* v_uri_4903_, lean_object* v_pos_4904_, lean_object* v_completionInfoPos_4905_, lean_object* v_ctx_4906_, lean_object* v_lctx_4907_, lean_object* v_stx_4908_, lean_object* v_id_4909_, lean_object* v_hoverInfo_4910_, lean_object* v_danglingDot_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
uint8_t v_danglingDot_boxed_4914_; lean_object* v_res_4915_; 
v_danglingDot_boxed_4914_ = lean_unbox(v_danglingDot_4911_);
v_res_4915_ = l_Lean_Server_Completion_idCompletion(v_uri_4903_, v_pos_4904_, v_completionInfoPos_4905_, v_ctx_4906_, v_lctx_4907_, v_stx_4908_, v_id_4909_, v_hoverInfo_4910_, v_danglingDot_boxed_4914_, v_a_4912_);
lean_dec_ref(v_a_4912_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(lean_object* v_e_4916_, lean_object* v___y_4917_){
_start:
{
uint8_t v___x_4919_; 
v___x_4919_ = l_Lean_Expr_hasMVar(v_e_4916_);
if (v___x_4919_ == 0)
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4920_, 0, v_e_4916_);
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
return v___x_4921_;
}
else
{
lean_object* v___x_4922_; lean_object* v_mctx_4923_; lean_object* v___x_4924_; lean_object* v_fst_4925_; lean_object* v_snd_4926_; lean_object* v___x_4927_; lean_object* v_cache_4928_; lean_object* v_zetaDeltaFVarIds_4929_; lean_object* v_postponed_4930_; lean_object* v_diag_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4941_; 
v___x_4922_ = lean_st_ref_get(v___y_4917_);
v_mctx_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc_ref(v_mctx_4923_);
lean_dec(v___x_4922_);
v___x_4924_ = l_Lean_instantiateMVarsCore(v_mctx_4923_, v_e_4916_);
v_fst_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc(v_fst_4925_);
v_snd_4926_ = lean_ctor_get(v___x_4924_, 1);
lean_inc(v_snd_4926_);
lean_dec_ref(v___x_4924_);
v___x_4927_ = lean_st_ref_take(v___y_4917_);
v_cache_4928_ = lean_ctor_get(v___x_4927_, 1);
v_zetaDeltaFVarIds_4929_ = lean_ctor_get(v___x_4927_, 2);
v_postponed_4930_ = lean_ctor_get(v___x_4927_, 3);
v_diag_4931_ = lean_ctor_get(v___x_4927_, 4);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4941_ == 0)
{
lean_object* v_unused_4942_; 
v_unused_4942_ = lean_ctor_get(v___x_4927_, 0);
lean_dec(v_unused_4942_);
v___x_4933_ = v___x_4927_;
v_isShared_4934_ = v_isSharedCheck_4941_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_diag_4931_);
lean_inc(v_postponed_4930_);
lean_inc(v_zetaDeltaFVarIds_4929_);
lean_inc(v_cache_4928_);
lean_dec(v___x_4927_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4941_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4936_; 
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 0, v_snd_4926_);
v___x_4936_ = v___x_4933_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_snd_4926_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_cache_4928_);
lean_ctor_set(v_reuseFailAlloc_4940_, 2, v_zetaDeltaFVarIds_4929_);
lean_ctor_set(v_reuseFailAlloc_4940_, 3, v_postponed_4930_);
lean_ctor_set(v_reuseFailAlloc_4940_, 4, v_diag_4931_);
v___x_4936_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4937_ = lean_st_ref_put(v___y_4917_, v___x_4936_);
v___x_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4938_, 0, v_fst_4925_);
v___x_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4938_);
return v___x_4939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg___boxed(lean_object* v_e_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4943_, v___y_4944_);
lean_dec(v___y_4944_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(lean_object* v_e_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_e_4947_, v___y_4952_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___boxed(lean_object* v_e_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0(v_e_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0(lean_object* v_a_4967_, lean_object* v_declName_4968_, lean_object* v_decl_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_unnormedTypeName_4978_; uint8_t v___x_4979_; 
v_unnormedTypeName_4978_ = l_Lean_Name_getPrefix(v_declName_4968_);
v___x_4979_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v_unnormedTypeName_4978_, v_a_4967_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
lean_dec_ref(v_decl_4969_);
lean_dec(v_declName_4968_);
v___x_4980_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5048_; 
v___x_4982_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_4968_, v___y_4976_);
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_5048_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5048_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
if (lean_obj_tag(v_a_4983_) == 1)
{
lean_object* v_val_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5043_; 
lean_del_object(v___x_4985_);
v_val_4987_ = lean_ctor_get(v_a_4983_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_a_4983_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_4989_ = v_a_4983_;
v_isShared_4990_ = v_isSharedCheck_5043_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_val_4987_);
lean_dec(v_a_4983_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5043_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v_info_4991_; lean_object* v_kind_4992_; lean_object* v_tags_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v_info_4991_ = lean_ctor_get(v_decl_4969_, 0);
lean_inc_ref(v_info_4991_);
v_kind_4992_ = lean_ctor_get(v_decl_4969_, 1);
lean_inc_ref(v_kind_4992_);
v_tags_4993_ = lean_ctor_get(v_decl_4969_, 2);
lean_inc_ref(v_tags_4993_);
lean_dec_ref(v_decl_4969_);
v___x_4994_ = l_Lean_Name_getPrefix(v_val_4987_);
lean_dec(v_val_4987_);
v___x_4995_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(v___x_4994_, v_info_4991_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5034_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5034_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5034_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
uint8_t v___x_5000_; 
v___x_5000_ = lean_unbox(v_a_4996_);
lean_dec(v_a_4996_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; lean_object* v___x_5003_; 
lean_dec_ref(v_tags_4993_);
lean_dec_ref(v_kind_4992_);
lean_dec_ref(v_info_4991_);
lean_del_object(v___x_4989_);
v___x_5001_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 0, v___x_5001_);
v___x_5003_ = v___x_4998_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
else
{
lean_object* v___x_5005_; 
lean_del_object(v___x_4998_);
lean_inc(v___y_4976_);
lean_inc_ref(v___y_4975_);
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
v___x_5005_ = lean_apply_5(v_kind_4992_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, lean_box(0));
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref_known(v___x_5005_, 1);
lean_inc(v___y_4976_);
lean_inc_ref(v___y_4975_);
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
v___x_5007_ = lean_apply_5(v_tags_4993_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, lean_box(0));
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v_a_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
lean_inc(v_a_5008_);
lean_dec_ref_known(v___x_5007_, 1);
v___x_5009_ = l_Lean_ConstantInfo_name(v_info_4991_);
lean_dec_ref(v_info_4991_);
v___x_5010_ = l_Lean_Name_getString_x21(v___x_5009_);
v___x_5011_ = lean_box(0);
v___x_5012_ = l_Lean_Name_str___override(v___x_5011_, v___x_5010_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set_tag(v___x_4989_, 0);
lean_ctor_set(v___x_4989_, 0, v___x_5009_);
v___x_5014_ = v___x_4989_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5009_);
v___x_5014_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
uint8_t v___x_5015_; lean_object* v___x_5016_; 
v___x_5015_ = lean_unbox(v_a_5006_);
lean_dec(v_a_5006_);
v___x_5016_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5012_, v___x_5014_, v___x_5015_, v_a_5008_, v___y_4970_, v___y_4971_);
return v___x_5016_;
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec(v_a_5006_);
lean_dec_ref(v_info_4991_);
lean_del_object(v___x_4989_);
v_a_5018_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5007_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5007_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
lean_dec_ref(v_tags_4993_);
lean_dec_ref(v_info_4991_);
lean_del_object(v___x_4989_);
v_a_5026_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_5005_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5005_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
}
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
lean_dec_ref(v_tags_4993_);
lean_dec_ref(v_kind_4992_);
lean_dec_ref(v_info_4991_);
lean_del_object(v___x_4989_);
v_a_5035_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_4995_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_4995_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
}
else
{
lean_object* v___x_5044_; lean_object* v___x_5046_; 
lean_dec(v_a_4983_);
lean_dec_ref(v_decl_4969_);
v___x_5044_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_5044_);
v___x_5046_ = v___x_4985_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__0___boxed(lean_object* v_a_5049_, lean_object* v_declName_5050_, lean_object* v_decl_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Lean_Server_Completion_dotCompletion___lam__0(v_a_5049_, v_declName_5050_, v_decl_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1(lean_object* v_expr_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_){
_start:
{
lean_object* v_a_5074_; lean_object* v___y_5078_; uint8_t v___y_5079_; lean_object* v___y_5089_; lean_object* v_a_5090_; lean_object* v___x_5093_; 
lean_inc(v___y_5068_);
lean_inc_ref(v___y_5067_);
lean_inc(v___y_5066_);
lean_inc_ref(v___y_5065_);
v___x_5093_ = lean_infer_type(v_expr_5061_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5095_; lean_object* v_a_5096_; lean_object* v_a_5097_; lean_object* v___x_5098_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___x_5093_, 1);
v___x_5095_ = l_Lean_instantiateMVars___at___00Lean_Server_Completion_dotCompletion_spec__0___redArg(v_a_5094_, v___y_5066_);
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_a_5096_);
lean_dec_ref(v___x_5095_);
v_a_5097_ = lean_ctor_get(v_a_5096_, 0);
lean_inc(v_a_5097_);
lean_dec(v_a_5096_);
v___x_5098_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet(v_a_5097_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v_a_5074_ = v_a_5099_;
goto v___jp_5073_;
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
v_a_5100_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5098_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5098_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
lean_inc(v_a_5100_);
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
v___y_5089_ = v___x_5105_;
v_a_5090_ = v_a_5100_;
goto v___jp_5088_;
}
}
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
v_a_5108_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_5093_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5093_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
lean_inc(v_a_5108_);
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
v___y_5089_ = v___x_5113_;
v_a_5090_ = v_a_5108_;
goto v___jp_5088_;
}
}
}
v___jp_5070_:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
return v___x_5072_;
}
v___jp_5073_:
{
if (lean_obj_tag(v_a_5074_) == 0)
{
lean_object* v___f_5075_; lean_object* v___x_5076_; 
v___f_5075_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5075_, 0, v_a_5074_);
v___x_5076_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5075_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
return v___x_5076_;
}
else
{
goto v___jp_5070_;
}
}
v___jp_5077_:
{
if (v___y_5079_ == 0)
{
lean_dec_ref(v___y_5078_);
goto v___jp_5070_;
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
v_a_5080_ = lean_ctor_get(v___y_5078_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___y_5078_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___y_5078_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___y_5078_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
v___jp_5088_:
{
uint8_t v___x_5091_; 
v___x_5091_ = l_Lean_Exception_isInterrupt(v_a_5090_);
if (v___x_5091_ == 0)
{
uint8_t v___x_5092_; 
v___x_5092_ = l_Lean_Exception_isRuntime(v_a_5090_);
v___y_5078_ = v___y_5089_;
v___y_5079_ = v___x_5092_;
goto v___jp_5077_;
}
else
{
lean_dec_ref(v_a_5090_);
v___y_5078_ = v___y_5089_;
v___y_5079_ = v___x_5091_;
goto v___jp_5077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lam__1___boxed(lean_object* v_expr_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_Server_Completion_dotCompletion___lam__1(v_expr_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* v_uri_5126_, lean_object* v_pos_5127_, lean_object* v_completionInfoPos_5128_, lean_object* v_ctx_5129_, lean_object* v_info_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v_lctx_5133_; lean_object* v_expr_5134_; lean_object* v___f_5135_; lean_object* v___x_5136_; 
v_lctx_5133_ = lean_ctor_get(v_info_5130_, 1);
lean_inc_ref(v_lctx_5133_);
v_expr_5134_ = lean_ctor_get(v_info_5130_, 3);
lean_inc_ref(v_expr_5134_);
lean_dec_ref(v_info_5130_);
v___f_5135_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lam__1___boxed), 9, 1);
lean_closure_set(v___f_5135_, 0, v_expr_5134_);
v___x_5136_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5126_, v_pos_5127_, v_completionInfoPos_5128_, v_ctx_5129_, v_lctx_5133_, v___f_5135_, v_a_5131_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___boxed(lean_object* v_uri_5137_, lean_object* v_pos_5138_, lean_object* v_completionInfoPos_5139_, lean_object* v_ctx_5140_, lean_object* v_info_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Lean_Server_Completion_dotCompletion(v_uri_5137_, v_pos_5138_, v_completionInfoPos_5139_, v_ctx_5140_, v_info_5141_, v_a_5142_);
lean_dec_ref(v_a_5142_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0(lean_object* v___x_5145_, lean_object* v_id_5146_, lean_object* v_declName_5147_, lean_object* v_decl_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_){
_start:
{
lean_object* v___x_5157_; uint8_t v___x_5158_; 
v___x_5157_ = l_Lean_Name_getPrefix(v_declName_5147_);
lean_inc(v___x_5145_);
v___x_5158_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNameSet_spec__0___redArg(v___x_5157_, v___x_5145_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; lean_object* v___x_5160_; 
lean_dec_ref(v_decl_5148_);
lean_dec(v_declName_5147_);
lean_dec(v___x_5145_);
v___x_5159_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5160_, 0, v___x_5159_);
return v___x_5160_;
}
else
{
lean_object* v___x_5161_; lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5258_; 
v___x_5161_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___redArg(v_declName_5147_, v___y_5155_);
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5164_ = v___x_5161_;
v_isShared_5165_ = v_isSharedCheck_5258_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5161_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5258_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
if (lean_obj_tag(v_a_5162_) == 1)
{
lean_object* v_val_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5253_; 
lean_del_object(v___x_5164_);
v_val_5166_ = lean_ctor_get(v_a_5162_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_a_5162_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5168_ = v_a_5162_;
v_isShared_5169_ = v_isSharedCheck_5253_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_val_5166_);
lean_dec(v_a_5162_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5253_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v_info_5170_; lean_object* v_kind_5171_; lean_object* v_tags_5172_; lean_object* v___x_5173_; 
v_info_5170_ = lean_ctor_get(v_decl_5148_, 0);
lean_inc_ref(v_info_5170_);
v_kind_5171_ = lean_ctor_get(v_decl_5148_, 1);
lean_inc_ref(v_kind_5171_);
v_tags_5172_ = lean_ctor_get(v_decl_5148_, 2);
lean_inc_ref(v_tags_5172_);
lean_dec_ref(v_decl_5148_);
v___x_5173_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(v___x_5145_, v_info_5170_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5244_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5176_ = v___x_5173_;
v_isShared_5177_ = v_isSharedCheck_5244_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5173_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5244_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
uint8_t v___x_5178_; 
v___x_5178_ = lean_unbox(v_a_5174_);
lean_dec(v_a_5174_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5179_; lean_object* v___x_5181_; 
lean_dec_ref(v_tags_5172_);
lean_dec_ref(v_kind_5171_);
lean_dec_ref(v_info_5170_);
lean_del_object(v___x_5168_);
lean_dec(v_val_5166_);
v___x_5179_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5177_ == 0)
{
lean_ctor_set(v___x_5176_, 0, v___x_5179_);
v___x_5181_ = v___x_5176_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5179_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
else
{
lean_object* v___x_5183_; 
lean_del_object(v___x_5176_);
lean_inc(v___y_5155_);
lean_inc_ref(v___y_5154_);
lean_inc(v___y_5153_);
lean_inc_ref(v___y_5152_);
v___x_5183_ = lean_apply_5(v_kind_5171_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, lean_box(0));
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; lean_object* v___x_5185_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc(v_a_5184_);
lean_dec_ref_known(v___x_5183_, 1);
lean_inc(v___y_5155_);
lean_inc_ref(v___y_5154_);
lean_inc(v___y_5153_);
lean_inc_ref(v___y_5152_);
v___x_5185_ = lean_apply_5(v_tags_5172_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, lean_box(0));
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; uint8_t v___x_5187_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5186_);
lean_dec_ref_known(v___x_5185_, 1);
v___x_5187_ = l_Lean_Name_isAnonymous(v_id_5146_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5209_; 
lean_del_object(v___x_5168_);
v___x_5188_ = l_Lean_Name_getPrefix(v_val_5166_);
v___x_5189_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___redArg(v___x_5188_, v_id_5146_, v___x_5187_, v_val_5166_, v___y_5155_);
lean_dec(v___x_5188_);
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5192_ = v___x_5189_;
v_isShared_5193_ = v_isSharedCheck_5209_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5189_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5209_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
if (lean_obj_tag(v_a_5190_) == 1)
{
lean_object* v_val_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5204_; 
lean_del_object(v___x_5192_);
v_val_5194_ = lean_ctor_get(v_a_5190_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v_a_5190_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5196_ = v_a_5190_;
v_isShared_5197_ = v_isSharedCheck_5204_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_val_5194_);
lean_dec(v_a_5190_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5204_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5198_; lean_object* v___x_5200_; 
v___x_5198_ = l_Lean_ConstantInfo_name(v_info_5170_);
lean_dec_ref(v_info_5170_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set_tag(v___x_5196_, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5198_);
v___x_5200_ = v___x_5196_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5198_);
v___x_5200_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
uint8_t v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = lean_unbox(v_a_5184_);
lean_dec(v_a_5184_);
v___x_5202_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v_val_5194_, v___x_5200_, v___x_5201_, v_a_5186_, v___y_5149_, v___y_5150_);
return v___x_5202_;
}
}
}
else
{
lean_object* v___x_5205_; lean_object* v___x_5207_; 
lean_dec(v_a_5190_);
lean_dec(v_a_5186_);
lean_dec(v_a_5184_);
lean_dec_ref(v_info_5170_);
v___x_5205_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5193_ == 0)
{
lean_ctor_set(v___x_5192_, 0, v___x_5205_);
v___x_5207_ = v___x_5192_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5205_);
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
else
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5215_; 
lean_dec(v_val_5166_);
v___x_5210_ = l_Lean_ConstantInfo_name(v_info_5170_);
lean_dec_ref(v_info_5170_);
v___x_5211_ = l_Lean_Name_getString_x21(v___x_5210_);
v___x_5212_ = lean_box(0);
v___x_5213_ = l_Lean_Name_str___override(v___x_5212_, v___x_5211_);
if (v_isShared_5169_ == 0)
{
lean_ctor_set_tag(v___x_5168_, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5210_);
v___x_5215_ = v___x_5168_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5210_);
v___x_5215_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
uint8_t v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5225_; 
v___x_5216_ = lean_unbox(v_a_5184_);
lean_dec(v_a_5184_);
v___x_5217_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___redArg(v___x_5213_, v___x_5215_, v___x_5216_, v_a_5186_, v___y_5149_, v___y_5150_);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5225_ == 0)
{
lean_object* v_unused_5226_; 
v_unused_5226_ = lean_ctor_get(v___x_5217_, 0);
lean_dec(v_unused_5226_);
v___x_5219_ = v___x_5217_;
v_isShared_5220_ = v_isSharedCheck_5225_;
goto v_resetjp_5218_;
}
else
{
lean_dec(v___x_5217_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5225_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5221_; lean_object* v___x_5223_; 
v___x_5221_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5220_ == 0)
{
lean_ctor_set(v___x_5219_, 0, v___x_5221_);
v___x_5223_ = v___x_5219_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5221_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_dec(v_a_5184_);
lean_dec_ref(v_info_5170_);
lean_del_object(v___x_5168_);
lean_dec(v_val_5166_);
v_a_5228_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5185_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5185_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec_ref(v_tags_5172_);
lean_dec_ref(v_info_5170_);
lean_del_object(v___x_5168_);
lean_dec(v_val_5166_);
v_a_5236_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5183_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5183_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_dec_ref(v_tags_5172_);
lean_dec_ref(v_kind_5171_);
lean_dec_ref(v_info_5170_);
lean_del_object(v___x_5168_);
lean_dec(v_val_5166_);
v_a_5245_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5173_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5173_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
}
else
{
lean_object* v___x_5254_; lean_object* v___x_5256_; 
lean_dec(v_a_5162_);
lean_dec_ref(v_decl_5148_);
lean_dec(v___x_5145_);
v___x_5254_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 0, v___x_5254_);
v___x_5256_ = v___x_5164_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v___x_5254_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed(lean_object* v___x_5259_, lean_object* v_id_5260_, lean_object* v_declName_5261_, lean_object* v_decl_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_Server_Completion_dotIdCompletion___lam__0(v___x_5259_, v_id_5260_, v_declName_5261_, v_decl_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v___y_5264_);
lean_dec_ref(v___y_5263_);
lean_dec(v_id_5260_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1(lean_object* v_expectedType_x3f_5272_, lean_object* v_id_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_5272_) == 1)
{
lean_object* v_val_5282_; lean_object* v___x_5283_; 
v_val_5282_ = lean_ctor_get(v_expectedType_x3f_5272_, 0);
lean_inc(v_val_5282_);
lean_dec_ref_known(v_expectedType_x3f_5272_, 1);
v___x_5283_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(v_val_5282_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5298_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5286_ = v___x_5283_;
v_isShared_5287_ = v_isSharedCheck_5298_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5298_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
v___x_5288_ = lean_array_get_size(v_a_5284_);
v___x_5289_ = lean_unsigned_to_nat(0u);
v___x_5290_ = lean_nat_dec_eq(v___x_5288_, v___x_5289_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; lean_object* v___f_5292_; lean_object* v___x_5293_; 
lean_del_object(v___x_5286_);
v___x_5291_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_NameSetModPrivate_ofArray(v_a_5284_);
lean_dec(v_a_5284_);
v___f_5292_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__0___boxed), 12, 2);
lean_closure_set(v___f_5292_, 0, v___x_5291_);
lean_closure_set(v___f_5292_, 1, v_id_5273_);
v___x_5293_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_forEligibleDeclsWithCancellationM___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_spec__0(v___f_5292_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
return v___x_5293_;
}
else
{
lean_object* v___x_5294_; lean_object* v___x_5296_; 
lean_dec(v_a_5284_);
lean_dec(v_id_5273_);
v___x_5294_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___x_5294_);
v___x_5296_ = v___x_5286_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5294_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
lean_dec(v_id_5273_);
v_a_5299_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5283_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5283_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
}
}
else
{
lean_object* v___x_5307_; lean_object* v___x_5308_; 
lean_dec(v_id_5273_);
lean_dec(v_expectedType_x3f_5272_);
v___x_5307_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
return v___x_5308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed(lean_object* v_expectedType_x3f_5309_, lean_object* v_id_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Lean_Server_Completion_dotIdCompletion___lam__1(v_expectedType_x3f_5309_, v_id_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec_ref(v___y_5313_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* v_uri_5320_, lean_object* v_pos_5321_, lean_object* v_completionInfoPos_5322_, lean_object* v_ctx_5323_, lean_object* v_lctx_5324_, lean_object* v_id_5325_, lean_object* v_expectedType_x3f_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v___y_5329_; lean_object* v___x_5330_; 
v___y_5329_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lam__1___boxed), 10, 2);
lean_closure_set(v___y_5329_, 0, v_expectedType_x3f_5326_);
lean_closure_set(v___y_5329_, 1, v_id_5325_);
v___x_5330_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5320_, v_pos_5321_, v_completionInfoPos_5322_, v_ctx_5323_, v_lctx_5324_, v___y_5329_, v_a_5327_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___boxed(lean_object* v_uri_5331_, lean_object* v_pos_5332_, lean_object* v_completionInfoPos_5333_, lean_object* v_ctx_5334_, lean_object* v_lctx_5335_, lean_object* v_id_5336_, lean_object* v_expectedType_x3f_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_5331_, v_pos_5332_, v_completionInfoPos_5333_, v_ctx_5334_, v_lctx_5335_, v_id_5336_, v_expectedType_x3f_5337_, v_a_5338_);
lean_dec_ref(v_a_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(lean_object* v___y_5347_, lean_object* v_as_5348_, size_t v_sz_5349_, size_t v_i_5350_, lean_object* v_b_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v_a_5356_; uint8_t v___x_5360_; 
v___x_5360_ = lean_usize_dec_lt(v_i_5350_, v_sz_5349_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5361_, 0, v_b_5351_);
v___x_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5362_, 0, v___x_5361_);
return v___x_5362_;
}
else
{
lean_object* v___x_5363_; lean_object* v_a_5364_; 
v___x_5363_ = lean_box(0);
v_a_5364_ = lean_array_uget_borrowed(v_as_5348_, v_i_5350_);
if (lean_obj_tag(v_a_5364_) == 1)
{
lean_object* v_str_5365_; uint8_t v___x_5366_; 
v_str_5365_ = lean_ctor_get(v_a_5364_, 1);
v___x_5366_ = l_Lean_String_charactersIn(v___y_5347_, v_str_5365_);
if (v___x_5366_ == 0)
{
v_a_5356_ = v___x_5363_;
goto v___jp_5355_;
}
else
{
lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; 
v___x_5367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__1));
v___x_5368_ = lean_box(0);
v___x_5369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___closed__2));
lean_inc_ref(v_str_5365_);
v___x_5370_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5370_, 0, v_str_5365_);
lean_ctor_set(v___x_5370_, 1, v___x_5367_);
lean_ctor_set(v___x_5370_, 2, v___x_5368_);
lean_ctor_set(v___x_5370_, 3, v___x_5369_);
lean_ctor_set(v___x_5370_, 4, v___x_5368_);
lean_ctor_set(v___x_5370_, 5, v___x_5368_);
lean_ctor_set(v___x_5370_, 6, v___x_5368_);
lean_ctor_set(v___x_5370_, 7, v___x_5368_);
v___x_5371_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg(v___x_5370_, v___x_5368_, v___y_5352_, v___y_5353_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
lean_inc(v_a_5372_);
if (lean_obj_tag(v_a_5372_) == 0)
{
lean_dec_ref_known(v_a_5372_, 1);
return v___x_5371_;
}
else
{
lean_dec_ref_known(v_a_5372_, 1);
lean_dec_ref_known(v___x_5371_, 1);
v_a_5356_ = v___x_5363_;
goto v___jp_5355_;
}
}
else
{
return v___x_5371_;
}
}
}
else
{
v_a_5356_ = v___x_5363_;
goto v___jp_5355_;
}
}
v___jp_5355_:
{
size_t v___x_5357_; size_t v___x_5358_; 
v___x_5357_ = ((size_t)1ULL);
v___x_5358_ = lean_usize_add(v_i_5350_, v___x_5357_);
v_i_5350_ = v___x_5358_;
v_b_5351_ = v_a_5356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg___boxed(lean_object* v___y_5373_, lean_object* v_as_5374_, lean_object* v_sz_5375_, lean_object* v_i_5376_, lean_object* v_b_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
size_t v_sz_boxed_5381_; size_t v_i_boxed_5382_; lean_object* v_res_5383_; 
v_sz_boxed_5381_ = lean_unbox_usize(v_sz_5375_);
lean_dec(v_sz_5375_);
v_i_boxed_5382_ = lean_unbox_usize(v_i_5376_);
lean_dec(v_i_5376_);
v_res_5383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5373_, v_as_5374_, v_sz_boxed_5381_, v_i_boxed_5382_, v_b_5377_, v___y_5378_, v___y_5379_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec_ref(v_as_5374_);
lean_dec_ref(v___y_5373_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0(lean_object* v_structName_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_){
_start:
{
lean_object* v___x_5394_; lean_object* v_env_5395_; uint8_t v___x_5396_; lean_object* v_fieldNames_5397_; lean_object* v___x_5398_; size_t v_sz_5399_; size_t v___x_5400_; lean_object* v___x_5401_; 
v___x_5394_ = lean_st_ref_get(v___y_5392_);
v_env_5395_ = lean_ctor_get(v___x_5394_, 0);
lean_inc_ref(v_env_5395_);
lean_dec(v___x_5394_);
v___x_5396_ = 0;
v_fieldNames_5397_ = l_Lean_getStructureFieldsFlattened(v_env_5395_, v_structName_5384_, v___x_5396_);
v___x_5398_ = lean_box(0);
v_sz_5399_ = lean_array_size(v_fieldNames_5397_);
v___x_5400_ = ((size_t)0ULL);
v___x_5401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5385_, v_fieldNames_5397_, v_sz_5399_, v___x_5400_, v___x_5398_, v___y_5386_, v___y_5387_);
lean_dec_ref(v_fieldNames_5397_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v_a_5402_; 
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_a_5402_);
if (lean_obj_tag(v_a_5402_) == 0)
{
lean_dec_ref_known(v_a_5402_, 1);
return v___x_5401_;
}
else
{
lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5410_; 
lean_dec_ref_known(v_a_5402_, 1);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5410_ == 0)
{
lean_object* v_unused_5411_; 
v_unused_5411_ = lean_ctor_get(v___x_5401_, 0);
lean_dec(v_unused_5411_);
v___x_5404_ = v___x_5401_;
v_isShared_5405_ = v_isSharedCheck_5410_;
goto v_resetjp_5403_;
}
else
{
lean_dec(v___x_5401_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5410_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5406_; lean_object* v___x_5408_; 
v___x_5406_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___redArg___closed__0));
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 0, v___x_5406_);
v___x_5408_ = v___x_5404_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v___x_5406_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
else
{
return v___x_5401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed(lean_object* v_structName_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_Server_Completion_fieldIdCompletion___lam__0(v_structName_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec_ref(v___y_5413_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* v_uri_5424_, lean_object* v_pos_5425_, lean_object* v_completionInfoPos_5426_, lean_object* v_ctx_5427_, lean_object* v_lctx_5428_, lean_object* v_id_5429_, lean_object* v_structName_5430_, lean_object* v_a_5431_){
_start:
{
lean_object* v___y_5434_; 
if (lean_obj_tag(v_id_5429_) == 0)
{
lean_object* v___x_5437_; 
v___x_5437_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___y_5434_ = v___x_5437_;
goto v___jp_5433_;
}
else
{
lean_object* v_val_5438_; uint8_t v___x_5439_; lean_object* v___x_5440_; 
v_val_5438_ = lean_ctor_get(v_id_5429_, 0);
lean_inc(v_val_5438_);
lean_dec_ref_known(v_id_5429_, 1);
v___x_5439_ = 1;
v___x_5440_ = l_Lean_Name_toString(v_val_5438_, v___x_5439_);
v___y_5434_ = v___x_5440_;
goto v___jp_5433_;
}
v___jp_5433_:
{
lean_object* v___f_5435_; lean_object* v___x_5436_; 
v___f_5435_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5435_, 0, v_structName_5430_);
lean_closure_set(v___f_5435_, 1, v___y_5434_);
v___x_5436_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(v_uri_5424_, v_pos_5425_, v_completionInfoPos_5426_, v_ctx_5427_, v_lctx_5428_, v___f_5435_, v_a_5431_);
return v___x_5436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___boxed(lean_object* v_uri_5441_, lean_object* v_pos_5442_, lean_object* v_completionInfoPos_5443_, lean_object* v_ctx_5444_, lean_object* v_lctx_5445_, lean_object* v_id_5446_, lean_object* v_structName_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_5441_, v_pos_5442_, v_completionInfoPos_5443_, v_ctx_5444_, v_lctx_5445_, v_id_5446_, v_structName_5447_, v_a_5448_);
lean_dec_ref(v_a_5448_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(lean_object* v___y_5451_, lean_object* v_as_5452_, size_t v_sz_5453_, size_t v_i_5454_, lean_object* v_b_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___redArg(v___y_5451_, v_as_5452_, v_sz_5453_, v_i_5454_, v_b_5455_, v___y_5456_, v___y_5457_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0___boxed(lean_object* v___y_5465_, lean_object* v_as_5466_, lean_object* v_sz_5467_, lean_object* v_i_5468_, lean_object* v_b_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_){
_start:
{
size_t v_sz_boxed_5478_; size_t v_i_boxed_5479_; lean_object* v_res_5480_; 
v_sz_boxed_5478_ = lean_unbox_usize(v_sz_5467_);
lean_dec(v_sz_5467_);
v_i_boxed_5479_ = lean_unbox_usize(v_i_5468_);
lean_dec(v_i_5468_);
v_res_5480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_fieldIdCompletion_spec__0(v___y_5465_, v_as_5466_, v_sz_boxed_5478_, v_i_boxed_5479_, v_b_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
lean_dec(v___y_5476_);
lean_dec_ref(v___y_5475_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec_ref(v_as_5466_);
lean_dec_ref(v___y_5465_);
return v_res_5480_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0(void){
_start:
{
uint32_t v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = 32;
v___x_5482_ = l_Char_utf8Size(v___x_5481_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(lean_object* v_fst_5483_, lean_object* v_caps_5484_, lean_object* v_mkItem_5485_, lean_object* v_ctx_5486_, lean_object* v_stx_5487_, uint8_t v_snd_5488_, lean_object* v_x_5489_, lean_object* v_____s_5490_){
_start:
{
lean_object* v_fst_5491_; lean_object* v_snd_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5546_; 
v_fst_5491_ = lean_ctor_get(v_x_5489_, 0);
v_snd_5492_ = lean_ctor_get(v_x_5489_, 1);
v_isSharedCheck_5546_ = !lean_is_exclusive(v_x_5489_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5494_ = v_x_5489_;
v_isShared_5495_ = v_isSharedCheck_5546_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_snd_5492_);
lean_inc(v_fst_5491_);
lean_dec(v_x_5489_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5546_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___y_5497_; uint8_t v___x_5501_; lean_object* v___x_5502_; lean_object* v___y_5504_; lean_object* v___y_5505_; uint8_t v___y_5524_; uint8_t v___x_5534_; 
v___x_5501_ = 1;
lean_inc(v_fst_5491_);
v___x_5502_ = l_Lean_Name_toString(v_fst_5491_, v___x_5501_);
v___x_5534_ = l_Lean_String_charactersIn(v_fst_5483_, v___x_5502_);
if (v___x_5534_ == 0)
{
lean_object* v___x_5537_; 
lean_dec_ref(v___x_5502_);
lean_del_object(v___x_5494_);
lean_dec(v_snd_5492_);
lean_dec(v_fst_5491_);
lean_dec_ref(v_ctx_5486_);
lean_dec_ref(v_mkItem_5485_);
v___x_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5537_, 0, v_____s_5490_);
return v___x_5537_;
}
else
{
lean_object* v_textDocument_x3f_5538_; 
v_textDocument_x3f_5538_ = lean_ctor_get(v_caps_5484_, 0);
if (lean_obj_tag(v_textDocument_x3f_5538_) == 0)
{
goto v___jp_5535_;
}
else
{
lean_object* v_val_5539_; lean_object* v_completion_x3f_5540_; 
v_val_5539_ = lean_ctor_get(v_textDocument_x3f_5538_, 0);
v_completion_x3f_5540_ = lean_ctor_get(v_val_5539_, 0);
if (lean_obj_tag(v_completion_x3f_5540_) == 0)
{
goto v___jp_5535_;
}
else
{
lean_object* v_val_5541_; 
v_val_5541_ = lean_ctor_get(v_completion_x3f_5540_, 0);
if (lean_obj_tag(v_val_5541_) == 0)
{
goto v___jp_5535_;
}
else
{
lean_object* v_val_5542_; 
v_val_5542_ = lean_ctor_get(v_val_5541_, 0);
if (lean_obj_tag(v_val_5542_) == 0)
{
goto v___jp_5535_;
}
else
{
lean_object* v_val_5543_; uint8_t v___x_5544_; 
v_val_5543_ = lean_ctor_get(v_val_5542_, 0);
v___x_5544_ = lean_unbox(v_val_5543_);
if (v___x_5544_ == 0)
{
goto v___jp_5535_;
}
else
{
uint8_t v___x_5545_; 
v___x_5545_ = 0;
v___y_5524_ = v___x_5545_;
goto v___jp_5523_;
}
}
}
}
}
}
v___jp_5496_:
{
lean_object* v___x_5498_; lean_object* v_items_5499_; lean_object* v___x_5500_; 
v___x_5498_ = lean_apply_3(v_mkItem_5485_, v_fst_5491_, v_snd_5492_, v___y_5497_);
v_items_5499_ = lean_array_push(v_____s_5490_, v___x_5498_);
v___x_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5500_, 0, v_items_5499_);
return v___x_5500_;
}
v___jp_5503_:
{
lean_object* v_toCommandContextInfo_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5520_; 
v_toCommandContextInfo_5506_ = lean_ctor_get(v_ctx_5486_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v_ctx_5486_);
if (v_isSharedCheck_5520_ == 0)
{
lean_object* v_unused_5521_; lean_object* v_unused_5522_; 
v_unused_5521_ = lean_ctor_get(v_ctx_5486_, 2);
lean_dec(v_unused_5521_);
v_unused_5522_ = lean_ctor_get(v_ctx_5486_, 1);
lean_dec(v_unused_5522_);
v___x_5508_ = v_ctx_5486_;
v_isShared_5509_ = v_isSharedCheck_5520_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_toCommandContextInfo_5506_);
lean_dec(v_ctx_5486_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5520_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v_fileMap_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v_range_5514_; 
v_fileMap_5510_ = lean_ctor_get(v_toCommandContextInfo_5506_, 2);
lean_inc_ref_n(v_fileMap_5510_, 2);
lean_dec_ref(v_toCommandContextInfo_5506_);
v___x_5511_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5510_, v___y_5504_);
lean_dec(v___y_5504_);
v___x_5512_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5510_, v___y_5505_);
lean_dec(v___y_5505_);
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5512_);
lean_ctor_set(v___x_5494_, 0, v___x_5511_);
v_range_5514_ = v___x_5494_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5511_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5512_);
v_range_5514_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; 
lean_inc_ref(v_range_5514_);
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 2, v_range_5514_);
lean_ctor_set(v___x_5508_, 1, v_range_5514_);
lean_ctor_set(v___x_5508_, 0, v___x_5502_);
v___x_5516_ = v___x_5508_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5502_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v_range_5514_);
lean_ctor_set(v_reuseFailAlloc_5518_, 2, v_range_5514_);
v___x_5516_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5517_; 
v___x_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5517_, 0, v___x_5516_);
v___y_5497_ = v___x_5517_;
goto v___jp_5496_;
}
}
}
}
v___jp_5523_:
{
lean_object* v___x_5525_; 
v___x_5525_ = l_Lean_Syntax_getRange_x3f(v_stx_5487_, v___y_5524_);
if (lean_obj_tag(v___x_5525_) == 1)
{
lean_object* v_val_5526_; 
v_val_5526_ = lean_ctor_get(v___x_5525_, 0);
lean_inc(v_val_5526_);
lean_dec_ref_known(v___x_5525_, 1);
if (v_snd_5488_ == 0)
{
lean_object* v_start_5527_; lean_object* v_stop_5528_; 
v_start_5527_ = lean_ctor_get(v_val_5526_, 0);
lean_inc(v_start_5527_);
v_stop_5528_ = lean_ctor_get(v_val_5526_, 1);
lean_inc(v_stop_5528_);
lean_dec(v_val_5526_);
v___y_5504_ = v_start_5527_;
v___y_5505_ = v_stop_5528_;
goto v___jp_5503_;
}
else
{
lean_object* v_start_5529_; lean_object* v_stop_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; 
v_start_5529_ = lean_ctor_get(v_val_5526_, 0);
lean_inc(v_start_5529_);
v_stop_5530_ = lean_ctor_get(v_val_5526_, 1);
lean_inc(v_stop_5530_);
lean_dec(v_val_5526_);
v___x_5531_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5532_ = lean_nat_add(v_stop_5530_, v___x_5531_);
lean_dec(v_stop_5530_);
v___y_5504_ = v_start_5529_;
v___y_5505_ = v___x_5532_;
goto v___jp_5503_;
}
}
else
{
lean_object* v___x_5533_; 
lean_dec(v___x_5525_);
lean_dec_ref(v___x_5502_);
lean_del_object(v___x_5494_);
lean_dec_ref(v_ctx_5486_);
v___x_5533_ = lean_box(0);
v___y_5497_ = v___x_5533_;
goto v___jp_5496_;
}
}
v___jp_5535_:
{
if (v___x_5534_ == 0)
{
v___y_5524_ = v___x_5534_;
goto v___jp_5523_;
}
else
{
lean_object* v___x_5536_; 
lean_dec_ref(v___x_5502_);
lean_del_object(v___x_5494_);
lean_dec_ref(v_ctx_5486_);
v___x_5536_ = lean_box(0);
v___y_5497_ = v___x_5536_;
goto v___jp_5496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed(lean_object* v_fst_5547_, lean_object* v_caps_5548_, lean_object* v_mkItem_5549_, lean_object* v_ctx_5550_, lean_object* v_stx_5551_, lean_object* v_snd_5552_, lean_object* v_x_5553_, lean_object* v_____s_5554_){
_start:
{
uint8_t v_snd_832__boxed_5555_; lean_object* v_res_5556_; 
v_snd_832__boxed_5555_ = lean_unbox(v_snd_5552_);
v_res_5556_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0(v_fst_5547_, v_caps_5548_, v_mkItem_5549_, v_ctx_5550_, v_stx_5551_, v_snd_832__boxed_5555_, v_x_5553_, v_____s_5554_);
lean_dec(v_stx_5551_);
lean_dec_ref(v_caps_5548_);
lean_dec_ref(v_fst_5547_);
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(lean_object* v_inst_5558_, lean_object* v_entries_5559_, lean_object* v_stx_5560_, lean_object* v_caps_5561_, lean_object* v_ctx_5562_, lean_object* v_mkItem_5563_){
_start:
{
lean_object* v_fst_5565_; uint8_t v_snd_5566_; uint8_t v___x_5571_; lean_object* v___x_5572_; 
v___x_5571_ = 0;
v___x_5572_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5560_, v___x_5571_, v___x_5571_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v___x_5573_; 
v___x_5573_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5565_ = v___x_5573_;
v_snd_5566_ = v___x_5571_;
goto v___jp_5564_;
}
else
{
lean_object* v_val_5574_; lean_object* v_str_5575_; lean_object* v_startPos_5576_; lean_object* v_stopPos_5577_; uint8_t v___y_5579_; uint8_t v___x_5581_; 
v_val_5574_ = lean_ctor_get(v___x_5572_, 0);
lean_inc(v_val_5574_);
lean_dec_ref_known(v___x_5572_, 1);
v_str_5575_ = lean_ctor_get(v_val_5574_, 0);
lean_inc_ref(v_str_5575_);
v_startPos_5576_ = lean_ctor_get(v_val_5574_, 1);
lean_inc(v_startPos_5576_);
v_stopPos_5577_ = lean_ctor_get(v_val_5574_, 2);
lean_inc(v_stopPos_5577_);
lean_dec(v_val_5574_);
v___x_5581_ = lean_string_utf8_at_end(v_str_5575_, v_stopPos_5577_);
if (v___x_5581_ == 0)
{
uint32_t v___x_5582_; uint32_t v___x_5583_; uint8_t v___x_5584_; 
v___x_5582_ = lean_string_utf8_get(v_str_5575_, v_stopPos_5577_);
v___x_5583_ = 46;
v___x_5584_ = lean_uint32_dec_eq(v___x_5582_, v___x_5583_);
if (v___x_5584_ == 0)
{
v___y_5579_ = v___x_5584_;
goto v___jp_5578_;
}
else
{
lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5585_ = lean_string_utf8_extract(v_str_5575_, v_startPos_5576_, v_stopPos_5577_);
lean_dec(v_stopPos_5577_);
lean_dec(v_startPos_5576_);
lean_dec_ref(v_str_5575_);
v___x_5586_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5587_ = lean_string_append(v___x_5585_, v___x_5586_);
v_fst_5565_ = v___x_5587_;
v_snd_5566_ = v___x_5584_;
goto v___jp_5564_;
}
}
else
{
v___y_5579_ = v___x_5571_;
goto v___jp_5578_;
}
v___jp_5578_:
{
lean_object* v___x_5580_; 
v___x_5580_ = lean_string_utf8_extract(v_str_5575_, v_startPos_5576_, v_stopPos_5577_);
lean_dec(v_stopPos_5577_);
lean_dec(v_startPos_5576_);
lean_dec_ref(v_str_5575_);
v_fst_5565_ = v___x_5580_;
v_snd_5566_ = v___y_5579_;
goto v___jp_5564_;
}
}
v___jp_5564_:
{
lean_object* v___x_5567_; lean_object* v___f_5568_; lean_object* v_items_5569_; lean_object* v___x_5570_; 
v___x_5567_ = lean_box(v_snd_5566_);
v___f_5568_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_5568_, 0, v_fst_5565_);
lean_closure_set(v___f_5568_, 1, v_caps_5561_);
lean_closure_set(v___f_5568_, 2, v_mkItem_5563_);
lean_closure_set(v___f_5568_, 3, v_ctx_5562_);
lean_closure_set(v___f_5568_, 4, v_stx_5560_);
lean_closure_set(v___f_5568_, 5, v___x_5567_);
v_items_5569_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5570_ = lean_apply_4(v_inst_5558_, lean_box(0), v_entries_5559_, v_items_5569_, v___f_5568_);
return v___x_5570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion(lean_object* v_Coll_5588_, lean_object* v_00_u03b1_5589_, lean_object* v_inst_5590_, lean_object* v_entries_5591_, lean_object* v_stx_5592_, lean_object* v_caps_5593_, lean_object* v_ctx_5594_, lean_object* v_mkItem_5595_){
_start:
{
lean_object* v___x_5596_; 
v___x_5596_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg(v_inst_5590_, v_entries_5591_, v_stx_5592_, v_caps_5593_, v_ctx_5594_, v_mkItem_5595_);
return v___x_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0(lean_object* v_options_5602_, lean_object* v_completionInfoPos_5603_, lean_object* v_uri_5604_, lean_object* v_pos_5605_, lean_object* v_name_5606_, lean_object* v_decl_5607_, lean_object* v_textEdit_x3f_5608_){
_start:
{
lean_object* v_defValue_5609_; lean_object* v_descr_5610_; lean_object* v_map_5611_; uint8_t v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___y_5616_; lean_object* v___x_5629_; 
v_defValue_5609_ = lean_ctor_get(v_decl_5607_, 2);
lean_inc_ref(v_defValue_5609_);
v_descr_5610_ = lean_ctor_get(v_decl_5607_, 3);
lean_inc_ref(v_descr_5610_);
lean_dec_ref(v_decl_5607_);
v_map_5611_ = lean_ctor_get(v_options_5602_, 0);
v___x_5612_ = 1;
lean_inc(v_name_5606_);
v___x_5613_ = l_Lean_Name_toString(v_name_5606_, v___x_5612_);
v___x_5614_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__0));
v___x_5629_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5611_, v_name_5606_);
lean_dec(v_name_5606_);
if (lean_obj_tag(v___x_5629_) == 0)
{
v___y_5616_ = v_defValue_5609_;
goto v___jp_5615_;
}
else
{
if (lean_obj_tag(v___x_5629_) == 0)
{
v___y_5616_ = v_defValue_5609_;
goto v___jp_5615_;
}
else
{
lean_object* v_val_5630_; 
lean_dec_ref(v_defValue_5609_);
v_val_5630_ = lean_ctor_get(v___x_5629_, 0);
lean_inc(v_val_5630_);
lean_dec_ref_known(v___x_5629_, 1);
v___y_5616_ = v_val_5630_;
goto v___jp_5615_;
}
}
v___jp_5615_:
{
lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5617_ = lean_data_value_to_string(v___y_5616_);
v___x_5618_ = lean_string_append(v___x_5614_, v___x_5617_);
lean_dec_ref(v___x_5617_);
v___x_5619_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__1));
v___x_5620_ = lean_string_append(v___x_5618_, v___x_5619_);
v___x_5621_ = lean_string_append(v___x_5620_, v_descr_5610_);
lean_dec_ref(v_descr_5610_);
v___x_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
v___x_5623_ = lean_box(0);
v___x_5624_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5625_, 0, v_completionInfoPos_5603_);
v___x_5626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5626_, 0, v_uri_5604_);
lean_ctor_set(v___x_5626_, 1, v_pos_5605_);
lean_ctor_set(v___x_5626_, 2, v___x_5625_);
lean_ctor_set(v___x_5626_, 3, v___x_5623_);
v___x_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
v___x_5628_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5613_);
lean_ctor_set(v___x_5628_, 1, v___x_5622_);
lean_ctor_set(v___x_5628_, 2, v___x_5623_);
lean_ctor_set(v___x_5628_, 3, v___x_5624_);
lean_ctor_set(v___x_5628_, 4, v_textEdit_x3f_5608_);
lean_ctor_set(v___x_5628_, 5, v___x_5623_);
lean_ctor_set(v___x_5628_, 6, v___x_5627_);
lean_ctor_set(v___x_5628_, 7, v___x_5623_);
return v___x_5628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__0___boxed(lean_object* v_options_5631_, lean_object* v_completionInfoPos_5632_, lean_object* v_uri_5633_, lean_object* v_pos_5634_, lean_object* v_name_5635_, lean_object* v_decl_5636_, lean_object* v_textEdit_x3f_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l_Lean_Server_Completion_optionCompletion___lam__0(v_options_5631_, v_completionInfoPos_5632_, v_uri_5633_, v_pos_5634_, v_name_5635_, v_decl_5636_, v_textEdit_x3f_5637_);
lean_dec_ref(v_options_5631_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(lean_object* v_mkItem_5639_, lean_object* v_stx_5640_, lean_object* v_ctx_5641_, uint8_t v_snd_5642_, lean_object* v_fst_5643_, lean_object* v_caps_5644_, lean_object* v_init_5645_, lean_object* v_x_5646_){
_start:
{
if (lean_obj_tag(v_x_5646_) == 0)
{
lean_object* v_k_5647_; lean_object* v_v_5648_; lean_object* v_l_5649_; lean_object* v_r_5650_; lean_object* v___x_5651_; lean_object* v_a_5652_; lean_object* v___y_5654_; uint8_t v___x_5658_; lean_object* v___x_5659_; lean_object* v___y_5661_; lean_object* v___y_5662_; uint8_t v___y_5671_; uint8_t v___x_5681_; 
v_k_5647_ = lean_ctor_get(v_x_5646_, 1);
lean_inc_n(v_k_5647_, 2);
v_v_5648_ = lean_ctor_get(v_x_5646_, 2);
lean_inc(v_v_5648_);
v_l_5649_ = lean_ctor_get(v_x_5646_, 3);
lean_inc(v_l_5649_);
v_r_5650_ = lean_ctor_get(v_x_5646_, 4);
lean_inc(v_r_5650_);
lean_dec_ref_known(v_x_5646_, 5);
lean_inc_ref(v_ctx_5641_);
lean_inc_ref(v_mkItem_5639_);
v___x_5651_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5639_, v_stx_5640_, v_ctx_5641_, v_snd_5642_, v_fst_5643_, v_caps_5644_, v_init_5645_, v_l_5649_);
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
v___x_5658_ = 1;
v___x_5659_ = l_Lean_Name_toString(v_k_5647_, v___x_5658_);
v___x_5681_ = l_Lean_String_charactersIn(v_fst_5643_, v___x_5659_);
if (v___x_5681_ == 0)
{
lean_object* v_a_5684_; 
lean_dec_ref(v___x_5659_);
lean_dec(v_a_5652_);
lean_dec(v_v_5648_);
lean_dec(v_k_5647_);
v_a_5684_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5684_);
lean_dec_ref(v___x_5651_);
v_init_5645_ = v_a_5684_;
v_x_5646_ = v_r_5650_;
goto _start;
}
else
{
lean_object* v_textDocument_x3f_5686_; 
lean_dec_ref(v___x_5651_);
v_textDocument_x3f_5686_ = lean_ctor_get(v_caps_5644_, 0);
if (lean_obj_tag(v_textDocument_x3f_5686_) == 0)
{
goto v___jp_5682_;
}
else
{
lean_object* v_val_5687_; lean_object* v_completion_x3f_5688_; 
v_val_5687_ = lean_ctor_get(v_textDocument_x3f_5686_, 0);
v_completion_x3f_5688_ = lean_ctor_get(v_val_5687_, 0);
if (lean_obj_tag(v_completion_x3f_5688_) == 0)
{
goto v___jp_5682_;
}
else
{
lean_object* v_val_5689_; 
v_val_5689_ = lean_ctor_get(v_completion_x3f_5688_, 0);
if (lean_obj_tag(v_val_5689_) == 0)
{
goto v___jp_5682_;
}
else
{
lean_object* v_val_5690_; 
v_val_5690_ = lean_ctor_get(v_val_5689_, 0);
if (lean_obj_tag(v_val_5690_) == 0)
{
goto v___jp_5682_;
}
else
{
lean_object* v_val_5691_; uint8_t v___x_5692_; 
v_val_5691_ = lean_ctor_get(v_val_5690_, 0);
v___x_5692_ = lean_unbox(v_val_5691_);
if (v___x_5692_ == 0)
{
goto v___jp_5682_;
}
else
{
uint8_t v___x_5693_; 
v___x_5693_ = 0;
v___y_5671_ = v___x_5693_;
goto v___jp_5670_;
}
}
}
}
}
}
v___jp_5653_:
{
lean_object* v___x_5655_; lean_object* v_items_5656_; 
lean_inc_ref(v_mkItem_5639_);
v___x_5655_ = lean_apply_3(v_mkItem_5639_, v_k_5647_, v_v_5648_, v___y_5654_);
v_items_5656_ = lean_array_push(v_a_5652_, v___x_5655_);
v_init_5645_ = v_items_5656_;
v_x_5646_ = v_r_5650_;
goto _start;
}
v___jp_5660_:
{
lean_object* v_toCommandContextInfo_5663_; lean_object* v_fileMap_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v_range_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v_toCommandContextInfo_5663_ = lean_ctor_get(v_ctx_5641_, 0);
v_fileMap_5664_ = lean_ctor_get(v_toCommandContextInfo_5663_, 2);
lean_inc_ref_n(v_fileMap_5664_, 2);
v___x_5665_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5664_, v___y_5661_);
lean_dec(v___y_5661_);
v___x_5666_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_5664_, v___y_5662_);
lean_dec(v___y_5662_);
v_range_5667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_5667_, 0, v___x_5665_);
lean_ctor_set(v_range_5667_, 1, v___x_5666_);
lean_inc_ref(v_range_5667_);
v___x_5668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5659_);
lean_ctor_set(v___x_5668_, 1, v_range_5667_);
lean_ctor_set(v___x_5668_, 2, v_range_5667_);
v___x_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
v___y_5654_ = v___x_5669_;
goto v___jp_5653_;
}
v___jp_5670_:
{
lean_object* v___x_5672_; 
v___x_5672_ = l_Lean_Syntax_getRange_x3f(v_stx_5640_, v___y_5671_);
if (lean_obj_tag(v___x_5672_) == 1)
{
lean_object* v_val_5673_; 
v_val_5673_ = lean_ctor_get(v___x_5672_, 0);
lean_inc(v_val_5673_);
lean_dec_ref_known(v___x_5672_, 1);
if (v_snd_5642_ == 0)
{
lean_object* v_start_5674_; lean_object* v_stop_5675_; 
v_start_5674_ = lean_ctor_get(v_val_5673_, 0);
lean_inc(v_start_5674_);
v_stop_5675_ = lean_ctor_get(v_val_5673_, 1);
lean_inc(v_stop_5675_);
lean_dec(v_val_5673_);
v___y_5661_ = v_start_5674_;
v___y_5662_ = v_stop_5675_;
goto v___jp_5660_;
}
else
{
lean_object* v_start_5676_; lean_object* v_stop_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
v_start_5676_ = lean_ctor_get(v_val_5673_, 0);
lean_inc(v_start_5676_);
v_stop_5677_ = lean_ctor_get(v_val_5673_, 1);
lean_inc(v_stop_5677_);
lean_dec(v_val_5673_);
v___x_5678_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_5679_ = lean_nat_add(v_stop_5677_, v___x_5678_);
lean_dec(v_stop_5677_);
v___y_5661_ = v_start_5676_;
v___y_5662_ = v___x_5679_;
goto v___jp_5660_;
}
}
else
{
lean_object* v___x_5680_; 
lean_dec(v___x_5672_);
lean_dec_ref(v___x_5659_);
v___x_5680_ = lean_box(0);
v___y_5654_ = v___x_5680_;
goto v___jp_5653_;
}
}
v___jp_5682_:
{
if (v___x_5681_ == 0)
{
v___y_5671_ = v___x_5681_;
goto v___jp_5670_;
}
else
{
lean_object* v___x_5683_; 
lean_dec_ref(v___x_5659_);
v___x_5683_ = lean_box(0);
v___y_5654_ = v___x_5683_;
goto v___jp_5653_;
}
}
}
else
{
lean_object* v___x_5694_; 
lean_dec_ref(v_ctx_5641_);
lean_dec_ref(v_mkItem_5639_);
v___x_5694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5694_, 0, v_init_5645_);
return v___x_5694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0___boxed(lean_object* v_mkItem_5695_, lean_object* v_stx_5696_, lean_object* v_ctx_5697_, lean_object* v_snd_5698_, lean_object* v_fst_5699_, lean_object* v_caps_5700_, lean_object* v_init_5701_, lean_object* v_x_5702_){
_start:
{
uint8_t v_snd_1430__boxed_5703_; lean_object* v_res_5704_; 
v_snd_1430__boxed_5703_ = lean_unbox(v_snd_5698_);
v_res_5704_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5695_, v_stx_5696_, v_ctx_5697_, v_snd_1430__boxed_5703_, v_fst_5699_, v_caps_5700_, v_init_5701_, v_x_5702_);
lean_dec_ref(v_caps_5700_);
lean_dec_ref(v_fst_5699_);
lean_dec(v_stx_5696_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(lean_object* v_entries_5705_, lean_object* v_stx_5706_, lean_object* v_caps_5707_, lean_object* v_ctx_5708_, lean_object* v_mkItem_5709_){
_start:
{
lean_object* v_fst_5711_; uint8_t v_snd_5712_; uint8_t v___x_5716_; lean_object* v___x_5717_; 
v___x_5716_ = 0;
v___x_5717_ = l_Lean_Syntax_getSubstring_x3f(v_stx_5706_, v___x_5716_, v___x_5716_);
if (lean_obj_tag(v___x_5717_) == 0)
{
lean_object* v___x_5718_; 
v___x_5718_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_5711_ = v___x_5718_;
v_snd_5712_ = v___x_5716_;
goto v___jp_5710_;
}
else
{
lean_object* v_val_5719_; lean_object* v_str_5720_; lean_object* v_startPos_5721_; lean_object* v_stopPos_5722_; uint8_t v___y_5724_; uint8_t v___x_5726_; 
v_val_5719_ = lean_ctor_get(v___x_5717_, 0);
lean_inc(v_val_5719_);
lean_dec_ref_known(v___x_5717_, 1);
v_str_5720_ = lean_ctor_get(v_val_5719_, 0);
lean_inc_ref(v_str_5720_);
v_startPos_5721_ = lean_ctor_get(v_val_5719_, 1);
lean_inc(v_startPos_5721_);
v_stopPos_5722_ = lean_ctor_get(v_val_5719_, 2);
lean_inc(v_stopPos_5722_);
lean_dec(v_val_5719_);
v___x_5726_ = lean_string_utf8_at_end(v_str_5720_, v_stopPos_5722_);
if (v___x_5726_ == 0)
{
uint32_t v___x_5727_; uint32_t v___x_5728_; uint8_t v___x_5729_; 
v___x_5727_ = lean_string_utf8_get(v_str_5720_, v_stopPos_5722_);
v___x_5728_ = 46;
v___x_5729_ = lean_uint32_dec_eq(v___x_5727_, v___x_5728_);
if (v___x_5729_ == 0)
{
v___y_5724_ = v___x_5729_;
goto v___jp_5723_;
}
else
{
lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5730_ = lean_string_utf8_extract(v_str_5720_, v_startPos_5721_, v_stopPos_5722_);
lean_dec(v_stopPos_5722_);
lean_dec(v_startPos_5721_);
lean_dec_ref(v_str_5720_);
v___x_5731_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_5732_ = lean_string_append(v___x_5730_, v___x_5731_);
v_fst_5711_ = v___x_5732_;
v_snd_5712_ = v___x_5729_;
goto v___jp_5710_;
}
}
else
{
v___y_5724_ = v___x_5716_;
goto v___jp_5723_;
}
v___jp_5723_:
{
lean_object* v___x_5725_; 
v___x_5725_ = lean_string_utf8_extract(v_str_5720_, v_startPos_5721_, v_stopPos_5722_);
lean_dec(v_stopPos_5722_);
lean_dec(v_startPos_5721_);
lean_dec_ref(v_str_5720_);
v_fst_5711_ = v___x_5725_;
v_snd_5712_ = v___y_5724_;
goto v___jp_5710_;
}
}
v___jp_5710_:
{
lean_object* v_items_5713_; lean_object* v___x_5714_; lean_object* v_a_5715_; 
v_items_5713_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v___x_5714_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0_spec__0(v_mkItem_5709_, v_stx_5706_, v_ctx_5708_, v_snd_5712_, v_fst_5711_, v_caps_5707_, v_items_5713_, v_entries_5705_);
lean_dec_ref(v_fst_5711_);
v_a_5715_ = lean_ctor_get(v___x_5714_, 0);
lean_inc(v_a_5715_);
lean_dec_ref(v___x_5714_);
return v_a_5715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0___boxed(lean_object* v_entries_5733_, lean_object* v_stx_5734_, lean_object* v_caps_5735_, lean_object* v_ctx_5736_, lean_object* v_mkItem_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_entries_5733_, v_stx_5734_, v_caps_5735_, v_ctx_5736_, v_mkItem_5737_);
lean_dec_ref(v_caps_5735_);
lean_dec(v_stx_5734_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1(lean_object* v_completionInfoPos_5739_, lean_object* v_uri_5740_, lean_object* v_pos_5741_, lean_object* v_stx_5742_, lean_object* v_caps_5743_, lean_object* v_ctx_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
lean_object* v___x_5750_; 
v___x_5750_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5763_; 
v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5763_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5763_ == 0)
{
v___x_5753_ = v___x_5750_;
v_isShared_5754_ = v_isSharedCheck_5763_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5763_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v_options_5755_; lean_object* v___f_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5761_; 
v_options_5755_ = lean_ctor_get(v___y_5747_, 1);
lean_inc_ref(v_options_5755_);
lean_dec_ref(v___y_5747_);
v___f_5756_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5756_, 0, v_options_5755_);
lean_closure_set(v___f_5756_, 1, v_completionInfoPos_5739_);
lean_closure_set(v___f_5756_, 2, v_uri_5740_);
lean_closure_set(v___f_5756_, 3, v_pos_5741_);
v___x_5757_ = lean_unsigned_to_nat(1u);
v___x_5758_ = l_Lean_Syntax_getArg(v_stx_5742_, v___x_5757_);
v___x_5759_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_optionCompletion_spec__0(v_a_5751_, v___x_5758_, v_caps_5743_, v_ctx_5744_, v___f_5756_);
lean_dec(v___x_5758_);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 0, v___x_5759_);
v___x_5761_ = v___x_5753_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5759_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
else
{
lean_object* v_a_5764_; lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5776_; 
lean_dec_ref(v_ctx_5744_);
lean_dec_ref(v_pos_5741_);
lean_dec_ref(v_uri_5740_);
lean_dec(v_completionInfoPos_5739_);
v_a_5764_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5766_ = v___x_5750_;
v_isShared_5767_ = v_isSharedCheck_5776_;
goto v_resetjp_5765_;
}
else
{
lean_inc(v_a_5764_);
lean_dec(v___x_5750_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5776_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
lean_object* v_ref_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5774_; 
v_ref_5768_ = lean_ctor_get(v___y_5747_, 4);
lean_inc(v_ref_5768_);
lean_dec_ref(v___y_5747_);
v___x_5769_ = lean_io_error_to_string(v_a_5764_);
v___x_5770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5769_);
v___x_5771_ = l_Lean_MessageData_ofFormat(v___x_5770_);
v___x_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5772_, 0, v_ref_5768_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
if (v_isShared_5767_ == 0)
{
lean_ctor_set(v___x_5766_, 0, v___x_5772_);
v___x_5774_ = v___x_5766_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lam__1___boxed(lean_object* v_completionInfoPos_5777_, lean_object* v_uri_5778_, lean_object* v_pos_5779_, lean_object* v_stx_5780_, lean_object* v_caps_5781_, lean_object* v_ctx_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l_Lean_Server_Completion_optionCompletion___lam__1(v_completionInfoPos_5777_, v_uri_5778_, v_pos_5779_, v_stx_5780_, v_caps_5781_, v_ctx_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_);
lean_dec(v___y_5786_);
lean_dec(v___y_5784_);
lean_dec_ref(v___y_5783_);
lean_dec_ref(v_caps_5781_);
lean_dec(v_stx_5780_);
return v_res_5788_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__0(void){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5789_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1(void){
_start:
{
lean_object* v___x_5790_; lean_object* v___x_5791_; 
v___x_5790_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__0, &l_Lean_Server_Completion_optionCompletion___closed__0_once, _init_l_Lean_Server_Completion_optionCompletion___closed__0);
v___x_5791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5790_);
return v___x_5791_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2(void){
_start:
{
lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; 
v___x_5792_ = lean_unsigned_to_nat(32u);
v___x_5793_ = lean_mk_empty_array_with_capacity(v___x_5792_);
v___x_5794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5793_);
return v___x_5794_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3(void){
_start:
{
size_t v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v___x_5795_ = ((size_t)5ULL);
v___x_5796_ = lean_unsigned_to_nat(0u);
v___x_5797_ = lean_unsigned_to_nat(32u);
v___x_5798_ = lean_mk_empty_array_with_capacity(v___x_5797_);
v___x_5799_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__2, &l_Lean_Server_Completion_optionCompletion___closed__2_once, _init_l_Lean_Server_Completion_optionCompletion___closed__2);
v___x_5800_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5800_, 0, v___x_5799_);
lean_ctor_set(v___x_5800_, 1, v___x_5798_);
lean_ctor_set(v___x_5800_, 2, v___x_5796_);
lean_ctor_set(v___x_5800_, 3, v___x_5796_);
lean_ctor_set_usize(v___x_5800_, 4, v___x_5795_);
return v___x_5800_;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4(void){
_start:
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; 
v___x_5801_ = lean_box(1);
v___x_5802_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__3, &l_Lean_Server_Completion_optionCompletion___closed__3_once, _init_l_Lean_Server_Completion_optionCompletion___closed__3);
v___x_5803_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__1, &l_Lean_Server_Completion_optionCompletion___closed__1_once, _init_l_Lean_Server_Completion_optionCompletion___closed__1);
v___x_5804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5804_, 0, v___x_5803_);
lean_ctor_set(v___x_5804_, 1, v___x_5802_);
lean_ctor_set(v___x_5804_, 2, v___x_5801_);
return v___x_5804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* v_uri_5805_, lean_object* v_pos_5806_, lean_object* v_completionInfoPos_5807_, lean_object* v_ctx_5808_, lean_object* v_stx_5809_, lean_object* v_caps_5810_){
_start:
{
lean_object* v___f_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; 
lean_inc_ref(v_ctx_5808_);
v___f_5812_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lam__1___boxed), 11, 6);
lean_closure_set(v___f_5812_, 0, v_completionInfoPos_5807_);
lean_closure_set(v___f_5812_, 1, v_uri_5805_);
lean_closure_set(v___f_5812_, 2, v_pos_5806_);
lean_closure_set(v___f_5812_, 3, v_stx_5809_);
lean_closure_set(v___f_5812_, 4, v_caps_5810_);
lean_closure_set(v___f_5812_, 5, v_ctx_5808_);
v___x_5813_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_5814_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_5808_, v___x_5813_, v___f_5812_);
return v___x_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* v_uri_5815_, lean_object* v_pos_5816_, lean_object* v_completionInfoPos_5817_, lean_object* v_ctx_5818_, lean_object* v_stx_5819_, lean_object* v_caps_5820_, lean_object* v_a_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l_Lean_Server_Completion_optionCompletion(v_uri_5815_, v_pos_5816_, v_completionInfoPos_5817_, v_ctx_5818_, v_stx_5819_, v_caps_5820_);
return v_res_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0(lean_object* v_completionInfoPos_5832_, lean_object* v_uri_5833_, lean_object* v_pos_5834_, lean_object* v_name_5835_, lean_object* v_explan_5836_, lean_object* v_textEdit_x3f_5837_){
_start:
{
lean_object* v_metadata_5838_; lean_object* v_removedVersion_x3f_5839_; uint8_t v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; uint8_t v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
v_metadata_5838_ = lean_ctor_get(v_explan_5836_, 1);
v_removedVersion_x3f_5839_ = lean_ctor_get(v_metadata_5838_, 2);
v___x_5840_ = 1;
v___x_5841_ = l_Lean_Name_toString(v_name_5835_, v___x_5840_);
v___x_5842_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__1));
v___x_5843_ = 1;
v___x_5844_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_5836_);
v___x_5845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5845_, 0, v___x_5844_);
lean_ctor_set_uint8(v___x_5845_, sizeof(void*)*1, v___x_5843_);
v___x_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5846_, 0, v___x_5845_);
v___x_5847_ = ((lean_object*)(l_Lean_Server_Completion_optionCompletion___lam__0___closed__2));
v___x_5848_ = lean_box(0);
v___x_5849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5849_, 0, v_completionInfoPos_5832_);
v___x_5850_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5850_, 0, v_uri_5833_);
lean_ctor_set(v___x_5850_, 1, v_pos_5834_);
lean_ctor_set(v___x_5850_, 2, v___x_5849_);
lean_ctor_set(v___x_5850_, 3, v___x_5848_);
v___x_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5850_);
if (lean_obj_tag(v_removedVersion_x3f_5839_) == 0)
{
lean_object* v___x_5852_; 
v___x_5852_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5852_, 0, v___x_5841_);
lean_ctor_set(v___x_5852_, 1, v___x_5842_);
lean_ctor_set(v___x_5852_, 2, v___x_5846_);
lean_ctor_set(v___x_5852_, 3, v___x_5847_);
lean_ctor_set(v___x_5852_, 4, v_textEdit_x3f_5837_);
lean_ctor_set(v___x_5852_, 5, v___x_5848_);
lean_ctor_set(v___x_5852_, 6, v___x_5851_);
lean_ctor_set(v___x_5852_, 7, v___x_5848_);
return v___x_5852_;
}
else
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = ((lean_object*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___closed__3));
v___x_5854_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5841_);
lean_ctor_set(v___x_5854_, 1, v___x_5842_);
lean_ctor_set(v___x_5854_, 2, v___x_5846_);
lean_ctor_set(v___x_5854_, 3, v___x_5847_);
lean_ctor_set(v___x_5854_, 4, v_textEdit_x3f_5837_);
lean_ctor_set(v___x_5854_, 5, v___x_5848_);
lean_ctor_set(v___x_5854_, 6, v___x_5851_);
lean_ctor_set(v___x_5854_, 7, v___x_5853_);
return v___x_5854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed(lean_object* v_completionInfoPos_5855_, lean_object* v_uri_5856_, lean_object* v_pos_5857_, lean_object* v_name_5858_, lean_object* v_explan_5859_, lean_object* v_textEdit_x3f_5860_){
_start:
{
lean_object* v_res_5861_; 
v_res_5861_ = l_Lean_Server_Completion_errorNameCompletion___lam__0(v_completionInfoPos_5855_, v_uri_5856_, v_pos_5857_, v_name_5858_, v_explan_5859_, v_textEdit_x3f_5860_);
lean_dec_ref(v_explan_5859_);
return v_res_5861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(lean_object* v_init_5862_, lean_object* v_x_5863_){
_start:
{
if (lean_obj_tag(v_x_5863_) == 0)
{
lean_object* v_k_5864_; lean_object* v_v_5865_; lean_object* v_l_5866_; lean_object* v_r_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v_k_5864_ = lean_ctor_get(v_x_5863_, 1);
v_v_5865_ = lean_ctor_get(v_x_5863_, 2);
v_l_5866_ = lean_ctor_get(v_x_5863_, 3);
v_r_5867_ = lean_ctor_get(v_x_5863_, 4);
v___x_5868_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5862_, v_l_5866_);
lean_inc(v_v_5865_);
lean_inc(v_k_5864_);
v___x_5869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5869_, 0, v_k_5864_);
lean_ctor_set(v___x_5869_, 1, v_v_5865_);
v___x_5870_ = lean_array_push(v___x_5868_, v___x_5869_);
v_init_5862_ = v___x_5870_;
v_x_5863_ = v_r_5867_;
goto _start;
}
else
{
return v_init_5862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5872_, lean_object* v_x_5873_){
_start:
{
lean_object* v_res_5874_; 
v_res_5874_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_5872_, v_x_5873_);
lean_dec(v_x_5873_);
return v_res_5874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(lean_object* v_hi_5875_, lean_object* v_pivot_5876_, lean_object* v_as_5877_, lean_object* v_i_5878_, lean_object* v_k_5879_){
_start:
{
uint8_t v___x_5880_; 
v___x_5880_ = lean_nat_dec_lt(v_k_5879_, v_hi_5875_);
if (v___x_5880_ == 0)
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
lean_dec(v_k_5879_);
lean_dec_ref(v_pivot_5876_);
v___x_5881_ = lean_array_fswap(v_as_5877_, v_i_5878_, v_hi_5875_);
v___x_5882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5882_, 0, v_i_5878_);
lean_ctor_set(v___x_5882_, 1, v___x_5881_);
return v___x_5882_;
}
else
{
lean_object* v___x_5883_; lean_object* v_fst_5884_; lean_object* v_fst_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; uint8_t v___x_5888_; 
v___x_5883_ = lean_array_fget_borrowed(v_as_5877_, v_k_5879_);
v_fst_5884_ = lean_ctor_get(v___x_5883_, 0);
v_fst_5885_ = lean_ctor_get(v_pivot_5876_, 0);
lean_inc(v_fst_5884_);
v___x_5886_ = l_Lean_Name_toString(v_fst_5884_, v___x_5880_);
lean_inc(v_fst_5885_);
v___x_5887_ = l_Lean_Name_toString(v_fst_5885_, v___x_5880_);
v___x_5888_ = lean_string_dec_lt(v___x_5886_, v___x_5887_);
lean_dec_ref(v___x_5887_);
lean_dec_ref(v___x_5886_);
if (v___x_5888_ == 0)
{
lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5889_ = lean_unsigned_to_nat(1u);
v___x_5890_ = lean_nat_add(v_k_5879_, v___x_5889_);
lean_dec(v_k_5879_);
v_k_5879_ = v___x_5890_;
goto _start;
}
else
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5892_ = lean_array_fswap(v_as_5877_, v_i_5878_, v_k_5879_);
v___x_5893_ = lean_unsigned_to_nat(1u);
v___x_5894_ = lean_nat_add(v_i_5878_, v___x_5893_);
lean_dec(v_i_5878_);
v___x_5895_ = lean_nat_add(v_k_5879_, v___x_5893_);
lean_dec(v_k_5879_);
v_as_5877_ = v___x_5892_;
v_i_5878_ = v___x_5894_;
v_k_5879_ = v___x_5895_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_hi_5897_, lean_object* v_pivot_5898_, lean_object* v_as_5899_, lean_object* v_i_5900_, lean_object* v_k_5901_){
_start:
{
lean_object* v_res_5902_; 
v_res_5902_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5897_, v_pivot_5898_, v_as_5899_, v_i_5900_, v_k_5901_);
lean_dec(v_hi_5897_);
return v_res_5902_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(uint8_t v___x_5903_, lean_object* v_e_5904_, lean_object* v_e_x27_5905_){
_start:
{
lean_object* v_fst_5906_; lean_object* v_fst_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; uint8_t v___x_5910_; 
v_fst_5906_ = lean_ctor_get(v_e_5904_, 0);
lean_inc(v_fst_5906_);
lean_dec_ref(v_e_5904_);
v_fst_5907_ = lean_ctor_get(v_e_x27_5905_, 0);
lean_inc(v_fst_5907_);
lean_dec_ref(v_e_x27_5905_);
v___x_5908_ = l_Lean_Name_toString(v_fst_5906_, v___x_5903_);
v___x_5909_ = l_Lean_Name_toString(v_fst_5907_, v___x_5903_);
v___x_5910_ = lean_string_dec_lt(v___x_5908_, v___x_5909_);
lean_dec_ref(v___x_5909_);
lean_dec_ref(v___x_5908_);
return v___x_5910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_5911_, lean_object* v_e_5912_, lean_object* v_e_x27_5913_){
_start:
{
uint8_t v___x_1615__boxed_5914_; uint8_t v_res_5915_; lean_object* v_r_5916_; 
v___x_1615__boxed_5914_ = lean_unbox(v___x_5911_);
v_res_5915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_1615__boxed_5914_, v_e_5912_, v_e_x27_5913_);
v_r_5916_ = lean_box(v_res_5915_);
return v_r_5916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(lean_object* v_n_5917_, lean_object* v_as_5918_, lean_object* v_lo_5919_, lean_object* v_hi_5920_){
_start:
{
lean_object* v___y_5922_; uint8_t v___x_5932_; 
v___x_5932_ = lean_nat_dec_lt(v_lo_5919_, v_hi_5920_);
if (v___x_5932_ == 0)
{
lean_dec(v_lo_5919_);
return v_as_5918_;
}
else
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v_mid_5935_; lean_object* v___y_5937_; lean_object* v___y_5943_; lean_object* v___x_5948_; lean_object* v___x_5949_; uint8_t v___x_5950_; 
v___x_5933_ = lean_nat_add(v_lo_5919_, v_hi_5920_);
v___x_5934_ = lean_unsigned_to_nat(1u);
v_mid_5935_ = lean_nat_shiftr(v___x_5933_, v___x_5934_);
lean_dec(v___x_5933_);
v___x_5948_ = lean_array_fget_borrowed(v_as_5918_, v_mid_5935_);
v___x_5949_ = lean_array_fget_borrowed(v_as_5918_, v_lo_5919_);
lean_inc(v___x_5949_);
lean_inc(v___x_5948_);
v___x_5950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5932_, v___x_5948_, v___x_5949_);
if (v___x_5950_ == 0)
{
v___y_5943_ = v_as_5918_;
goto v___jp_5942_;
}
else
{
lean_object* v___x_5951_; 
v___x_5951_ = lean_array_fswap(v_as_5918_, v_lo_5919_, v_mid_5935_);
v___y_5943_ = v___x_5951_;
goto v___jp_5942_;
}
v___jp_5936_:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; uint8_t v___x_5940_; 
v___x_5938_ = lean_array_fget_borrowed(v___y_5937_, v_mid_5935_);
v___x_5939_ = lean_array_fget_borrowed(v___y_5937_, v_hi_5920_);
lean_inc(v___x_5939_);
lean_inc(v___x_5938_);
v___x_5940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5932_, v___x_5938_, v___x_5939_);
if (v___x_5940_ == 0)
{
lean_dec(v_mid_5935_);
v___y_5922_ = v___y_5937_;
goto v___jp_5921_;
}
else
{
lean_object* v___x_5941_; 
v___x_5941_ = lean_array_fswap(v___y_5937_, v_mid_5935_, v_hi_5920_);
lean_dec(v_mid_5935_);
v___y_5922_ = v___x_5941_;
goto v___jp_5921_;
}
}
v___jp_5942_:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; uint8_t v___x_5946_; 
v___x_5944_ = lean_array_fget_borrowed(v___y_5943_, v_hi_5920_);
v___x_5945_ = lean_array_fget_borrowed(v___y_5943_, v_lo_5919_);
lean_inc(v___x_5945_);
lean_inc(v___x_5944_);
v___x_5946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___lam__0(v___x_5932_, v___x_5944_, v___x_5945_);
if (v___x_5946_ == 0)
{
v___y_5937_ = v___y_5943_;
goto v___jp_5936_;
}
else
{
lean_object* v___x_5947_; 
v___x_5947_ = lean_array_fswap(v___y_5943_, v_lo_5919_, v_hi_5920_);
v___y_5937_ = v___x_5947_;
goto v___jp_5936_;
}
}
}
v___jp_5921_:
{
lean_object* v_pivot_5923_; lean_object* v___x_5924_; lean_object* v_fst_5925_; lean_object* v_snd_5926_; uint8_t v___x_5927_; 
v_pivot_5923_ = lean_array_fget(v___y_5922_, v_hi_5920_);
lean_inc_n(v_lo_5919_, 2);
v___x_5924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_5920_, v_pivot_5923_, v___y_5922_, v_lo_5919_, v_lo_5919_);
v_fst_5925_ = lean_ctor_get(v___x_5924_, 0);
lean_inc(v_fst_5925_);
v_snd_5926_ = lean_ctor_get(v___x_5924_, 1);
lean_inc(v_snd_5926_);
lean_dec_ref(v___x_5924_);
v___x_5927_ = lean_nat_dec_le(v_hi_5920_, v_fst_5925_);
if (v___x_5927_ == 0)
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; 
v___x_5928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5917_, v_snd_5926_, v_lo_5919_, v_fst_5925_);
v___x_5929_ = lean_unsigned_to_nat(1u);
v___x_5930_ = lean_nat_add(v_fst_5925_, v___x_5929_);
lean_dec(v_fst_5925_);
v_as_5918_ = v___x_5928_;
v_lo_5919_ = v___x_5930_;
goto _start;
}
else
{
lean_dec(v_fst_5925_);
lean_dec(v_lo_5919_);
return v_snd_5926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg___boxed(lean_object* v_n_5952_, lean_object* v_as_5953_, lean_object* v_lo_5954_, lean_object* v_hi_5955_){
_start:
{
lean_object* v_res_5956_; 
v_res_5956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_5952_, v_as_5953_, v_lo_5954_, v_hi_5955_);
lean_dec(v_hi_5955_);
lean_dec(v_n_5952_);
return v_res_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(lean_object* v___y_5959_){
_start:
{
lean_object* v___x_5961_; lean_object* v_env_5962_; lean_object* v___x_5963_; lean_object* v_toEnvExtension_5964_; lean_object* v_asyncMode_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___y_5974_; lean_object* v___y_5975_; uint8_t v___x_5978_; 
v___x_5961_ = lean_st_ref_get(v___y_5959_);
v_env_5962_ = lean_ctor_get(v___x_5961_, 0);
lean_inc_ref(v_env_5962_);
lean_dec(v___x_5961_);
v___x_5963_ = l_Lean_errorExplanationExt;
v_toEnvExtension_5964_ = lean_ctor_get(v___x_5963_, 0);
v_asyncMode_5965_ = lean_ctor_get(v_toEnvExtension_5964_, 2);
v___x_5966_ = lean_box(1);
v___x_5967_ = lean_box(0);
v___x_5968_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5966_, v___x_5963_, v_env_5962_, v_asyncMode_5965_, v___x_5967_);
v___x_5969_ = lean_unsigned_to_nat(0u);
v___x_5970_ = ((lean_object*)(l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___closed__0));
v___x_5971_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v___x_5970_, v___x_5968_);
lean_dec(v___x_5968_);
v___x_5972_ = lean_array_get_size(v___x_5971_);
v___x_5978_ = lean_nat_dec_eq(v___x_5972_, v___x_5969_);
if (v___x_5978_ == 0)
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___y_5982_; uint8_t v___x_5984_; 
v___x_5979_ = lean_unsigned_to_nat(1u);
v___x_5980_ = lean_nat_sub(v___x_5972_, v___x_5979_);
v___x_5984_ = lean_nat_dec_le(v___x_5969_, v___x_5980_);
if (v___x_5984_ == 0)
{
lean_inc(v___x_5980_);
v___y_5982_ = v___x_5980_;
goto v___jp_5981_;
}
else
{
v___y_5982_ = v___x_5969_;
goto v___jp_5981_;
}
v___jp_5981_:
{
uint8_t v___x_5983_; 
v___x_5983_ = lean_nat_dec_le(v___y_5982_, v___x_5980_);
if (v___x_5983_ == 0)
{
lean_dec(v___x_5980_);
lean_inc(v___y_5982_);
v___y_5974_ = v___y_5982_;
v___y_5975_ = v___y_5982_;
goto v___jp_5973_;
}
else
{
v___y_5974_ = v___y_5982_;
v___y_5975_ = v___x_5980_;
goto v___jp_5973_;
}
}
}
else
{
lean_object* v___x_5985_; 
v___x_5985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5971_);
return v___x_5985_;
}
v___jp_5973_:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v___x_5972_, v___x_5971_, v___y_5974_, v___y_5975_);
lean_dec(v___y_5975_);
v___x_5977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
return v___x_5977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg___boxed(lean_object* v___y_5986_, lean_object* v___y_5987_){
_start:
{
lean_object* v_res_5988_; 
v_res_5988_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_5986_);
lean_dec(v___y_5986_);
return v_res_5988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(lean_object* v_mkItem_5989_, lean_object* v_stx_5990_, lean_object* v_ctx_5991_, uint8_t v_snd_5992_, lean_object* v_fst_5993_, lean_object* v_caps_5994_, lean_object* v_as_5995_, size_t v_sz_5996_, size_t v_i_5997_, lean_object* v_b_5998_){
_start:
{
lean_object* v_a_6000_; uint8_t v___x_6004_; 
v___x_6004_ = lean_usize_dec_lt(v_i_5997_, v_sz_5996_);
if (v___x_6004_ == 0)
{
lean_dec_ref(v_ctx_5991_);
lean_dec_ref(v_mkItem_5989_);
return v_b_5998_;
}
else
{
lean_object* v_a_6005_; lean_object* v_fst_6006_; lean_object* v_snd_6007_; lean_object* v___x_6009_; uint8_t v_isShared_6010_; uint8_t v_isSharedCheck_6050_; 
v_a_6005_ = lean_array_uget(v_as_5995_, v_i_5997_);
v_fst_6006_ = lean_ctor_get(v_a_6005_, 0);
v_snd_6007_ = lean_ctor_get(v_a_6005_, 1);
v_isSharedCheck_6050_ = !lean_is_exclusive(v_a_6005_);
if (v_isSharedCheck_6050_ == 0)
{
v___x_6009_ = v_a_6005_;
v_isShared_6010_ = v_isSharedCheck_6050_;
goto v_resetjp_6008_;
}
else
{
lean_inc(v_snd_6007_);
lean_inc(v_fst_6006_);
lean_dec(v_a_6005_);
v___x_6009_ = lean_box(0);
v_isShared_6010_ = v_isSharedCheck_6050_;
goto v_resetjp_6008_;
}
v_resetjp_6008_:
{
lean_object* v___y_6012_; lean_object* v___x_6015_; lean_object* v___y_6017_; lean_object* v___y_6018_; uint8_t v___y_6029_; uint8_t v___x_6039_; 
lean_inc(v_fst_6006_);
v___x_6015_ = l_Lean_Name_toString(v_fst_6006_, v___x_6004_);
v___x_6039_ = l_Lean_String_charactersIn(v_fst_5993_, v___x_6015_);
if (v___x_6039_ == 0)
{
lean_dec_ref(v___x_6015_);
lean_del_object(v___x_6009_);
lean_dec(v_snd_6007_);
lean_dec(v_fst_6006_);
v_a_6000_ = v_b_5998_;
goto v___jp_5999_;
}
else
{
lean_object* v_textDocument_x3f_6042_; 
v_textDocument_x3f_6042_ = lean_ctor_get(v_caps_5994_, 0);
if (lean_obj_tag(v_textDocument_x3f_6042_) == 0)
{
goto v___jp_6040_;
}
else
{
lean_object* v_val_6043_; lean_object* v_completion_x3f_6044_; 
v_val_6043_ = lean_ctor_get(v_textDocument_x3f_6042_, 0);
v_completion_x3f_6044_ = lean_ctor_get(v_val_6043_, 0);
if (lean_obj_tag(v_completion_x3f_6044_) == 0)
{
goto v___jp_6040_;
}
else
{
lean_object* v_val_6045_; 
v_val_6045_ = lean_ctor_get(v_completion_x3f_6044_, 0);
if (lean_obj_tag(v_val_6045_) == 0)
{
goto v___jp_6040_;
}
else
{
lean_object* v_val_6046_; 
v_val_6046_ = lean_ctor_get(v_val_6045_, 0);
if (lean_obj_tag(v_val_6046_) == 0)
{
goto v___jp_6040_;
}
else
{
lean_object* v_val_6047_; uint8_t v___x_6048_; 
v_val_6047_ = lean_ctor_get(v_val_6046_, 0);
v___x_6048_ = lean_unbox(v_val_6047_);
if (v___x_6048_ == 0)
{
goto v___jp_6040_;
}
else
{
uint8_t v___x_6049_; 
v___x_6049_ = 0;
v___y_6029_ = v___x_6049_;
goto v___jp_6028_;
}
}
}
}
}
}
v___jp_6011_:
{
lean_object* v___x_6013_; lean_object* v_items_6014_; 
lean_inc_ref(v_mkItem_5989_);
v___x_6013_ = lean_apply_3(v_mkItem_5989_, v_fst_6006_, v_snd_6007_, v___y_6012_);
v_items_6014_ = lean_array_push(v_b_5998_, v___x_6013_);
v_a_6000_ = v_items_6014_;
goto v___jp_5999_;
}
v___jp_6016_:
{
lean_object* v_toCommandContextInfo_6019_; lean_object* v_fileMap_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v_range_6024_; 
v_toCommandContextInfo_6019_ = lean_ctor_get(v_ctx_5991_, 0);
v_fileMap_6020_ = lean_ctor_get(v_toCommandContextInfo_6019_, 2);
lean_inc_ref_n(v_fileMap_6020_, 2);
v___x_6021_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6020_, v___y_6017_);
lean_dec(v___y_6017_);
v___x_6022_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_6020_, v___y_6018_);
lean_dec(v___y_6018_);
if (v_isShared_6010_ == 0)
{
lean_ctor_set(v___x_6009_, 1, v___x_6022_);
lean_ctor_set(v___x_6009_, 0, v___x_6021_);
v_range_6024_ = v___x_6009_;
goto v_reusejp_6023_;
}
else
{
lean_object* v_reuseFailAlloc_6027_; 
v_reuseFailAlloc_6027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6027_, 0, v___x_6021_);
lean_ctor_set(v_reuseFailAlloc_6027_, 1, v___x_6022_);
v_range_6024_ = v_reuseFailAlloc_6027_;
goto v_reusejp_6023_;
}
v_reusejp_6023_:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; 
lean_inc_ref(v_range_6024_);
v___x_6025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6015_);
lean_ctor_set(v___x_6025_, 1, v_range_6024_);
lean_ctor_set(v___x_6025_, 2, v_range_6024_);
v___x_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
v___y_6012_ = v___x_6026_;
goto v___jp_6011_;
}
}
v___jp_6028_:
{
lean_object* v___x_6030_; 
v___x_6030_ = l_Lean_Syntax_getRange_x3f(v_stx_5990_, v___y_6029_);
if (lean_obj_tag(v___x_6030_) == 1)
{
lean_object* v_val_6031_; 
v_val_6031_ = lean_ctor_get(v___x_6030_, 0);
lean_inc(v_val_6031_);
lean_dec_ref_known(v___x_6030_, 1);
if (v_snd_5992_ == 0)
{
lean_object* v_start_6032_; lean_object* v_stop_6033_; 
v_start_6032_ = lean_ctor_get(v_val_6031_, 0);
lean_inc(v_start_6032_);
v_stop_6033_ = lean_ctor_get(v_val_6031_, 1);
lean_inc(v_stop_6033_);
lean_dec(v_val_6031_);
v___y_6017_ = v_start_6032_;
v___y_6018_ = v_stop_6033_;
goto v___jp_6016_;
}
else
{
lean_object* v_start_6034_; lean_object* v_stop_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; 
v_start_6034_ = lean_ctor_get(v_val_6031_, 0);
lean_inc(v_start_6034_);
v_stop_6035_ = lean_ctor_get(v_val_6031_, 1);
lean_inc(v_stop_6035_);
lean_dec(v_val_6031_);
v___x_6036_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0, &l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___lam__0___closed__0);
v___x_6037_ = lean_nat_add(v_stop_6035_, v___x_6036_);
lean_dec(v_stop_6035_);
v___y_6017_ = v_start_6034_;
v___y_6018_ = v___x_6037_;
goto v___jp_6016_;
}
}
else
{
lean_object* v___x_6038_; 
lean_dec(v___x_6030_);
lean_dec_ref(v___x_6015_);
lean_del_object(v___x_6009_);
v___x_6038_ = lean_box(0);
v___y_6012_ = v___x_6038_;
goto v___jp_6011_;
}
}
v___jp_6040_:
{
if (v___x_6039_ == 0)
{
v___y_6029_ = v___x_6039_;
goto v___jp_6028_;
}
else
{
lean_object* v___x_6041_; 
lean_dec_ref(v___x_6015_);
lean_del_object(v___x_6009_);
v___x_6041_ = lean_box(0);
v___y_6012_ = v___x_6041_;
goto v___jp_6011_;
}
}
}
}
v___jp_5999_:
{
size_t v___x_6001_; size_t v___x_6002_; 
v___x_6001_ = ((size_t)1ULL);
v___x_6002_ = lean_usize_add(v_i_5997_, v___x_6001_);
v_i_5997_ = v___x_6002_;
v_b_5998_ = v_a_6000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3___boxed(lean_object* v_mkItem_6051_, lean_object* v_stx_6052_, lean_object* v_ctx_6053_, lean_object* v_snd_6054_, lean_object* v_fst_6055_, lean_object* v_caps_6056_, lean_object* v_as_6057_, lean_object* v_sz_6058_, lean_object* v_i_6059_, lean_object* v_b_6060_){
_start:
{
uint8_t v_snd_1740__boxed_6061_; size_t v_sz_boxed_6062_; size_t v_i_boxed_6063_; lean_object* v_res_6064_; 
v_snd_1740__boxed_6061_ = lean_unbox(v_snd_6054_);
v_sz_boxed_6062_ = lean_unbox_usize(v_sz_6058_);
lean_dec(v_sz_6058_);
v_i_boxed_6063_ = lean_unbox_usize(v_i_6059_);
lean_dec(v_i_6059_);
v_res_6064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6051_, v_stx_6052_, v_ctx_6053_, v_snd_1740__boxed_6061_, v_fst_6055_, v_caps_6056_, v_as_6057_, v_sz_boxed_6062_, v_i_boxed_6063_, v_b_6060_);
lean_dec_ref(v_as_6057_);
lean_dec_ref(v_caps_6056_);
lean_dec_ref(v_fst_6055_);
lean_dec(v_stx_6052_);
return v_res_6064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(lean_object* v_entries_6065_, lean_object* v_stx_6066_, lean_object* v_caps_6067_, lean_object* v_ctx_6068_, lean_object* v_mkItem_6069_){
_start:
{
lean_object* v_fst_6071_; uint8_t v_snd_6072_; uint8_t v___x_6077_; lean_object* v___x_6078_; 
v___x_6077_ = 0;
v___x_6078_ = l_Lean_Syntax_getSubstring_x3f(v_stx_6066_, v___x_6077_, v___x_6077_);
if (lean_obj_tag(v___x_6078_) == 0)
{
lean_object* v___x_6079_; 
v___x_6079_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_fst_6071_ = v___x_6079_;
v_snd_6072_ = v___x_6077_;
goto v___jp_6070_;
}
else
{
lean_object* v_val_6080_; lean_object* v_str_6081_; lean_object* v_startPos_6082_; lean_object* v_stopPos_6083_; uint8_t v___y_6085_; uint8_t v___x_6087_; 
v_val_6080_ = lean_ctor_get(v___x_6078_, 0);
lean_inc(v_val_6080_);
lean_dec_ref_known(v___x_6078_, 1);
v_str_6081_ = lean_ctor_get(v_val_6080_, 0);
lean_inc_ref(v_str_6081_);
v_startPos_6082_ = lean_ctor_get(v_val_6080_, 1);
lean_inc(v_startPos_6082_);
v_stopPos_6083_ = lean_ctor_get(v_val_6080_, 2);
lean_inc(v_stopPos_6083_);
lean_dec(v_val_6080_);
v___x_6087_ = lean_string_utf8_at_end(v_str_6081_, v_stopPos_6083_);
if (v___x_6087_ == 0)
{
uint32_t v___x_6088_; uint32_t v___x_6089_; uint8_t v___x_6090_; 
v___x_6088_ = lean_string_utf8_get(v_str_6081_, v_stopPos_6083_);
v___x_6089_ = 46;
v___x_6090_ = lean_uint32_dec_eq(v___x_6088_, v___x_6089_);
if (v___x_6090_ == 0)
{
v___y_6085_ = v___x_6090_;
goto v___jp_6084_;
}
else
{
lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6091_ = lean_string_utf8_extract(v_str_6081_, v_startPos_6082_, v_stopPos_6083_);
lean_dec(v_stopPos_6083_);
lean_dec(v_startPos_6082_);
lean_dec_ref(v_str_6081_);
v___x_6092_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6093_ = lean_string_append(v___x_6091_, v___x_6092_);
v_fst_6071_ = v___x_6093_;
v_snd_6072_ = v___x_6090_;
goto v___jp_6070_;
}
}
else
{
v___y_6085_ = v___x_6077_;
goto v___jp_6084_;
}
v___jp_6084_:
{
lean_object* v___x_6086_; 
v___x_6086_ = lean_string_utf8_extract(v_str_6081_, v_startPos_6082_, v_stopPos_6083_);
lean_dec(v_stopPos_6083_);
lean_dec(v_startPos_6082_);
lean_dec_ref(v_str_6081_);
v_fst_6071_ = v___x_6086_;
v_snd_6072_ = v___y_6085_;
goto v___jp_6070_;
}
}
v___jp_6070_:
{
lean_object* v_items_6073_; size_t v_sz_6074_; size_t v___x_6075_; lean_object* v___x_6076_; 
v_items_6073_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__0));
v_sz_6074_ = lean_array_size(v_entries_6065_);
v___x_6075_ = ((size_t)0ULL);
v___x_6076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1_spec__3(v_mkItem_6069_, v_stx_6066_, v_ctx_6068_, v_snd_6072_, v_fst_6071_, v_caps_6067_, v_entries_6065_, v_sz_6074_, v___x_6075_, v_items_6073_);
lean_dec_ref(v_fst_6071_);
return v___x_6076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1___boxed(lean_object* v_entries_6094_, lean_object* v_stx_6095_, lean_object* v_caps_6096_, lean_object* v_ctx_6097_, lean_object* v_mkItem_6098_){
_start:
{
lean_object* v_res_6099_; 
v_res_6099_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_entries_6094_, v_stx_6095_, v_caps_6096_, v_ctx_6097_, v_mkItem_6098_);
lean_dec_ref(v_caps_6096_);
lean_dec(v_stx_6095_);
lean_dec_ref(v_entries_6094_);
return v_res_6099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1(lean_object* v_partialId_6100_, lean_object* v_caps_6101_, lean_object* v_ctx_6102_, lean_object* v___f_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_){
_start:
{
lean_object* v___x_6109_; lean_object* v_a_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6118_; 
v___x_6109_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6107_);
v_a_6110_ = lean_ctor_get(v___x_6109_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v___x_6109_);
if (v_isSharedCheck_6118_ == 0)
{
v___x_6112_ = v___x_6109_;
v_isShared_6113_ = v_isSharedCheck_6118_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_a_6110_);
lean_dec(v___x_6109_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6118_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6114_; lean_object* v___x_6116_; 
v___x_6114_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___at___00Lean_Server_Completion_errorNameCompletion_spec__1(v_a_6110_, v_partialId_6100_, v_caps_6101_, v_ctx_6102_, v___f_6103_);
lean_dec(v_a_6110_);
if (v_isShared_6113_ == 0)
{
lean_ctor_set(v___x_6112_, 0, v___x_6114_);
v___x_6116_ = v___x_6112_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v___x_6114_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
return v___x_6116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed(lean_object* v_partialId_6119_, lean_object* v_caps_6120_, lean_object* v_ctx_6121_, lean_object* v___f_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v_res_6128_; 
v_res_6128_ = l_Lean_Server_Completion_errorNameCompletion___lam__1(v_partialId_6119_, v_caps_6120_, v_ctx_6121_, v___f_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_);
lean_dec(v___y_6126_);
lean_dec_ref(v___y_6125_);
lean_dec(v___y_6124_);
lean_dec_ref(v___y_6123_);
lean_dec_ref(v_caps_6120_);
lean_dec(v_partialId_6119_);
return v_res_6128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object* v_uri_6129_, lean_object* v_pos_6130_, lean_object* v_completionInfoPos_6131_, lean_object* v_ctx_6132_, lean_object* v_partialId_6133_, lean_object* v_caps_6134_){
_start:
{
lean_object* v___f_6136_; lean_object* v___f_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; 
v___f_6136_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6136_, 0, v_completionInfoPos_6131_);
lean_closure_set(v___f_6136_, 1, v_uri_6129_);
lean_closure_set(v___f_6136_, 2, v_pos_6130_);
lean_inc_ref(v_ctx_6132_);
v___f_6137_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_errorNameCompletion___lam__1___boxed), 9, 4);
lean_closure_set(v___f_6137_, 0, v_partialId_6133_);
lean_closure_set(v___f_6137_, 1, v_caps_6134_);
lean_closure_set(v___f_6137_, 2, v_ctx_6132_);
lean_closure_set(v___f_6137_, 3, v___f_6136_);
v___x_6138_ = lean_unsigned_to_nat(32u);
v___x_6139_ = lean_mk_empty_array_with_capacity(v___x_6138_);
lean_dec_ref(v___x_6139_);
v___x_6140_ = lean_obj_once(&l_Lean_Server_Completion_optionCompletion___closed__4, &l_Lean_Server_Completion_optionCompletion___closed__4_once, _init_l_Lean_Server_Completion_optionCompletion___closed__4);
v___x_6141_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6132_, v___x_6140_, v___f_6137_);
return v___x_6141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_errorNameCompletion___boxed(lean_object* v_uri_6142_, lean_object* v_pos_6143_, lean_object* v_completionInfoPos_6144_, lean_object* v_ctx_6145_, lean_object* v_partialId_6146_, lean_object* v_caps_6147_, lean_object* v_a_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_6142_, v_pos_6143_, v_completionInfoPos_6144_, v_ctx_6145_, v_partialId_6146_, v_caps_6147_);
return v_res_6149_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_){
_start:
{
lean_object* v___x_6155_; 
v___x_6155_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___redArg(v___y_6153_);
return v___x_6155_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0___boxed(lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_){
_start:
{
lean_object* v_res_6161_; 
v_res_6161_ = l_Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0(v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec(v___y_6157_);
lean_dec_ref(v___y_6156_);
return v_res_6161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(lean_object* v_init_6162_, lean_object* v_t_6163_){
_start:
{
lean_object* v___x_6164_; 
v___x_6164_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0_spec__1(v_init_6162_, v_t_6163_);
return v___x_6164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0___boxed(lean_object* v_init_6165_, lean_object* v_t_6166_){
_start:
{
lean_object* v_res_6167_; 
v_res_6167_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__0(v_init_6165_, v_t_6166_);
lean_dec(v_t_6166_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(lean_object* v_n_6168_, lean_object* v_as_6169_, lean_object* v_lo_6170_, lean_object* v_hi_6171_, lean_object* v_w_6172_, lean_object* v_hlo_6173_, lean_object* v_hhi_6174_){
_start:
{
lean_object* v___x_6175_; 
v___x_6175_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___redArg(v_n_6168_, v_as_6169_, v_lo_6170_, v_hi_6171_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1___boxed(lean_object* v_n_6176_, lean_object* v_as_6177_, lean_object* v_lo_6178_, lean_object* v_hi_6179_, lean_object* v_w_6180_, lean_object* v_hlo_6181_, lean_object* v_hhi_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1(v_n_6176_, v_as_6177_, v_lo_6178_, v_hi_6179_, v_w_6180_, v_hlo_6181_, v_hhi_6182_);
lean_dec(v_hi_6179_);
lean_dec(v_n_6176_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(lean_object* v_n_6184_, lean_object* v_lo_6185_, lean_object* v_hi_6186_, lean_object* v_hhi_6187_, lean_object* v_pivot_6188_, lean_object* v_as_6189_, lean_object* v_i_6190_, lean_object* v_k_6191_, lean_object* v_ilo_6192_, lean_object* v_ik_6193_, lean_object* v_w_6194_){
_start:
{
lean_object* v___x_6195_; 
v___x_6195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___redArg(v_hi_6186_, v_pivot_6188_, v_as_6189_, v_i_6190_, v_k_6191_);
return v___x_6195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3___boxed(lean_object* v_n_6196_, lean_object* v_lo_6197_, lean_object* v_hi_6198_, lean_object* v_hhi_6199_, lean_object* v_pivot_6200_, lean_object* v_as_6201_, lean_object* v_i_6202_, lean_object* v_k_6203_, lean_object* v_ilo_6204_, lean_object* v_ik_6205_, lean_object* v_w_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanations___at___00Lean_Server_Completion_errorNameCompletion_spec__0_spec__1_spec__3(v_n_6196_, v_lo_6197_, v_hi_6198_, v_hhi_6199_, v_pivot_6200_, v_as_6201_, v_i_6202_, v_k_6203_, v_ilo_6204_, v_ik_6205_, v_w_6206_);
lean_dec(v_hi_6198_);
lean_dec(v_lo_6197_);
lean_dec(v_n_6196_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(lean_object* v_completionInfoPos_6208_, lean_object* v_uri_6209_, lean_object* v_pos_6210_, size_t v_sz_6211_, size_t v_i_6212_, lean_object* v_bs_6213_){
_start:
{
uint8_t v___x_6214_; 
v___x_6214_ = lean_usize_dec_lt(v_i_6212_, v_sz_6211_);
if (v___x_6214_ == 0)
{
lean_dec_ref(v_pos_6210_);
lean_dec_ref(v_uri_6209_);
lean_dec(v_completionInfoPos_6208_);
return v_bs_6213_;
}
else
{
lean_object* v_v_6215_; lean_object* v_userName_6216_; lean_object* v_docString_6217_; lean_object* v___x_6218_; lean_object* v_bs_x27_6219_; lean_object* v___x_6220_; lean_object* v___y_6222_; 
v_v_6215_ = lean_array_uget_borrowed(v_bs_6213_, v_i_6212_);
v_userName_6216_ = lean_ctor_get(v_v_6215_, 1);
lean_inc_ref(v_userName_6216_);
v_docString_6217_ = lean_ctor_get(v_v_6215_, 3);
lean_inc(v_docString_6217_);
v___x_6218_ = lean_unsigned_to_nat(0u);
v_bs_x27_6219_ = lean_array_uset(v_bs_6213_, v_i_6212_, v___x_6218_);
v___x_6220_ = lean_box(0);
if (lean_obj_tag(v_docString_6217_) == 0)
{
v___y_6222_ = v___x_6220_;
goto v___jp_6221_;
}
else
{
lean_object* v_val_6232_; lean_object* v___x_6234_; uint8_t v_isShared_6235_; uint8_t v_isSharedCheck_6241_; 
v_val_6232_ = lean_ctor_get(v_docString_6217_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v_docString_6217_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6234_ = v_docString_6217_;
v_isShared_6235_ = v_isSharedCheck_6241_;
goto v_resetjp_6233_;
}
else
{
lean_inc(v_val_6232_);
lean_dec(v_docString_6217_);
v___x_6234_ = lean_box(0);
v_isShared_6235_ = v_isSharedCheck_6241_;
goto v_resetjp_6233_;
}
v_resetjp_6233_:
{
uint8_t v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6239_; 
v___x_6236_ = 1;
v___x_6237_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6237_, 0, v_val_6232_);
lean_ctor_set_uint8(v___x_6237_, sizeof(void*)*1, v___x_6236_);
if (v_isShared_6235_ == 0)
{
lean_ctor_set(v___x_6234_, 0, v___x_6237_);
v___x_6239_ = v___x_6234_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v___x_6237_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
v___y_6222_ = v___x_6239_;
goto v___jp_6221_;
}
}
}
v___jp_6221_:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; size_t v___x_6228_; size_t v___x_6229_; lean_object* v___x_6230_; 
v___x_6223_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6208_);
v___x_6224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6224_, 0, v_completionInfoPos_6208_);
lean_inc_ref(v_pos_6210_);
lean_inc_ref(v_uri_6209_);
v___x_6225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6225_, 0, v_uri_6209_);
lean_ctor_set(v___x_6225_, 1, v_pos_6210_);
lean_ctor_set(v___x_6225_, 2, v___x_6224_);
lean_ctor_set(v___x_6225_, 3, v___x_6220_);
v___x_6226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6225_);
v___x_6227_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6227_, 0, v_userName_6216_);
lean_ctor_set(v___x_6227_, 1, v___x_6220_);
lean_ctor_set(v___x_6227_, 2, v___y_6222_);
lean_ctor_set(v___x_6227_, 3, v___x_6223_);
lean_ctor_set(v___x_6227_, 4, v___x_6220_);
lean_ctor_set(v___x_6227_, 5, v___x_6220_);
lean_ctor_set(v___x_6227_, 6, v___x_6226_);
lean_ctor_set(v___x_6227_, 7, v___x_6220_);
v___x_6228_ = ((size_t)1ULL);
v___x_6229_ = lean_usize_add(v_i_6212_, v___x_6228_);
v___x_6230_ = lean_array_uset(v_bs_x27_6219_, v_i_6212_, v___x_6227_);
v_i_6212_ = v___x_6229_;
v_bs_6213_ = v___x_6230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6242_, lean_object* v_uri_6243_, lean_object* v_pos_6244_, lean_object* v_sz_6245_, lean_object* v_i_6246_, lean_object* v_bs_6247_){
_start:
{
size_t v_sz_boxed_6248_; size_t v_i_boxed_6249_; lean_object* v_res_6250_; 
v_sz_boxed_6248_ = lean_unbox_usize(v_sz_6245_);
lean_dec(v_sz_6245_);
v_i_boxed_6249_ = lean_unbox_usize(v_i_6246_);
lean_dec(v_i_6246_);
v_res_6250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6242_, v_uri_6243_, v_pos_6244_, v_sz_boxed_6248_, v_i_boxed_6249_, v_bs_6247_);
return v_res_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0(uint8_t v___x_6251_, lean_object* v_completionInfoPos_6252_, lean_object* v_uri_6253_, lean_object* v_pos_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_){
_start:
{
lean_object* v___x_6260_; 
v___x_6260_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v___x_6251_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_);
if (lean_obj_tag(v___x_6260_) == 0)
{
lean_object* v_a_6261_; lean_object* v___x_6263_; uint8_t v_isShared_6264_; uint8_t v_isSharedCheck_6271_; 
v_a_6261_ = lean_ctor_get(v___x_6260_, 0);
v_isSharedCheck_6271_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6271_ == 0)
{
v___x_6263_ = v___x_6260_;
v_isShared_6264_ = v_isSharedCheck_6271_;
goto v_resetjp_6262_;
}
else
{
lean_inc(v_a_6261_);
lean_dec(v___x_6260_);
v___x_6263_ = lean_box(0);
v_isShared_6264_ = v_isSharedCheck_6271_;
goto v_resetjp_6262_;
}
v_resetjp_6262_:
{
size_t v_sz_6265_; size_t v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6269_; 
v_sz_6265_ = lean_array_size(v_a_6261_);
v___x_6266_ = ((size_t)0ULL);
v___x_6267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_tacticCompletion_spec__0(v_completionInfoPos_6252_, v_uri_6253_, v_pos_6254_, v_sz_6265_, v___x_6266_, v_a_6261_);
if (v_isShared_6264_ == 0)
{
lean_ctor_set(v___x_6263_, 0, v___x_6267_);
v___x_6269_ = v___x_6263_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v___x_6267_);
v___x_6269_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
return v___x_6269_;
}
}
}
else
{
lean_object* v_a_6272_; lean_object* v___x_6274_; uint8_t v_isShared_6275_; uint8_t v_isSharedCheck_6279_; 
lean_dec_ref(v_pos_6254_);
lean_dec_ref(v_uri_6253_);
lean_dec(v_completionInfoPos_6252_);
v_a_6272_ = lean_ctor_get(v___x_6260_, 0);
v_isSharedCheck_6279_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6279_ == 0)
{
v___x_6274_ = v___x_6260_;
v_isShared_6275_ = v_isSharedCheck_6279_;
goto v_resetjp_6273_;
}
else
{
lean_inc(v_a_6272_);
lean_dec(v___x_6260_);
v___x_6274_ = lean_box(0);
v_isShared_6275_ = v_isSharedCheck_6279_;
goto v_resetjp_6273_;
}
v_resetjp_6273_:
{
lean_object* v___x_6277_; 
if (v_isShared_6275_ == 0)
{
v___x_6277_ = v___x_6274_;
goto v_reusejp_6276_;
}
else
{
lean_object* v_reuseFailAlloc_6278_; 
v_reuseFailAlloc_6278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6278_, 0, v_a_6272_);
v___x_6277_ = v_reuseFailAlloc_6278_;
goto v_reusejp_6276_;
}
v_reusejp_6276_:
{
return v___x_6277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lam__0___boxed(lean_object* v___x_6280_, lean_object* v_completionInfoPos_6281_, lean_object* v_uri_6282_, lean_object* v_pos_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
uint8_t v___x_493__boxed_6289_; lean_object* v_res_6290_; 
v___x_493__boxed_6289_ = lean_unbox(v___x_6280_);
v_res_6290_ = l_Lean_Server_Completion_tacticCompletion___lam__0(v___x_493__boxed_6289_, v_completionInfoPos_6281_, v_uri_6282_, v_pos_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* v_uri_6291_, lean_object* v_pos_6292_, lean_object* v_completionInfoPos_6293_, lean_object* v_ctx_6294_){
_start:
{
lean_object* v___x_6296_; uint8_t v___x_6297_; lean_object* v___x_6298_; lean_object* v___f_6299_; lean_object* v___x_6300_; 
v___x_6296_ = l_Lean_LocalContext_empty;
v___x_6297_ = 0;
v___x_6298_ = lean_box(v___x_6297_);
v___f_6299_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6299_, 0, v___x_6298_);
lean_closure_set(v___f_6299_, 1, v_completionInfoPos_6293_);
lean_closure_set(v___f_6299_, 2, v_uri_6291_);
lean_closure_set(v___f_6299_, 3, v_pos_6292_);
v___x_6300_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6294_, v___x_6296_, v___f_6299_);
return v___x_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___boxed(lean_object* v_uri_6301_, lean_object* v_pos_6302_, lean_object* v_completionInfoPos_6303_, lean_object* v_ctx_6304_, lean_object* v_a_6305_){
_start:
{
lean_object* v_res_6306_; 
v_res_6306_ = l_Lean_Server_Completion_tacticCompletion(v_uri_6301_, v_pos_6302_, v_completionInfoPos_6303_, v_ctx_6304_);
return v_res_6306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(lean_object* v_a_6307_, lean_object* v_b_6308_){
_start:
{
lean_object* v_array_6309_; lean_object* v_start_6310_; lean_object* v_stop_6311_; lean_object* v___x_6313_; uint8_t v_isShared_6314_; uint8_t v_isSharedCheck_6324_; 
v_array_6309_ = lean_ctor_get(v_a_6307_, 0);
v_start_6310_ = lean_ctor_get(v_a_6307_, 1);
v_stop_6311_ = lean_ctor_get(v_a_6307_, 2);
v_isSharedCheck_6324_ = !lean_is_exclusive(v_a_6307_);
if (v_isSharedCheck_6324_ == 0)
{
v___x_6313_ = v_a_6307_;
v_isShared_6314_ = v_isSharedCheck_6324_;
goto v_resetjp_6312_;
}
else
{
lean_inc(v_stop_6311_);
lean_inc(v_start_6310_);
lean_inc(v_array_6309_);
lean_dec(v_a_6307_);
v___x_6313_ = lean_box(0);
v_isShared_6314_ = v_isSharedCheck_6324_;
goto v_resetjp_6312_;
}
v_resetjp_6312_:
{
uint8_t v___x_6315_; 
v___x_6315_ = lean_nat_dec_lt(v_start_6310_, v_stop_6311_);
if (v___x_6315_ == 0)
{
lean_del_object(v___x_6313_);
lean_dec(v_stop_6311_);
lean_dec(v_start_6310_);
lean_dec_ref(v_array_6309_);
return v_b_6308_;
}
else
{
lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6319_; 
v___x_6316_ = lean_unsigned_to_nat(1u);
v___x_6317_ = lean_nat_add(v_start_6310_, v___x_6316_);
lean_inc_ref(v_array_6309_);
if (v_isShared_6314_ == 0)
{
lean_ctor_set(v___x_6313_, 1, v___x_6317_);
v___x_6319_ = v___x_6313_;
goto v_reusejp_6318_;
}
else
{
lean_object* v_reuseFailAlloc_6323_; 
v_reuseFailAlloc_6323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6323_, 0, v_array_6309_);
lean_ctor_set(v_reuseFailAlloc_6323_, 1, v___x_6317_);
lean_ctor_set(v_reuseFailAlloc_6323_, 2, v_stop_6311_);
v___x_6319_ = v_reuseFailAlloc_6323_;
goto v_reusejp_6318_;
}
v_reusejp_6318_:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6320_ = lean_array_fget(v_array_6309_, v_start_6310_);
lean_dec(v_start_6310_);
lean_dec_ref(v_array_6309_);
v___x_6321_ = lean_array_push(v_b_6308_, v___x_6320_);
v_a_6307_ = v___x_6319_;
v_b_6308_ = v___x_6321_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(lean_object* v_scopeNames_6327_, lean_object* v_idx_6328_){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6329_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_trailingDotCompletion___redArg___closed__0));
v___x_6330_ = lean_array_get_size(v_scopeNames_6327_);
v___x_6331_ = l_Array_toSubarray___redArg(v_scopeNames_6327_, v_idx_6328_, v___x_6330_);
v___x_6332_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6333_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v___x_6331_, v___x_6332_);
v___x_6334_ = lean_array_to_list(v___x_6333_);
v___x_6335_ = l_String_intercalate(v___x_6329_, v___x_6334_);
return v___x_6335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0(lean_object* v_inst_6336_, lean_object* v_R_6337_, lean_object* v_a_6338_, lean_object* v_b_6339_){
_start:
{
lean_object* v___x_6340_; 
v___x_6340_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate_spec__0___redArg(v_a_6338_, v_b_6339_);
return v___x_6340_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(lean_object* v_upperBound_6341_, lean_object* v_next_6342_, lean_object* v_scopeNames_6343_, lean_object* v_idComponents_6344_, lean_object* v_a_6345_, uint8_t v_b_6346_){
_start:
{
uint8_t v___x_6347_; 
v___x_6347_ = lean_nat_dec_lt(v_a_6345_, v_upperBound_6341_);
if (v___x_6347_ == 0)
{
lean_dec(v_a_6345_);
return v_b_6346_;
}
else
{
uint8_t v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; uint8_t v___x_6351_; 
v___x_6348_ = 0;
v___x_6349_ = lean_nat_add(v_next_6342_, v_a_6345_);
v___x_6350_ = lean_array_get_size(v_scopeNames_6343_);
v___x_6351_ = lean_nat_dec_lt(v___x_6349_, v___x_6350_);
if (v___x_6351_ == 0)
{
lean_dec(v___x_6349_);
lean_dec(v_a_6345_);
return v___x_6348_;
}
else
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; uint8_t v___x_6355_; 
v___x_6352_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v___x_6353_ = lean_array_fget_borrowed(v_scopeNames_6343_, v___x_6349_);
lean_dec(v___x_6349_);
v___x_6354_ = lean_array_get_borrowed(v___x_6352_, v_idComponents_6344_, v_a_6345_);
v___x_6355_ = lean_string_dec_eq(v___x_6354_, v___x_6353_);
if (v___x_6355_ == 0)
{
lean_dec(v_a_6345_);
return v___x_6348_;
}
else
{
lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6356_ = lean_unsigned_to_nat(1u);
v___x_6357_ = lean_nat_add(v_a_6345_, v___x_6356_);
lean_dec(v_a_6345_);
v_a_6345_ = v___x_6357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg___boxed(lean_object* v_upperBound_6359_, lean_object* v_next_6360_, lean_object* v_scopeNames_6361_, lean_object* v_idComponents_6362_, lean_object* v_a_6363_, lean_object* v_b_6364_){
_start:
{
uint8_t v_b_boxed_6365_; uint8_t v_res_6366_; lean_object* v_r_6367_; 
v_b_boxed_6365_ = lean_unbox(v_b_6364_);
v_res_6366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6359_, v_next_6360_, v_scopeNames_6361_, v_idComponents_6362_, v_a_6363_, v_b_boxed_6365_);
lean_dec_ref(v_idComponents_6362_);
lean_dec_ref(v_scopeNames_6361_);
lean_dec(v_next_6360_);
lean_dec(v_upperBound_6359_);
v_r_6367_ = lean_box(v_res_6366_);
return v_r_6367_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(lean_object* v_upperBound_6368_, lean_object* v_idComponents_6369_, lean_object* v_scopeNames_6370_, lean_object* v_a_6371_, lean_object* v_b_6372_){
_start:
{
lean_object* v_a_6374_; uint8_t v___x_6378_; 
v___x_6378_ = lean_nat_dec_lt(v_a_6371_, v_upperBound_6368_);
if (v___x_6378_ == 0)
{
lean_dec(v_a_6371_);
lean_dec_ref(v_scopeNames_6370_);
return v_b_6372_;
}
else
{
lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; uint8_t v___x_6382_; 
v___x_6379_ = lean_array_get_size(v_idComponents_6369_);
v___x_6380_ = lean_unsigned_to_nat(1u);
v___x_6381_ = lean_nat_sub(v___x_6379_, v___x_6380_);
v___x_6382_ = lean_nat_dec_lt(v___x_6381_, v___x_6379_);
if (v___x_6382_ == 0)
{
lean_object* v___x_6383_; lean_object* v___x_6384_; 
lean_dec(v___x_6381_);
lean_inc(v_a_6371_);
lean_inc_ref(v_scopeNames_6370_);
v___x_6383_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6370_, v_a_6371_);
v___x_6384_ = lean_array_push(v_b_6372_, v___x_6383_);
v_a_6374_ = v___x_6384_;
goto v___jp_6373_;
}
else
{
lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; uint8_t v___x_6388_; 
v___x_6385_ = lean_nat_add(v_a_6371_, v___x_6379_);
v___x_6386_ = lean_nat_sub(v___x_6385_, v___x_6380_);
lean_dec(v___x_6385_);
v___x_6387_ = lean_array_get_size(v_scopeNames_6370_);
v___x_6388_ = lean_nat_dec_lt(v___x_6386_, v___x_6387_);
if (v___x_6388_ == 0)
{
lean_dec(v___x_6386_);
lean_dec(v___x_6381_);
v_a_6374_ = v_b_6372_;
goto v___jp_6373_;
}
else
{
lean_object* v___x_6389_; lean_object* v___x_6390_; uint8_t v___x_6391_; 
v___x_6389_ = lean_array_fget_borrowed(v_idComponents_6369_, v___x_6381_);
v___x_6390_ = lean_array_fget_borrowed(v_scopeNames_6370_, v___x_6386_);
v___x_6391_ = l_Lean_String_charactersIn(v___x_6389_, v___x_6390_);
if (v___x_6391_ == 0)
{
lean_dec(v___x_6386_);
lean_dec(v___x_6381_);
v_a_6374_ = v_b_6372_;
goto v___jp_6373_;
}
else
{
lean_object* v___x_6392_; uint8_t v___x_6393_; 
v___x_6392_ = lean_unsigned_to_nat(0u);
v___x_6393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v___x_6381_, v_a_6371_, v_scopeNames_6370_, v_idComponents_6369_, v___x_6392_, v___x_6378_);
lean_dec(v___x_6381_);
if (v___x_6393_ == 0)
{
lean_dec(v___x_6386_);
v_a_6374_ = v_b_6372_;
goto v___jp_6373_;
}
else
{
lean_object* v___x_6394_; lean_object* v___x_6395_; 
lean_inc_ref(v_scopeNames_6370_);
v___x_6394_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate(v_scopeNames_6370_, v___x_6386_);
v___x_6395_ = lean_array_push(v_b_6372_, v___x_6394_);
v_a_6374_ = v___x_6395_;
goto v___jp_6373_;
}
}
}
}
}
v___jp_6373_:
{
lean_object* v___x_6375_; lean_object* v___x_6376_; 
v___x_6375_ = lean_unsigned_to_nat(1u);
v___x_6376_ = lean_nat_add(v_a_6371_, v___x_6375_);
lean_dec(v_a_6371_);
v_a_6371_ = v___x_6376_;
v_b_6372_ = v_a_6374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg___boxed(lean_object* v_upperBound_6396_, lean_object* v_idComponents_6397_, lean_object* v_scopeNames_6398_, lean_object* v_a_6399_, lean_object* v_b_6400_){
_start:
{
lean_object* v_res_6401_; 
v_res_6401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6396_, v_idComponents_6397_, v_scopeNames_6398_, v_a_6399_, v_b_6400_);
lean_dec_ref(v_idComponents_6397_);
lean_dec(v_upperBound_6396_);
return v_res_6401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(lean_object* v_idComponents_6402_, lean_object* v_scopeNames_6403_){
_start:
{
lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v_r_6406_; lean_object* v___x_6407_; 
v___x_6404_ = lean_unsigned_to_nat(0u);
v___x_6405_ = lean_array_get_size(v_scopeNames_6403_);
v_r_6406_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___x_6407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v___x_6405_, v_idComponents_6402_, v_scopeNames_6403_, v___x_6404_, v_r_6406_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates___boxed(lean_object* v_idComponents_6408_, lean_object* v_scopeNames_6409_){
_start:
{
lean_object* v_res_6410_; 
v_res_6410_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6408_, v_scopeNames_6409_);
lean_dec_ref(v_idComponents_6408_);
return v_res_6410_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(lean_object* v_upperBound_6411_, lean_object* v_next_6412_, lean_object* v_scopeNames_6413_, lean_object* v_idComponents_6414_, lean_object* v_inst_6415_, lean_object* v_R_6416_, lean_object* v_a_6417_, uint8_t v_b_6418_, lean_object* v_c_6419_){
_start:
{
uint8_t v___x_6420_; 
v___x_6420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___redArg(v_upperBound_6411_, v_next_6412_, v_scopeNames_6413_, v_idComponents_6414_, v_a_6417_, v_b_6418_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0___boxed(lean_object* v_upperBound_6421_, lean_object* v_next_6422_, lean_object* v_scopeNames_6423_, lean_object* v_idComponents_6424_, lean_object* v_inst_6425_, lean_object* v_R_6426_, lean_object* v_a_6427_, lean_object* v_b_6428_, lean_object* v_c_6429_){
_start:
{
uint8_t v_b_boxed_6430_; uint8_t v_res_6431_; lean_object* v_r_6432_; 
v_b_boxed_6430_ = lean_unbox(v_b_6428_);
v_res_6431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__0(v_upperBound_6421_, v_next_6422_, v_scopeNames_6423_, v_idComponents_6424_, v_inst_6425_, v_R_6426_, v_a_6427_, v_b_boxed_6430_, v_c_6429_);
lean_dec_ref(v_idComponents_6424_);
lean_dec_ref(v_scopeNames_6423_);
lean_dec(v_next_6422_);
lean_dec(v_upperBound_6421_);
v_r_6432_ = lean_box(v_res_6431_);
return v_r_6432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(lean_object* v_upperBound_6433_, lean_object* v_idComponents_6434_, lean_object* v_scopeNames_6435_, lean_object* v_inst_6436_, lean_object* v_R_6437_, lean_object* v_a_6438_, lean_object* v_b_6439_, lean_object* v_c_6440_){
_start:
{
lean_object* v___x_6441_; 
v___x_6441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___redArg(v_upperBound_6433_, v_idComponents_6434_, v_scopeNames_6435_, v_a_6438_, v_b_6439_);
return v___x_6441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1___boxed(lean_object* v_upperBound_6442_, lean_object* v_idComponents_6443_, lean_object* v_scopeNames_6444_, lean_object* v_inst_6445_, lean_object* v_R_6446_, lean_object* v_a_6447_, lean_object* v_b_6448_, lean_object* v_c_6449_){
_start:
{
lean_object* v_res_6450_; 
v_res_6450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_spec__1(v_upperBound_6442_, v_idComponents_6443_, v_scopeNames_6444_, v_inst_6445_, v_R_6446_, v_a_6447_, v_b_6448_, v_c_6449_);
lean_dec_ref(v_idComponents_6443_);
lean_dec(v_upperBound_6442_);
return v_res_6450_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Completion_endSectionCompletion___lam__0(lean_object* v_x_6451_){
_start:
{
lean_object* v___x_6452_; lean_object* v___x_6453_; uint8_t v___x_6454_; 
v___x_6452_ = lean_string_utf8_byte_size(v_x_6451_);
v___x_6453_ = lean_unsigned_to_nat(0u);
v___x_6454_ = lean_nat_dec_eq(v___x_6452_, v___x_6453_);
if (v___x_6454_ == 0)
{
uint8_t v___x_6455_; 
v___x_6455_ = 1;
return v___x_6455_;
}
else
{
uint8_t v___x_6456_; 
v___x_6456_ = 0;
return v___x_6456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___lam__0___boxed(lean_object* v_x_6457_){
_start:
{
uint8_t v_res_6458_; lean_object* v_r_6459_; 
v_res_6458_ = l_Lean_Server_Completion_endSectionCompletion___lam__0(v_x_6457_);
lean_dec_ref(v_x_6457_);
v_r_6459_ = lean_box(v_res_6458_);
return v_r_6459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(size_t v_sz_6460_, size_t v_i_6461_, lean_object* v_bs_6462_){
_start:
{
uint8_t v___x_6463_; 
v___x_6463_ = lean_usize_dec_lt(v_i_6461_, v_sz_6460_);
if (v___x_6463_ == 0)
{
return v_bs_6462_;
}
else
{
lean_object* v_v_6464_; lean_object* v___x_6465_; lean_object* v_bs_x27_6466_; lean_object* v___x_6467_; size_t v___x_6468_; size_t v___x_6469_; lean_object* v___x_6470_; 
v_v_6464_ = lean_array_uget(v_bs_6462_, v_i_6461_);
v___x_6465_ = lean_unsigned_to_nat(0u);
v_bs_x27_6466_ = lean_array_uset(v_bs_6462_, v_i_6461_, v___x_6465_);
v___x_6467_ = l_Lean_Name_toString(v_v_6464_, v___x_6463_);
v___x_6468_ = ((size_t)1ULL);
v___x_6469_ = lean_usize_add(v_i_6461_, v___x_6468_);
v___x_6470_ = lean_array_uset(v_bs_x27_6466_, v_i_6461_, v___x_6467_);
v_i_6461_ = v___x_6469_;
v_bs_6462_ = v___x_6470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1___boxed(lean_object* v_sz_6472_, lean_object* v_i_6473_, lean_object* v_bs_6474_){
_start:
{
size_t v_sz_boxed_6475_; size_t v_i_boxed_6476_; lean_object* v_res_6477_; 
v_sz_boxed_6475_ = lean_unbox_usize(v_sz_6472_);
lean_dec(v_sz_6472_);
v_i_boxed_6476_ = lean_unbox_usize(v_i_6473_);
lean_dec(v_i_6473_);
v_res_6477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_boxed_6475_, v_i_boxed_6476_, v_bs_6474_);
return v_res_6477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(lean_object* v_completionInfoPos_6478_, lean_object* v_uri_6479_, lean_object* v_pos_6480_, size_t v_sz_6481_, size_t v_i_6482_, lean_object* v_bs_6483_){
_start:
{
uint8_t v___x_6484_; 
v___x_6484_ = lean_usize_dec_lt(v_i_6482_, v_sz_6481_);
if (v___x_6484_ == 0)
{
lean_dec_ref(v_pos_6480_);
lean_dec_ref(v_uri_6479_);
lean_dec(v_completionInfoPos_6478_);
return v_bs_6483_;
}
else
{
lean_object* v_v_6485_; lean_object* v___x_6486_; lean_object* v_bs_x27_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; size_t v___x_6494_; size_t v___x_6495_; lean_object* v___x_6496_; 
v_v_6485_ = lean_array_uget(v_bs_6483_, v_i_6482_);
v___x_6486_ = lean_unsigned_to_nat(0u);
v_bs_x27_6487_ = lean_array_uset(v_bs_6483_, v_i_6482_, v___x_6486_);
v___x_6488_ = lean_box(0);
v___x_6489_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___redArg___closed__2));
lean_inc(v_completionInfoPos_6478_);
v___x_6490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6490_, 0, v_completionInfoPos_6478_);
lean_inc_ref(v_pos_6480_);
lean_inc_ref(v_uri_6479_);
v___x_6491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6491_, 0, v_uri_6479_);
lean_ctor_set(v___x_6491_, 1, v_pos_6480_);
lean_ctor_set(v___x_6491_, 2, v___x_6490_);
lean_ctor_set(v___x_6491_, 3, v___x_6488_);
v___x_6492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6492_, 0, v___x_6491_);
v___x_6493_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6493_, 0, v_v_6485_);
lean_ctor_set(v___x_6493_, 1, v___x_6488_);
lean_ctor_set(v___x_6493_, 2, v___x_6488_);
lean_ctor_set(v___x_6493_, 3, v___x_6489_);
lean_ctor_set(v___x_6493_, 4, v___x_6488_);
lean_ctor_set(v___x_6493_, 5, v___x_6488_);
lean_ctor_set(v___x_6493_, 6, v___x_6492_);
lean_ctor_set(v___x_6493_, 7, v___x_6488_);
v___x_6494_ = ((size_t)1ULL);
v___x_6495_ = lean_usize_add(v_i_6482_, v___x_6494_);
v___x_6496_ = lean_array_uset(v_bs_x27_6487_, v_i_6482_, v___x_6493_);
v_i_6482_ = v___x_6495_;
v_bs_6483_ = v___x_6496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0___boxed(lean_object* v_completionInfoPos_6498_, lean_object* v_uri_6499_, lean_object* v_pos_6500_, lean_object* v_sz_6501_, lean_object* v_i_6502_, lean_object* v_bs_6503_){
_start:
{
size_t v_sz_boxed_6504_; size_t v_i_boxed_6505_; lean_object* v_res_6506_; 
v_sz_boxed_6504_ = lean_unbox_usize(v_sz_6501_);
lean_dec(v_sz_6501_);
v_i_boxed_6505_ = lean_unbox_usize(v_i_6502_);
lean_dec(v_i_6502_);
v_res_6506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6498_, v_uri_6499_, v_pos_6500_, v_sz_boxed_6504_, v_i_boxed_6505_, v_bs_6503_);
return v_res_6506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object* v_uri_6508_, lean_object* v_pos_6509_, lean_object* v_completionInfoPos_6510_, lean_object* v_id_x3f_6511_, uint8_t v_danglingDot_6512_, lean_object* v_scopeNames_6513_){
_start:
{
lean_object* v___f_6515_; lean_object* v_idComponents_6517_; lean_object* v___y_6528_; 
v___f_6515_ = ((lean_object*)(l_Lean_Server_Completion_endSectionCompletion___closed__0));
if (lean_obj_tag(v_id_x3f_6511_) == 0)
{
lean_object* v___x_6531_; 
v___x_6531_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates_mkCandidate___closed__0));
v___y_6528_ = v___x_6531_;
goto v___jp_6527_;
}
else
{
lean_object* v_val_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; size_t v_sz_6535_; size_t v___x_6536_; lean_object* v___x_6537_; 
v_val_6532_ = lean_ctor_get(v_id_x3f_6511_, 0);
lean_inc(v_val_6532_);
lean_dec_ref_known(v_id_x3f_6511_, 1);
v___x_6533_ = l_Lean_Name_components(v_val_6532_);
v___x_6534_ = lean_array_mk(v___x_6533_);
v_sz_6535_ = lean_array_size(v___x_6534_);
v___x_6536_ = ((size_t)0ULL);
v___x_6537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__1(v_sz_6535_, v___x_6536_, v___x_6534_);
v___y_6528_ = v___x_6537_;
goto v___jp_6527_;
}
v___jp_6516_:
{
lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v_scopeNames_6521_; lean_object* v_candidates_6522_; size_t v_sz_6523_; size_t v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; 
v___x_6518_ = lean_array_mk(v_scopeNames_6513_);
v___x_6519_ = lean_array_pop(v___x_6518_);
v___x_6520_ = l_Array_takeWhile___redArg(v___f_6515_, v___x_6519_);
lean_dec_ref(v___x_6519_);
v_scopeNames_6521_ = l_Array_reverse___redArg(v___x_6520_);
v_candidates_6522_ = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_findEndSectionCompletionCandidates(v_idComponents_6517_, v_scopeNames_6521_);
lean_dec_ref(v_idComponents_6517_);
v_sz_6523_ = lean_array_size(v_candidates_6522_);
v___x_6524_ = ((size_t)0ULL);
v___x_6525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_Completion_endSectionCompletion_spec__0(v_completionInfoPos_6510_, v_uri_6508_, v_pos_6509_, v_sz_6523_, v___x_6524_, v_candidates_6522_);
v___x_6526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6526_, 0, v___x_6525_);
return v___x_6526_;
}
v___jp_6527_:
{
if (v_danglingDot_6512_ == 0)
{
v_idComponents_6517_ = v___y_6528_;
goto v___jp_6516_;
}
else
{
lean_object* v___x_6529_; lean_object* v_idComponents_6530_; 
v___x_6529_ = ((lean_object*)(l_Lean_Server_Completion_fieldIdCompletion___closed__0));
v_idComponents_6530_ = lean_array_push(v___y_6528_, v___x_6529_);
v_idComponents_6517_ = v_idComponents_6530_;
goto v___jp_6516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_endSectionCompletion___boxed(lean_object* v_uri_6538_, lean_object* v_pos_6539_, lean_object* v_completionInfoPos_6540_, lean_object* v_id_x3f_6541_, lean_object* v_danglingDot_6542_, lean_object* v_scopeNames_6543_, lean_object* v_a_6544_){
_start:
{
uint8_t v_danglingDot_boxed_6545_; lean_object* v_res_6546_; 
v_danglingDot_boxed_6545_ = lean_unbox(v_danglingDot_6542_);
v_res_6546_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_6538_, v_pos_6539_, v_completionInfoPos_6540_, v_id_x3f_6541_, v_danglingDot_boxed_6545_, v_scopeNames_6543_);
return v_res_6546_;
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
